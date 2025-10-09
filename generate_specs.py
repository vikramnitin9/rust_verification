'''
Script to generate specifications for C functions using an LLM and verify them with CBMC.
'''
MODEL = 'gpt-4o'

import sys
from pathlib import Path
import subprocess
from models import get_model_from_name
import os
import json
import networkx as nx

def get_llvm_analysis_result(file_path):
    '''
    Given a C file, run the 'parsec' tool to get LLVM analysis in JSON format
    '''
    # Check if PARSEC_BUILD_DIR is set
    parsec_build_dir = os.environ.get('PARSEC_BUILD_DIR')
    if parsec_build_dir is None:
        raise Exception("Error: $PARSEC_BUILD_DIR not set.")
    try:
        cmd = f'{parsec_build_dir}/parsec --rename-main=false --add-instr=false {file_path}'
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        if result.returncode != 0:
            raise Exception(f"Error running parsec: {result.stderr}")
    except:
        raise Exception("Error running parsec.")
    
    analysis_file = Path("analysis.json")
    if not analysis_file.exists():
        raise Exception("Error: analysis.json not found after running parsec.")
    with open(analysis_file, 'r') as f:
        analysis = json.load(f)
    return analysis

def get_call_graph(llvm_analysis):
    '''
    From the JSON analysis, build a call graph using networkx
    '''
    call_graph = nx.DiGraph()
    for func in llvm_analysis['functions']:
        func_name = func['name']
        call_graph.add_node(func_name)
        for callee in func.get('functions', []):
            call_graph.add_edge(func_name, callee['name'])
    return call_graph

# Extract function source code from file given its analysis info    
def extract_func(filename, func_analysis):
    start_line = func_analysis['startLine']
    start_col = func_analysis['startCol']
    end_col = func_analysis['endCol']
    end_line = func_analysis['endLine']

    with open(filename, 'r') as f:
        lines = f.readlines()

    func_lines = lines[start_line-1:end_line+1]
    func_lines[0] = func_lines[0][start_col-1:]
    func_lines[-1] = func_lines[-1][:end_col-1]

    return ''.join(func_lines)

def generate_spec(model, conversation, func_name, llvm_analysis, out_file):
    '''
    Use the LLM to generate specifications for a given function and update the source file.

    The LLM is given the following information:
    - The body of the function `func_name`, including all comments
    - Extensive documentation of the CBMC API
    - A history of the conversation so far, including any errors from verification attempts
    TODO:
    - Callee context: If the function calls other functions, provide their specifications

    Take the LLM's response, extract the function with specifications,
    replace the original function in `out_file` with this new function,
    and update the line/column information for all functions in `llvm_analysis`.
    '''

    try:
        response = model.gen(conversation, top_k=1, temperature=0.0)[0]
        conversation += [{'role': 'assistant', 'content': response}]
    except Exception as e:
        print(f"Error generating specs: {e}")
        sys.exit(1)

    func_analysis = next((f for f in llvm_analysis['functions'] if f['name'] == func_name), None)
    if func_analysis is None:
        print(f"Function {func_name} not found in LLVM analysis.")
        sys.exit(1)

    # Get the part within <FUNC> and </FUNC> tags
    function_w_specs = response.split("<FUNC>")[1].split("</FUNC>")[0].strip()
    if function_w_specs[:4] == '```c':
        function_w_specs = function_w_specs[4:]
    if function_w_specs[-3:] == '```':
        function_w_specs = function_w_specs[:-3]
    function_w_specs = function_w_specs.strip()

    start_line = func_analysis['startLine']
    start_col = func_analysis['startCol']
    end_line = func_analysis['endLine']
    end_col = func_analysis['endCol']

    with open(out_file, 'r') as f:
        lines = f.readlines()

    before = lines[:start_line-1] + [lines[start_line-1][:start_col-1]]
    after = [lines[end_line-1][end_col:]] + lines[end_line:]
    new_contents = ''.join(before + [function_w_specs] + after)

    # Update the line/col info for this function
    func_lines = len(function_w_specs.splitlines())
    new_end_line = start_line + func_lines - 1
    new_end_col = len(function_w_specs.splitlines()[-1]) if func_lines > 1 else start_col + len(function_w_specs)
    func_analysis['endLine'] = new_end_line
    func_analysis['endCol'] = new_end_col

    # Update line/col info for other functions
    line_offset = func_lines - (end_line - start_line + 1)
    for f in llvm_analysis['functions']:
        if f['name'] == func_name:
            continue
        if f['startLine'] > end_line:
            f['startLine'] += line_offset
            f['endLine'] += line_offset
        elif f['startLine'] == end_line and f['startCol'] >= end_col:
            f['startCol'] += (new_end_col - end_col)
            f['endCol'] += (new_end_col - end_col)
        elif f['endLine'] > end_line:
            f['endLine'] += line_offset
        elif f['endLine'] == end_line and f['endCol'] >= end_col:
            f['endCol'] += (new_end_col - end_col)
    
    with open(out_file, 'w') as f:
        f.write(new_contents)

def recover_from_failure():
    '''
    Placeholder for recovery logic
    TODO
    '''
    raise NotImplementedError

def verify_one_function(func_name, llvm_analysis, out_file):

    # Load the prompt from the template file
    prompt_file = Path('prompt.txt')
    with open(prompt_file, 'r') as f:
        prompt_template = f.read()

    func_analysis = next((f for f in llvm_analysis['functions'] if f['name'] == func_name), None)
    # This should not happen
    if func_analysis is None:
        print(f"Function {func_name} not found in LLVM analysis, skipping.")
        return None
    
    # Get the source code of the function
    inp = extract_func(out_file, func_analysis)

    # Fill in the prompt_template template
    prompt = prompt_template.replace("<<SOURCE>>", inp)

    # Call the LLM to generate specs
    model = get_model_from_name(MODEL)
    conversation = [{'role': 'system', 'content': 'You are an intelligent coding assistant'},
                    {'role': 'user', 'content': prompt}]
    
    generate_spec(model, conversation, func_name, llvm_analysis, out_file)

    success = False
    for _ in range(10):
        
        # Replace calls to already processed functions with their contracts
        replace_cmd = ''.join([f"--replace-call-with-contract {f} " for f in processed_funcs])

        command = (f"goto-cc -o {func_name}.goto {out_file.absolute()} --function {func_name} && "
        f"goto-instrument --partial-loops --unwind 5 {func_name}.goto {func_name}.goto && "
        f"goto-instrument {replace_cmd}"
        f"--enforce-contract {func_name} {func_name}.goto checking-{func_name}-contracts.goto && "
        f"cbmc checking-{func_name}-contracts.goto --function {func_name} --depth 100")

        print(f"Running command: {command}")
        
        try:
            result = subprocess.run(command, shell=True, capture_output=True, text=True)
            if result.returncode == 0:
                print(f"Verification for function {func_name} succeeded.")
                success = True
                processed_funcs.append(func_name)
                break
            else:
                filt_out = '\n'.join([line for line in result.stdout.splitlines() if "FAILURE" in line])
                repair_msg = (f"Error while running verification for function {func_name}:\n"
                                f"STDOUT: {filt_out}\n"
                                f"STDERR: {result.stderr}\n"
                                "Please fix the error and re-generate the function with specifications.")
                print(repair_msg)
                conversation += [{'role': 'user', 'content': repair_msg}]

                generate_spec(model, conversation, func_name, llvm_analysis, out_file)

        except Exception as e:
            print(f"Error running command for function {func_name}: {e}")
            break

    if not success:
        recover_from_failure()

    return success


if __name__ == "__main__":

    inp_file = Path(sys.argv[1])
    
    spec_folder = Path('specs')
    spec_folder.mkdir(exist_ok=True)
    out_file = spec_folder / inp_file.name

    # Copy input file to output file initially
    # We iteratively update the output file with specs
    # TODO: Include <stdlib.h> and <limits.h> in out_file if not present
    with open(inp_file, 'r') as f:
        inp = f.read()
    with open(out_file, 'w') as f:
        f.write(inp)

    # Get LLVM analysis and call graph
    llvm_analysis = get_llvm_analysis_result(out_file)
    call_graph = get_call_graph(llvm_analysis)

    # Get a list of functions in reverse topological order
    func_names = [n for n in call_graph.nodes if n != '']
    recursive_funcs = [n for n in func_names if call_graph.has_edge(n, n)]
    cg_without_self_loops = call_graph.copy()
    cg_without_self_loops.remove_edges_from(nx.selfloop_edges(cg_without_self_loops))
    try:
        func_ordering = list(reversed(list(nx.topological_sort(cg_without_self_loops))))
    except nx.NetworkXUnfeasible:
        print("Warning: Call graph has cycles, using DFS postorder for function ordering.")
        func_ordering = list(nx.dfs_postorder_nodes(cg_without_self_loops, source=func_names[0]))

    processed_funcs = []

    for func_name in func_ordering:
        # Skip recursive functions for now
        if func_name in recursive_funcs:
            print(f"Skipping recursive function {func_name}")
            processed_funcs.append(func_name)
            continue

        print(f"Processing function {func_name}...")

        success = verify_one_function(func_name, llvm_analysis, out_file)
        
        if success is None:
            print(f"Skipping function {func_name} due to missing analysis.")
            processed_funcs.append(func_name)
            continue
        
        if not success:
            print(f"Verification for function {func_name} failed after multiple attempts.")
            processed_funcs.append(func_name)
            continue