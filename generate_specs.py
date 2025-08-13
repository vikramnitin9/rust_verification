import sys
from pathlib import Path
import subprocess
from models import get_model_from_name
from tree_sitter import Language, Parser
import tree_sitter_c

C_LANGUAGE = Language(tree_sitter_c.language())

def extract_function_names(c_code: str):
    parser = Parser(C_LANGUAGE)
    tree = parser.parse(bytes(c_code, "utf8"))
    root_node = tree.root_node

    function_names = []

    def visit(node):
        if node.type == 'function_declarator':
            identifier = node.child_by_field_name('declarator')
            if identifier and identifier.type == 'identifier':
                function_names.append(c_code[identifier.start_byte:identifier.end_byte])
        for child in node.children:
            visit(child)

    visit(root_node)
    return function_names

def generate_specs(model, conversation, out_file):
    try:
        response = model.gen(conversation, top_k=1, temperature=0.0)[0]
        conversation += [{'role': 'assistant', 'content': response}]
    except Exception as e:
        print(f"Error generating specs: {e}")
        sys.exit(1)

    # Get the part within <PROGRAM> and </PROGRAM> tags
    program_w_specs = response.split("<PROGRAM>")[1].split("</PROGRAM>")[0].strip()
    if program_w_specs[:4] == '```c':
        program_w_specs = program_w_specs[4:]
    if program_w_specs[-3:] == '```':
        program_w_specs = program_w_specs[:-3]

    with open(out_file, 'w') as f:
        f.write(program_w_specs)

if __name__ == "__main__":

    inp_file = Path(sys.argv[1])

    prompt_file = Path('prompt.txt')

    with open(prompt_file, 'r') as f:
        prompt = f.read()
    
    with open(inp_file, 'r') as f:
        inp = f.read()

    spec_folder = Path('specs')
    spec_folder.mkdir(exist_ok=True)
    out_file = spec_folder / inp_file.name

    func_names = extract_function_names(inp)
    
    prompt = prompt.replace("<<SOURCE>>", inp)

    model = get_model_from_name('claude37')

    conversation = [{'role': 'system', 'content': 'You are an intelligent coding assistant'},
                    {'role': 'user', 'content': prompt}]

    generate_specs(model, conversation, out_file)

    successful_funcs = []

    for func_name in func_names:
        success = False
        for _ in range(10):
            replace_cmd = ''.join([f"--replace-call-with-contract {f} " for f in successful_funcs])
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
                    successful_funcs.append(func_name)
                    break
                else:
                    filt_out = '\n'.join([line for line in result.stdout.splitlines() if "FAILURE" in line])
                    repair_msg = (f"Error while running verification for function {func_name}:\n"
                                  f"STDOUT: {filt_out}\n"
                                  f"STDERR: {result.stderr}\n"
                                  "Please fix the error and re-generate the entire program.")
                    print(repair_msg)
                    import pdb; pdb.set_trace()
                    conversation += [{'role': 'user', 'content': repair_msg}]
                    generate_specs(model, conversation, out_file)
                    
            except Exception as e:
                print(f"Error running command for function {func_name}: {e}")
                break
        if not success:
            print(f"Verification for function {func_name} failed after multiple attempts.")
            sys.exit(1)