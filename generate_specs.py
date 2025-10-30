"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

import subprocess
import sys
from pathlib import Path

from analysis import CodeGraph
from models import LLMGen, get_llm_generation_with_model
from util import LLVMAnalysis, extract_specifications

MODEL = "gpt-4o"
HEADERS_TO_INCLUDE_IN_OUTPUT = ["stdlib.h", "limits.h"]


def generate_spec(
    model: LLMGen,
    conversation: list[dict[str, str]],
    func_name: str,
    llvm_analysis: LLVMAnalysis,
    out_file: Path,
) -> None:
    """Use the LLM to generate specifications for a given function and update the source file.

    The LLM is given the following information:
    - The body of the function `func_name`, including all comments
    - Extensive documentation of the CBMC API
    - A history of the conversation so far, including Any errors from verification attempts

    Take the LLM's response, extract the function with specifications,
    replace the original function in `out_file` with this new function,
    and update the line/column information for all functions in `llvm_analysis`.
    """
    func_analysis = llvm_analysis.get_analysis_for_function(func_name)
    if func_analysis is None:
        sys.exit(1)

    # Check if the function to generate specifications for has any callees.
    callees = llvm_analysis.get_callees(func_analysis)
    callees_with_specs = [callee for callee in callees if callee.is_specified()]
    # If the function has callees, and they have specifications, include them in the conversation.
    if callees_with_specs:
        callee_context = "\n".join(str(callee) for callee in callees_with_specs)
        conversation.append({"role": "user", "content": callee_context})

    try:
        response = model.gen(conversation, top_k=1, temperature=0.0)[0]
        conversation += [{"role": "assistant", "content": response}]
    except Exception as e:
        print(f"Error generating specs: {e}")
        sys.exit(1)

    # Get the part within <FUNC> and </FUNC> tags
    function_w_specs = response.split("<FUNC>")[1].split("</FUNC>")[0].strip()
    if function_w_specs[:4] == "```c":
        function_w_specs = function_w_specs[4:]
    if function_w_specs[-3:] == "```":
        function_w_specs = function_w_specs[:-3]
    function_w_specs = function_w_specs.strip()

    start_line = func_analysis.start_line
    start_col = func_analysis.start_col
    end_line = func_analysis.end_line
    end_col = func_analysis.end_col

    with Path(out_file).open(encoding="utf-8") as f:
        lines = f.readlines()

    before = [*lines[: start_line - 1], *[lines[start_line - 1][: start_col - 1]]]
    after = [*lines[end_line - 1][end_col:], *lines[end_line:]]
    new_contents = "".join([*before, function_w_specs, *after])

    # Update the line/col info for this function
    function_len = len(function_w_specs.splitlines())
    new_end_line = start_line + function_len - 1
    new_end_col = (
        len(function_w_specs.splitlines()[-1])
        if function_len > 1
        else start_col + len(function_w_specs)
    )
    func_analysis.end_line = new_end_line
    func_analysis.end_col = new_end_col
    func_analysis.set_specifications(extract_specifications(function_w_specs.splitlines()))

    # Update line/col info for other functions
    line_offset = function_len - (end_line - start_line + 1)
    for other_func in llvm_analysis.functions.values():
        if other_func.name == func_name:
            continue
        if other_func.start_line > end_line:
            other_func.start_line += line_offset
            other_func.end_line += line_offset
        elif other_func.start_line == end_line and other_func.start_col >= end_col:
            other_func.start_col += new_end_col - end_col
            other_func.end_col += new_end_col - end_col
        elif other_func.end_line > end_line:
            other_func.end_line += line_offset
        elif other_func.end_line == end_line and other_func.end_col >= end_col:
            other_func.end_col += new_end_col - end_col

    with Path(out_file).open(mode="w", encoding="utf-8") as f:
        f.write(new_contents)


def recover_from_failure() -> None:
    """Implement recovery logic."""
    raise NotImplementedError("TODO: Implement me")


def verify_one_function(func_name: str, llvm_analysis: LLVMAnalysis, out_file: Path) -> bool | None:
    """Return the result of running CBMC on the specifications generated for a single function.

    Args:
        func_name (str): The name of the function to verify.
        llvm_analysis (LLVMAnalysis): The top-level LLVM analysis.
        out_file (Path): The path to the updated file where the function is defined (with specs).

    Returns:
        bool | None: True iff verification succeeds, False if it fails. None if the function is
            not able to found in the top-level LLVM analysis.
    """
    # Load the prompt from the template file
    prompt_file = Path("prompt.txt")
    with Path(prompt_file).open(encoding="utf-8") as f:
        prompt_template = f.read()

    func_analysis = llvm_analysis.get_analysis_for_function(func_name)
    # This should not happen
    if func_analysis is None:
        print(f"Function {func_name} not found in LLVM analysis, skipping.")
        return None

    # Get the source code of the function
    inp = func_analysis.get_source_code()
    # Fill in the prompt_template template
    prompt = prompt_template.replace("<<SOURCE>>", inp)

    # Call the LLM to generate specs
    model = get_llm_generation_with_model(MODEL)
    conversation = [
        {"role": "system", "content": "You are an intelligent coding assistant"},
        {"role": "user", "content": prompt},
    ]

    generate_spec(model, conversation, func_name, llvm_analysis, out_file)

    success = False
    for _ in range(10):
        # Replace calls to already processed functions with their contracts
        replace_cmd = "".join([f"--replace-call-with-contract {f} " for f in processed_funcs])

        command = (
            f"goto-cc -o {func_name}.goto {out_file.absolute()} --function {func_name} && "
            f"goto-instrument --partial-loops --unwind 5 {func_name}.goto {func_name}.goto && "
            f"goto-instrument {replace_cmd}"
            f"--enforce-contract {func_name} "
            f"{func_name}.goto checking-{func_name}-contracts.goto && "
            f"cbmc checking-{func_name}-contracts.goto --function {func_name} --depth 100"
        )

        print(f"Running command: {command}")

        try:
            result = subprocess.run(command, shell=True, capture_output=True, text=True)
            if result.returncode == 0:
                print(f"Verification for function {func_name} succeeded.")
                success = True
                processed_funcs.append(func_name)
                break
            filt_out = "\n".join([line for line in result.stdout.splitlines() if "FAILURE" in line])
            repair_msg = (
                f"Error while running verification for function {func_name}:\n"
                f"STDOUT: {filt_out}\n"
                f"STDERR: {result.stderr}\n"
                "Please fix the error and re-generate the function with specifications."
            )
            print(repair_msg)
            conversation += [{"role": "user", "content": repair_msg}]

            generate_spec(model, conversation, func_name, llvm_analysis, out_file)

        except Exception as e:
            print(f"Error running command for function {func_name}: {e}")
            break

    if not success:
        recover_from_failure()

    return success


def _prepare_output_location(input_file_path: Path) -> Path:
    """Return the path to the output location of the C program with generated specs.

    Note: The output file is (initially) identical to the input file, with the addition of the
    headers in `HEADERS_TO_INCLUDE_IN_OUTPUT` if they are not already in the file.

    Note: The LLVM analysis should ideally expose the imports in a file, mitigating the need for the
    brittle string matching that is currently done.

    Args:
        input_file_path (Path): The path to the initial C program for which to generate specs.

    Returns:
        Path: The path to the output location of the C program with generated specs.
    """
    output_folder = Path("specs")
    output_folder.mkdir(exist_ok=True)
    output_file_path = output_folder / input_file_path.name

    input_program_content = input_file_path.read_text(encoding="utf-8")
    input_program_lines = [line.strip() for line in input_program_content.splitlines()]
    initial_output_program = input_program_content
    for header in HEADERS_TO_INCLUDE_IN_OUTPUT:
        header_line = f"#include <{header}>"
        if header_line not in input_program_lines:
            initial_output_program = f"{header_line}\n" + initial_output_program

    output_file_path.write_text(initial_output_program, encoding="utf-8")
    return output_file_path


if __name__ == "__main__":
    input_file_path = Path(sys.argv[1])
    output_file_path = _prepare_output_location(input_file_path)

    # Get a list of functions in reverse topological order
    code_graph = CodeGraph(output_file_path)
    recursive_funcs = code_graph.get_names_of_recursive_functions()
    code_graph_no_recursive_loops = code_graph.remove_recursive_loops()
    func_ordering = code_graph_no_recursive_loops.get_function_names_in_topological_order(
        reverse_order=True
    )

    processed_funcs = []
    for func_name in func_ordering:
        # Skip recursive functions for now
        if func_name in recursive_funcs:
            print(f"Skipping recursive function {func_name}")
            processed_funcs.append(func_name)
            continue

        print(f"Processing function {func_name}...")

        is_verification_successful = verify_one_function(
            func_name, code_graph.llvm_analysis, output_file_path
        )

        if is_verification_successful is None:
            print(f"Skipping function {func_name} due to missing analysis.")
            processed_funcs.append(func_name)
            continue

        if not is_verification_successful:
            print(f"Verification for function {func_name} failed after multiple attempts.")
            processed_funcs.append(func_name)
            continue
