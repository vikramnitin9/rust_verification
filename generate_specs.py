"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

from analysis import CodeGraph
from models import LLMGen, get_llm_generation_with_model
from util import LlvmAnalysis, extract_specification

MODEL = "gpt-4o"


def write_new_spec_to_file(
    model: LLMGen,
    conversation: list[dict[str, str]],
    func_name: str,
    llvm_analysis: LlvmAnalysis,
    out_file: Path,
) -> None:
    """Use the given LLM to generate specifications for a given function and update the source file.

    The LLM prompt contains:
    - The body of the function `func_name`, including all comments.
    - Documentation of the CBMC API.
    - A history of the conversation so far, including any errors from verification attempts.

    Take the LLM's response, extract the function with specifications,
    replace the original function in `out_file` with this new function,
    and update the line/column information for all functions in `llvm_analysis`.
    """
    func_analysis = llvm_analysis.get_analysis_for_function(func_name)
    if func_analysis is None:
        sys.exit(1)

    # If the function has any callees, get their specifications.
    callees = llvm_analysis.get_callees(func_analysis)
    callees_with_specs = [callee for callee in callees if callee.is_specified()]
    if callees_with_specs:
        callee_context = "\n".join(str(callee) for callee in callees_with_specs)
        conversation.append({"role": "user", "content": callee_context})

    try:
        response = model.gen(conversation, top_k=1, temperature=0.0)[0]
        conversation += [{"role": "assistant", "content": response}]
    except Exception as e:
        print(f"Error generating specs: {e}")
        sys.exit(1)

    # Get the part within <FUNC> and </FUNC> tags.
    functions = re.findall(r"<FUNC>(.*?)</FUNC>", response, re.DOTALL)
    if len(functions) != 1:
        msg = f"Wrong number of functions {len(functions)}: {functions}"
        raise RuntimeError(msg)
    function_w_spec = functions[0]
    fences = re.findall(r"```", function_w_spec)
    if len(fences) == 0:
        # Nothing to do
        pass
    elif len(fences) == 2:
        match = re.search(r"```c?(.*)```", function_w_spec, re.DOTALL)
        if match is None:
            raise RuntimeError("Existing fences not found: " + function_w_spec)
        function_w_spec = match.group(1)
    else:
        msg = f"Wrong number of code fences {len(fences)}: {function_w_spec}"
        raise RuntimeError(msg)
    function_w_spec = function_w_spec.strip()

    start_line = func_analysis.start_line
    start_col = func_analysis.start_col
    end_line = func_analysis.end_line
    end_col = func_analysis.end_col

    with Path(out_file).open(encoding="utf-8") as f:
        lines = f.readlines()

    before = [*lines[: start_line - 1], *[lines[start_line - 1][: start_col - 1]]]
    after = [*lines[end_line - 1][end_col:], *lines[end_line:]]
    new_contents = "".join([*before, function_w_spec, *after])

    # Update the line/col info for this function.
    function_len = len(function_w_spec.splitlines())
    new_end_line = start_line + function_len - 1
    new_end_col = (
        len(function_w_spec.splitlines()[-1])
        if function_len > 1
        else start_col + len(function_w_spec)
    )
    func_analysis.end_line = new_end_line
    func_analysis.end_col = new_end_col
    func_analysis.set_specifications(extract_specification(function_w_spec.splitlines()))

    # Update line/col info for other functions.
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

    Path(out_file).write_text(new_contents)


def recover_from_failure() -> None:
    """Implement recovery logic."""
    raise NotImplementedError("TODO: Implement me")


def verify_one_function(func_name: str, llvm_analysis: LlvmAnalysis, out_file: Path) -> bool | None:
    """Return the result of running CBMC on the specifications generated for a single function.

    Args:
        func_name (str): The name of the function to verify.
        llvm_analysis (LlvmAnalysis): The top-level LLVM analysis.
        out_file (Path): The path to the updated file where the function is defined (with a spec).

    Returns:
        bool | None: True iff verification succeeds, False if it fails. None if the function is
            not in the top-level LLVM analysis.
    """
    # Load the prompt from the template file.
    prompt_template = Path("prompt.txt").read_text()

    func_analysis = llvm_analysis.get_analysis_for_function(func_name)
    # This should not happen.
    if func_analysis is None:
        msg = f"Function {func_name} not found in LLVM analysis"
        raise RuntimeError(msg)

    # Get the source code of the function.
    source_code = func_analysis.get_source_code()
    # Fill in the prompt_template template
    prompt = prompt_template.replace("<<SOURCE>>", source_code)

    # Call the LLM to generate a spec.
    model = get_llm_generation_with_model(MODEL)
    conversation = [
        {"role": "system", "content": "You are an intelligent coding assistant"},
        {"role": "user", "content": prompt},
    ]

    write_new_spec_to_file(model, conversation, func_name, llvm_analysis, out_file)

    success = False
    for _ in range(10):
        # Replace calls to already-processed functions with their contracts
        replace_args = "".join([f"--replace-call-with-contract {f} " for f in processed_funcs])

        command = (
            f"goto-cc -o {func_name}.goto {out_file.absolute()} --function {func_name} && "
            f"goto-instrument --partial-loops --unwind 5 {func_name}.goto {func_name}.goto && "
            f"goto-instrument {replace_args}"
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
            failure_lines = "\n".join(
                [line for line in result.stdout.splitlines() if "FAILURE" in line]
            )
            repair_msg = (
                f"Error while running verification for function {func_name}:\n"
                f"STDOUT: {failure_lines}\n"
                f"STDERR: {result.stderr}\n"
                "Please fix the error and re-generate the function with specifications."
            )
            print(repair_msg)
            conversation += [{"role": "user", "content": repair_msg}]

            write_new_spec_to_file(model, conversation, func_name, llvm_analysis, out_file)

        except Exception as e:
            print(f"Error running command for function {func_name}: {e}")
            break

    if not success:
        recover_from_failure()

    return success


if __name__ == "__main__":
    inp_file = Path(sys.argv[1])

    spec_folder = Path("specs")
    spec_folder.mkdir(exist_ok=True)
    out_file = spec_folder / inp_file.name

    # Copy input file to output file initially.
    # We iteratively update the output file with specs.
    # TODO: Include <stdlib.h> and <limits.h> in out_file if not present.
    inp = Path(inp_file).read_text()
    Path(out_file).write_text(inp)

    # Get a list of functions in reverse topological order.
    code_graph = CodeGraph(out_file)
    recursive_funcs = code_graph.get_names_of_recursive_functions()
    # TODO: Process recursive loops rather than removing them.
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
            func_name, code_graph.llvm_analysis, out_file
        )

        if is_verification_successful is None:
            print(f"Skipping function {func_name} due to missing analysis.")
            processed_funcs.append(func_name)
            continue

        if not is_verification_successful:
            print(f"Verification for function {func_name} failed after multiple attempts.")
            processed_funcs.append(func_name)
            continue
