"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

from analysis import CallGraph
from models import LLMGen, get_llm_generation_with_model
from util import ParsecResult, PromptBuilder, extract_specification

MODEL = "gpt-4o"
HEADERS_TO_INCLUDE_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_VERIFICATION_ATTEMPTS = 10


def main() -> None:
    """Entry point to generate_specs.py."""
    input_file_path = Path(sys.argv[1])
    output_file_path = _prepare_output_location(input_file_path)

    call_graph = CallGraph(output_file_path)
    recursive_funcs = call_graph.get_names_of_recursive_functions()

    # TODO: Process recursive loops rather than removing them.
    # Note: No recursive functions are actually removed from the graph; only self-edges.
    call_graph_without_self_edges = call_graph.remove_self_edges()

    # Get a list of functions in reverse topological order.
    func_ordering = call_graph_without_self_edges.get_function_names_in_topological_order(
        reverse_order=True
    )

    processed_funcs = []
    for func_name in func_ordering:
        if func_name in recursive_funcs:
            print(f"Skipping self-recursive function {func_name} because of CBMC bugs/limitations.")
            processed_funcs.append(func_name)
            continue

        print(f"Processing function {func_name}...")

        is_verification_successful = verify_one_function(
            PromptBuilder(), func_name, call_graph.parsec_result, processed_funcs, output_file_path
        )

        if is_verification_successful is None:
            print(f"Skipping function {func_name} due to missing analysis.")
            processed_funcs.append(func_name)
            continue

        if not is_verification_successful:
            print(
                f"Verification for function {func_name} failed after "
                f"{DEFAULT_NUM_VERIFICATION_ATTEMPTS} attempts."
            )
            processed_funcs.append(func_name)
            continue


def write_new_spec_to_file(
    model: LLMGen,
    conversation: list[dict[str, str]],
    func_name: str,
    parsec_result: ParsecResult,
    out_file: Path,
) -> None:
    """Use the given LLM to generate specifications for a given function and update the source file.

    The LLM prompt contains:
    - The body of the function `func_name`, including all comments.
    - Documentation of the CBMC API.
    - A history of the conversation so far, including any errors from verification attempts.

    Take the LLM's response, extract the function with specifications,
    replace the original function in `out_file` with this new function,
    and update the line/column information for all functions in `parsec_result`.
    """
    parsec_function = parsec_result.get_function(func_name)
    if parsec_function is None:
        print(f"ParseC failed to find a function for '{func_name}'")
        sys.exit(1)

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
        match = re.search(r"```[cC]?(.*)```", function_w_spec, re.DOTALL)
        if match is None:
            raise RuntimeError("Existing fences not found: " + function_w_spec)
        function_w_spec = match.group(1)
    else:
        msg = f"Wrong number of code fences {len(fences)}: {function_w_spec}"
        raise RuntimeError(msg)
    function_w_spec = function_w_spec.strip()

    start_line = parsec_function.start_line
    start_col = parsec_function.start_col
    end_line = parsec_function.end_line
    end_col = parsec_function.end_col

    # Use `with` and `readlines()` here to enable line-by-line file reading.
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
    parsec_function.end_line = new_end_line
    parsec_function.end_col = new_end_col
    parsec_function.set_specifications(extract_specification(function_w_spec.splitlines()))

    # Update line/col info for other functions.
    line_offset = function_len - (end_line - start_line + 1)
    for other_func in parsec_result.functions.values():
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


def verify_one_function(
    prompt_builder: PromptBuilder,
    func_name: str,
    parsec_result: ParsecResult,
    processed_funcs: list[str],
    out_file: Path,
) -> bool | None:
    """Return the result of running CBMC on the specifications generated for a single function.

    Args:
        prompt_builder (PromptBuilder): Constructs prompts for the LLM.
        func_name (str): The name of the function to verify.
        parsec_result (ParsecResult): The result of running `parsec` on the initial code.
        processed_funcs (list[str]): The names of previously-processed functions.
        out_file (Path): The path to the updated file where the function is defined (with a spec).

    Returns:
        bool | None: True iff verification succeeds, False if it fails. None if the function is
            not in the result of running `parsec` on the initial code.
    """
    parsec_function = parsec_result.get_function(func_name)
    # This should not happen.
    if parsec_function is None:
        msg = f"Function {func_name} not found in ParseC result"
        raise RuntimeError(msg)

    initial_spec_generation_prompt = prompt_builder.initial_specification_generation_prompt(
        parsec_function, parsec_result
    )

    # Call the LLM to generate a spec.
    model = get_llm_generation_with_model(MODEL)
    # `conversation` will be added to iteratively.
    conversation = [
        {"role": "system", "content": "You are an intelligent coding assistant"},
        {"role": "user", "content": initial_spec_generation_prompt},
    ]

    write_new_spec_to_file(model, conversation, func_name, parsec_result, out_file)

    for n in range(DEFAULT_NUM_VERIFICATION_ATTEMPTS):
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
                print(
                    f"Verification for function {func_name} succeeded (Number of attempts: {n + 1})"
                )
                processed_funcs.append(func_name)
                return True
            repair_msg = prompt_builder.repair_specification_prompt(parsec_function, result)
            print(repair_msg)
            conversation += [{"role": "user", "content": repair_msg}]

            write_new_spec_to_file(model, conversation, func_name, parsec_result, out_file)

        except Exception as e:
            print(f"Error running command for function {func_name}: {e}")
            break

    recover_from_failure()
    return False


def _prepare_output_location(input_file_path: Path) -> Path:
    """Return the path to the output location of the C program with generated specs.

    Note: The output file is (initially) identical to the input file, with the addition of `include`
    directives for the headers in `HEADERS_TO_INCLUDE_IN_OUTPUT` if they are not already in the
    file.

    Note: The ParseC result should ideally expose the imports in a file, mitigating the need for the
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
    main()
