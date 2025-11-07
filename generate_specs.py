"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

from models import LLMGen, get_llm_generation_with_model
from util import ParsecFunction, ParsecResult, PromptBuilder, extract_specification
from verification import Failure, LlmGenerateVerifyIteration, Success

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_SPECIFY_AND_VERIFY_RETRIES = 10
DEFAULT_SYSTEM_PROMPT = Path("system-prompt.txt").read_text(encoding="utf-8")


def main() -> None:
    """Generate specifications for C functions using an LLM and verify them with CBMC."""
    parser = argparse.ArgumentParser(
        prog="generate_specs.py", description="Generate CBMC specifications for a C file."
    )
    parser.add_argument(
        "--file", required=True, help="Path to the C file for which to generate specifications."
    )
    parser.add_argument(
        "--save-conversation",
        action="store_true",
        help="Save the conversation used to generate specifications.",
    )
    args = parser.parse_args()

    input_file_path = Path(args.file)
    output_file_path = _copy_input_file_to_output_file(input_file_path)
    _insert_default_headers(output_file_path)

    parsec_result = ParsecResult(output_file_path)
    recursive_funcs = parsec_result.get_names_of_recursive_functions()
    parsec_result_without_direct_recursive_functions = parsec_result.copy(
        remove_self_edges_in_call_graph=True
    )

    # Get a list of functions in reverse topological order.
    func_ordering = (
        parsec_result_without_direct_recursive_functions.get_function_names_in_topological_order(
            reverse_order=True
        )
    )
    verified_functions: list[str] = []
    prompt_builder = PromptBuilder()
    generation_strategy = get_llm_generation_with_model(MODEL)
    conversation_log: dict[str, list[LlmGenerateVerifyIteration]] = defaultdict(list)
    for func_name in func_ordering:
        conversation = [{"role": "system", "content": DEFAULT_SYSTEM_PROMPT}]
        if func_name in recursive_funcs:
            print(f"Skipping self-recursive function {func_name} because of CBMC bugs/limitations.")
            continue

        print(f"Processing function {func_name}...")
        function_to_verify = parsec_result_without_direct_recursive_functions.get_function(
            func_name
        )
        if not function_to_verify:
            msg = f"Failed to find function '{func_name}' to verify"
            raise RuntimeError(msg)

        # Get the initial prompt for specification generation.
        spec_generation_prompt = prompt_builder.initial_specification_generation_prompt(
            function_to_verify, parsec_result_without_direct_recursive_functions
        )
        updated_file = _generate_specifications(
            generation_strategy,
            conversation,
            spec_generation_prompt,
            function_to_verify,
            parsec_result_without_direct_recursive_functions,
            output_file_path,
        )
        # Attempt to verify the generated specifications for the function.
        verification_result = verify_one_function(func_name, verified_functions, output_file_path)
        if args.save_conversation:
            conversation_log[func_name].append(
                LlmGenerateVerifyIteration(
                    func_name, spec_generation_prompt, updated_file, verification_result
                )
            )

        if isinstance(verification_result, Success):
            print(f"Verification succeeded for '{func_name}'")
            verified_functions.append(func_name)
            continue
        print(f"Verification failed for '{func_name}'; regenerating specs and re-trying")

        for n in range(DEFAULT_NUM_SPECIFY_AND_VERIFY_RETRIES):
            # Try to re-generate specifications for verification.
            spec_generation_prompt = prompt_builder.repair_specification_prompt(
                function_to_verify, verification_result
            )
            updated_file = _generate_specifications(
                generation_strategy,
                conversation,
                spec_generation_prompt,
                function_to_verify,
                parsec_result_without_direct_recursive_functions,
                output_file_path,
            )
            verification_result = verify_one_function(
                func_name, verified_functions, output_file_path
            )
            if isinstance(verification_result, Success):
                print(
                    f"Verification succeeded for '{func_name}' after "
                    f"{n + 1}/{DEFAULT_NUM_SPECIFY_AND_VERIFY_RETRIES} retries(s)"
                )
                verified_functions.append(func_name)
                if args.save_conversation:
                    conversation_log[func_name].append(
                        LlmGenerateVerifyIteration(
                            func_name, spec_generation_prompt, updated_file, verification_result
                        )
                    )
                break  # Move on to the next function to generate specs and verify.
            print(f"Verification failed for '{func_name}'; on retry attempt {n + 1}")
            if args.save_conversation:
                conversation_log[func_name].append(
                    LlmGenerateVerifyIteration(
                        func_name, spec_generation_prompt, updated_file, verification_result
                    )
                )
            continue

        if func_name not in verified_functions:
            print(
                f"{func_name} failed to verify after "
                f"{DEFAULT_NUM_SPECIFY_AND_VERIFY_RETRIES} retries(s)"
            )
            recover_from_failure()
    if args.save_conversation:
        _write_conversation_log(conversation_log)


def _generate_specifications(
    generation_strategy: LLMGen,
    conversation: list[dict[str, str]],
    prompt: str,
    function: ParsecFunction,
    parsec_result: ParsecResult,
    out_file: Path,
) -> str:
    """Use the given LLM to generate specifications for a given function and update the source file.

    The LLM prompt contains:
    - The body of the function `func_name`, including all comments.
    - Documentation of the CBMC API.
    - A history of the conversation so far, including any errors from verification attempts.

    Take the LLM's response, extract the function with specifications,
    replace the original function in `out_file` with this new function,
    and update the line/column information for all functions in `parsec_result`.

    Returns:
        str: The contents of the file with the newly-generated specifications.
    """
    try:
        conversation.append({"role": "user", "content": prompt})
        response = generation_strategy.gen(conversation, top_k=1, temperature=0.0)[0]
        conversation.append({"role": "assistant", "content": response})
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

    start_line = function.start_line
    start_col = function.start_col
    end_line = function.end_line
    end_col = function.end_col

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
    function.end_line = new_end_line
    function.end_col = new_end_col
    function.set_specifications(extract_specification(function_w_spec.splitlines()))

    # Update line/col info for other functions.
    line_offset = function_len - (end_line - start_line + 1)
    for other_func in parsec_result.functions.values():
        if other_func.name == function.name:
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

    Path(out_file).write_text(new_contents, encoding="utf-8")
    return new_contents


def recover_from_failure() -> None:
    """Implement recovery logic."""


def verify_one_function(
    func_name: str,
    verified_funcs: list[str],
    out_file: Path,
) -> Success | Failure:
    """Return the result of verifying the function named `func_name` with CBMC.

    Args:
        func_name (str): The name of the function to verify with CBMC.
        verified_funcs (list[str]): The list of verified functions.
        out_file (Path): The path to the file in which the function to verify is defined.

    Raises:
        RuntimeError: Raised when an error occurs in executing the verification command.

    Returns:
        Success | Failure: Success if the function successfully verifies, Failure if the
            function does not verify.
    """
    replace_args = "".join([f"--replace-call-with-contract {f} " for f in verified_funcs])
    verification_command = (
        f"goto-cc -o {func_name}.goto {out_file.absolute()} --function {func_name} && "
        f"goto-instrument --partial-loops --unwind 5 {func_name}.goto {func_name}.goto && "
        f"goto-instrument {replace_args}"
        f"--enforce-contract {func_name} "
        f"{func_name}.goto checking-{func_name}-contracts.goto && "
        f"cbmc checking-{func_name}-contracts.goto --function {func_name} --depth 100"
    )

    print(f"Running command: {verification_command}")
    try:
        result = subprocess.run(verification_command, shell=True, capture_output=True, text=True)
        if result.returncode == 0:
            return Success()
        return Failure(stdout=result.stdout, stderr=result.stderr)
    except Exception as e:
        msg = f"Error running command for function {func_name}: {e}"
        raise RuntimeError(msg) from e


def _copy_input_file_to_output_file(input_file_path: Path) -> Path:
    """Copy the initial input file to the output file, where spec generation should occur.

    Args:
        input_file_path (Path): The path to the initial C program for which to generate specs.

    Returns:
        Path: The path to the output location of the C program with generated specs.
    """
    output_folder = Path("specs")
    output_folder.mkdir(exist_ok=True)
    output_file_path = output_folder / input_file_path.name

    input_file_content = input_file_path.read_text(encoding="utf-8")
    output_file_path.write_text(input_file_content, encoding="utf-8")
    return output_file_path


def _insert_default_headers(file_path: Path) -> None:
    """Insert default headers (DEFAULT_HEADERS_IN_OUTPUT) into the file at `file_path`.

    Some of the LLM-generated specifications use functions that are defined in header files
    that are not imported in the source code. This function performs a best-effort attempt
    to include some that are commonly used.

    Args:
        file_path (Path): The path to the file to update with default headers.
    """
    file_content = file_path.read_text(encoding="utf-8")
    program_lines = [line.strip() for line in file_content.splitlines()]
    for header in DEFAULT_HEADERS_IN_OUTPUT:
        header_line = f"#include <{header}>"
        if header_line not in program_lines:
            # TODO: The ParseC result should ideally expose the imports in a file, mitigating the
            # need for the brittle string matching that is currently done.
            file_content = f"{header_line}\n" + file_content
    file_path.open(mode="w", encoding="utf-8").write(file_content)


def _write_conversation_log(conversation_log: dict[str, list[LlmGenerateVerifyIteration]]) -> None:
    """Write the conversation log to disk.

    Args:
        conversation_log (list[GenerateVerifyIteration]): The conversation log.
    """
    path_to_log = _get_path_to_conversation_log()
    path_to_log.write_text(
        json.dumps(
            {
                func_name: [attempt.to_dict() for attempt in attempts]
                for func_name, attempts in conversation_log.items()
            }
        )
    )


def _get_path_to_conversation_log() -> Path:
    """Return the path to where the conversation log should be written.

    Returns:
        Path: The path to where the conversation log should be written.
    """
    current_time = int(time.time())
    path_to_log = Path(f"logs/specifications/{current_time}-specs.json")
    path_to_log.parent.mkdir(parents=True, exist_ok=True)
    path_to_log.touch(exist_ok=True)
    return path_to_log


if __name__ == "__main__":
    main()
