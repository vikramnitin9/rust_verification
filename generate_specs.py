"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import argparse
import json
import subprocess
import time
from collections import defaultdict
from pathlib import Path

from specifications import LlmSpecificationGenerator
from util import (
    ParsecResult,
    extract_function,
    function_util,
)
from verification import Failure, LlmGenerateVerifyIteration, Success, VerificationResult

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_REGENERATION_ATTEMPTS = 10
DEFAULT_NUM_REPAIR_ATTEMPTS = 5
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
        "--num-regeneration",
        required=False,
        help="The number of times to regenerate a specification after failing to repair it.",
        default=DEFAULT_NUM_REGENERATION_ATTEMPTS,
        type=int,
    )
    parser.add_argument(
        "--num-repair",
        required=False,
        help="The number of times to repair a generated specification.",
        default=DEFAULT_NUM_REPAIR_ATTEMPTS,
        type=int,
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
    conversation_log: dict[str, list[LlmGenerateVerifyIteration]] = defaultdict(list)
    conversation = [{"role": "system", "content": "You are an intelligent coding assistant"}]
    specification_generator = LlmSpecificationGenerator(
        MODEL, parsec_result_without_direct_recursive_functions
    )

    for func_name in func_ordering:
        conversation = [{"role": "system", "content": DEFAULT_SYSTEM_PROMPT}]
        if func_name in recursive_funcs:
            print(f"Skipping self-recursive function {func_name} because of CBMC bugs/limitations.")
            continue

        print(f"Processing function {func_name}...")

        # Generate the initial specifications for verification.
        llm_invocation_result = specification_generator.generate_specifications(
            func_name, conversation
        )
        updated_file = _update_parsec_result_and_output_file(
            llm_invocation_result.response,
            func_name,
            parsec_result_without_direct_recursive_functions,
            output_file_path,
        )
        # Attempt to verify the generated specifications for the function.
        verification_result = verify_one_function(func_name, verified_functions, output_file_path)
        if args.save_conversation:
            conversation_log[func_name].append(
                LlmGenerateVerifyIteration(
                    func_name, llm_invocation_result.prompt, updated_file, verification_result
                )
            )

        if isinstance(verification_result, Success):
            print(f"Verification succeeded for '{func_name}'")
            verified_functions.append(func_name)
            continue
        print(f"Verification failed for '{func_name}'; attempting to repair the generated specs")

        repair_iterations = _run_repair_loop(
            specification_generator,
            func_name,
            verified_functions,
            verification_result,
            conversation,
            parsec_result_without_direct_recursive_functions,
            output_file_path,
            args.num_repair,
        )

        if args.num_repair != 0 and not repair_iterations:
            raise RuntimeError()
        if args.save_conversation:
            conversation_log[func_name].extend(repair_iterations)

        final_repair_iteration = repair_iterations[-1]
        is_repair_successful = isinstance(final_repair_iteration.verification_result, Success)
        repair_result_msg = (
            f"Verification {'succeeded' if is_repair_successful else 'failed'} for "
            f"'{func_name}' after {len(repair_iterations)} repair iterations"
        )
        print(repair_result_msg)

        if func_name not in verified_functions:
            recover_from_failure()
    if args.save_conversation:
        _write_conversation_log(conversation_log)


def _run_repair_loop(
    specification_generator: LlmSpecificationGenerator,
    function_name: str,
    verified_functions: list[str],
    initial_verification_failure: Failure,
    conversation: list[dict[str, str]],
    parsec_result: ParsecResult,
    output_file_path: Path,
    num_repair_attempts: int,
) -> list[LlmGenerateVerifyIteration]:
    verification_result: VerificationResult = initial_verification_failure
    repair_attempts: list[LlmGenerateVerifyIteration] = []
    for n in range(num_repair_attempts):
        print(f"Running repair for '{function_name}' specs: attempt {n + 1}/{num_repair_attempts}'")
        llm_invocation_result = specification_generator.repair_specifications(
            function_name, verification_result, conversation
        )
        verification_result = verify_one_function(
            function_name, verified_functions, output_file_path
        )
        _update_parsec_result_and_output_file(
            llm_invocation_result.response,
            function_name,
            parsec_result,
            output_file_path,
        )
        if isinstance(verification_result, Failure):
            repair_attempts.append(
                LlmGenerateVerifyIteration(
                    function_name,
                    llm_invocation_result.prompt,
                    llm_invocation_result.response,
                    verification_result,
                )
            )
        else:
            repair_attempts.append(
                LlmGenerateVerifyIteration(
                    function_name,
                    llm_invocation_result.prompt,
                    llm_invocation_result.response,
                    verification_result,
                )
            )
            return repair_attempts

    return repair_attempts


def recover_from_failure() -> None:
    """Implement recovery logic."""


def _update_parsec_result_and_output_file(
    llm_response: str, function_name: str, parsec_result: ParsecResult, output_file: Path
) -> str:
    """Update the ParseC result and output file with the function with specifications.

    Args:
        llm_response (str): The response from the LLM.
        function_name (str): The name of the function that should be updated in the ParseC result
            and output file.
        parsec_result (ParsecResult): The ParseC result to update.
        output_file (Path): The path to the output file to update.

    Returns:
        str: The contents of the updated file.
    """
    updated_function_content = extract_function(llm_response)
    return function_util.update_function_declaration(
        function_name, updated_function_content, parsec_result, output_file
    )


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
    file_path.write_text(file_content, encoding="utf-8")


def _write_conversation_log(conversation_log: dict[str, list[LlmGenerateVerifyIteration]]) -> None:
    """Write the conversation log to disk.

    Args:
        conversation_log (dict[str, list[LlmGenerateVerifyIteration]]): The conversation log.
    """
    path_to_log = _get_path_to_conversation_log()
    path_to_log.write_text(
        json.dumps(
            {
                func_name: [attempt.to_dict() for attempt in attempts]
                for func_name, attempts in conversation_log.items()
            },
            indent=4,
        ),
        encoding="utf-8",
    )


def _get_path_to_conversation_log() -> Path:
    """Return the path to where the conversation log should be written.

    Returns:
        Path: The path to where the conversation log should be written.
    """
    current_time = int(time.time())
    path_to_log = Path(f"logs/specifications/{current_time}-specs.json")
    path_to_log.parent.mkdir(parents=True, exist_ok=True)
    return path_to_log


if __name__ == "__main__":
    main()
