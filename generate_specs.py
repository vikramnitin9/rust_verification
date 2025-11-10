"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from specifications import LlmSpecificationGenerator
from util import (
    ParsecResult,
    extract_function,
    function_util,
)
from verification import Failure, Success

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_VERIFICATION_ATTEMPTS = 10


def main() -> None:
    """Generate specifications for C functions using an LLM and verify them with CBMC."""
    input_file_path = Path(sys.argv[1])
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
    conversation = [{"role": "system", "content": "You are an intelligent coding assistant"}]
    specification_generator = LlmSpecificationGenerator(
        MODEL, parsec_result_without_direct_recursive_functions
    )

    for func_name in func_ordering:
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

        # Generate the initial specifications for verification.
        (_, response) = specification_generator.generate_specifications(func_name, conversation)
        _update_output_file_and_parsec_result(
            response, func_name, parsec_result_without_direct_recursive_functions, output_file_path
        )

        for n in range(DEFAULT_NUM_VERIFICATION_ATTEMPTS):
            # Attempt to verify the generated specifications for the function.
            match verify_one_function(func_name, verified_functions, output_file_path):
                case Success():
                    print(f"Verification succeeded for '{func_name}' ({n + 1} attempt[s])")
                    verified_functions.append(func_name)
                    break
                case Failure(error_message):
                    print(
                        f"Verification failed for '{func_name}' "
                        f"regenerating specs and re-trying: "
                        f"{n + 1}/{DEFAULT_NUM_VERIFICATION_ATTEMPTS}"
                    )
                    # Repair specifications
                    (_, response) = specification_generator.repair_specifications(
                        func_name, error_message, conversation
                    )
                    _update_output_file_and_parsec_result(
                        response,
                        func_name,
                        parsec_result_without_direct_recursive_functions,
                        output_file_path,
                    )
                case unexpected_verification_result:
                    msg = f"Unexpected verification result: {unexpected_verification_result}"
                    raise RuntimeError(msg)

        if func_name not in verified_functions:
            recover_from_failure()


def recover_from_failure() -> None:
    """Implement recovery logic."""
    raise NotImplementedError("TODO: Implement me")


def _update_output_file_and_parsec_result(
    llm_response: str, function_name: str, parsec_result: ParsecResult, output_file: Path
) -> None:
    updated_function_content = extract_function(llm_response)
    function_util.update_function_declaration(
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
    file_path.open(mode="w", encoding="utf-8").write(file_content)


if __name__ == "__main__":
    main()
