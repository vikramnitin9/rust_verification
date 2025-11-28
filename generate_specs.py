#!/opt/miniconda3/bin/python

"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import argparse
import json
import pickle as pkl
import time
from collections import defaultdict
from pathlib import Path

from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    ParsecResult,
    extract_function,
    function_util,
)
from verification import (
    CbmcVerificationClient,
    LlmGenerateVerifyIteration,
    Success,
    VerificationClient,
)

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_SPECIFICATION_GENERATION_SAMPLES = 1
DEFAULT_NUM_REPAIR_ATTEMPTS = 10
DEFAULT_MODEL_TEMPERATURE = 1.0
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")


def main() -> None:
    """Generate specifications for C functions using an LLM and verify them with CBMC."""
    parser = argparse.ArgumentParser(
        prog="generate_specs.py", description="Generate CBMC specifications for a C file."
    )
    parser.add_argument(
        "--file", required=True, help="Path to the C file for which to generate specifications."
    )
    parser.add_argument(
        "--num-specification-generation-samples",
        required=False,
        help="The number of samples for specification generation.",
        default=DEFAULT_NUM_SPECIFICATION_GENERATION_SAMPLES,
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
        "--model-temperature",
        required=False,
        help="The temperature to use for specification generation",
        default=DEFAULT_MODEL_TEMPERATURE,
        type=float,
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
    specification_generator = LlmSpecificationGenerator(
        MODEL, parsec_result_without_direct_recursive_functions
    )
    verifier: VerificationClient = CbmcVerificationClient()

    for func_name in func_ordering:
        conversation = [{"role": "system", "content": DEFAULT_SYSTEM_PROMPT}]
        if func_name in recursive_funcs:
            logger.info(
                f"Skipping self-recursive function {func_name} because of CBMC bugs/limitations."
            )
            continue

        logger.info(f"Processing function {func_name}...")
        function_to_verify = parsec_result_without_direct_recursive_functions.get_function(
            func_name
        )
        if not function_to_verify:
            msg = f"Failed to find function '{func_name}' to verify"
            raise RuntimeError(msg)

        # Generate the initial specifications for verification.
        llm_invocation_result = specification_generator.generate_specifications(
            func_name,
            conversation,
            args.num_specification_generation_samples,
            temperature=args.model_temperature,
        )
        _update_parsec_result_and_output_file(
            llm_invocation_result.responses[0],
            func_name,
            parsec_result_without_direct_recursive_functions,
            output_file_path,
        )
        # Attempt to verify the generated specifications for the function.
        verification_result = verifier.verify(
            function_name=func_name,
            names_of_verified_functions=verified_functions,
            names_of_trusted_functions=[],
            file_path=output_file_path,
        )
        if args.save_conversation:
            conversation_log[func_name].append(
                LlmGenerateVerifyIteration(func_name, llm_invocation_result, verification_result)
            )

        if isinstance(verification_result, Success):
            logger.success(f"Verification succeeded for '{func_name}'")
            verified_functions.append(func_name)
            continue
        logger.warning(
            f"Verification failed for '{func_name}'; attempting to repair the generated specs"
        )

        for n in range(args.num_repair):
            # Try to repair specifications for verification.
            llm_invocation_result = specification_generator.repair_specifications(
                func_name,
                verification_result,
                conversation,
            )
            _update_parsec_result_and_output_file(
                llm_invocation_result.responses[0],
                func_name,
                parsec_result_without_direct_recursive_functions,
                output_file_path,
            )
            verification_result = verifier.verify(
                function_name=func_name,
                names_of_verified_functions=verified_functions,
                names_of_trusted_functions=[],
                file_path=output_file_path,
            )
            if args.save_conversation:
                conversation_log[func_name].append(
                    LlmGenerateVerifyIteration(
                        func_name, llm_invocation_result, verification_result
                    )
                )
            if isinstance(verification_result, Success):
                logger.success(
                    f"Verification succeeded for '{func_name}' after "
                    f"{n + 1}/{args.num_repair} repair attempt(s)"
                )
                verified_functions.append(func_name)
                break  # Move on to the next function to generate specs and verify.
            logger.warning(f"Verification failed for '{func_name}'; on repair attempt {n + 1}")

        if func_name not in verified_functions:
            logger.warning(
                f"{func_name} failed to verify after {args.num_repair} repair attempt(s)"
            )
            recover_from_failure()
    if args.save_conversation:
        _write_conversation_log(conversation_log)

        _save_functions_with_specs(
            parsec_result_without_direct_recursive_functions, output_file_path
        )


def recover_from_failure() -> None:
    """Implement recovery logic."""


def _update_parsec_result_and_output_file(
    llm_response: str, function_name: str, parsec_result: ParsecResult, output_file: Path
) -> str:
    """Update the ParseC result and output file with the function with specifications.

    Note: The return value of this function will be used in functions in future commits.

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


def _save_functions_with_specs(parsec_result: ParsecResult, output_file_path: Path) -> None:
    """Write functions from a ParseC result that have specifications to disk.

    This is needed for specification translation. Ideally, the specified functions would be read
    directly from the source file resulting directly from specification generation. However, CBMC
    specifications are not legal C code, and are not able to be easily parsed (e.g., with ParseC).

    Args:
        parsec_result (ParsecResult): The ParseC result in which to look for specified functions.
        output_file_path (Path): The path to the file where the result of specification generation
            is saved.
    """
    functions_with_specs = [f for f in parsec_result.functions.values() if f.is_specified()]
    result_file = output_file_path.with_suffix("")
    with Path(f"{result_file}-specified-functions.pkl").open("wb") as f:
        pkl.dump(functions_with_specs, f)


if __name__ == "__main__":
    main()
