"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import argparse
import json
import pickle as pkl
import subprocess
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
    Failure,
    GenerateRepairMetadata,
    LlmGenerateVerifyIteration,
    SpecificationGenerationContext,
    Success,
    VerificationResult,
)

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
    verified_functions: set[str] = set()
    conversation_log: dict[str, list[LlmGenerateVerifyIteration]] = defaultdict(list)
    specification_generator = LlmSpecificationGenerator(
        MODEL, parsec_result_without_direct_recursive_functions
    )

    specgen_context = SpecificationGenerationContext(
        verified_functions=verified_functions,
        parsec_result=parsec_result_without_direct_recursive_functions,
        output_file_path=output_file_path,
    )

    for func_name in func_ordering:
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

        specgen_context.set_function(function_to_verify)

        for _ in range(args.num_regeneration):
            if specgen_context.has_successful_verification_state():
                specgen_context.rollback_to_latest_verified_state()

            attempts = _generate_and_verify(
                specification_generator=specification_generator,
                specgen_context=specgen_context,
                num_repair_attempts=args.num_repair,
            )
            if not attempts:
                raise RuntimeError("Expected at least one generate specification iteration")

            if args.save_conversation:
                conversation_log[func_name].extend(attempts)

            final_attempt = attempts[-1]
            if isinstance(final_attempt.verification_result, Success):
                msg = (
                    f"Successfully verified '{final_attempt.function} "
                    f"({final_attempt.iteration_metadata})"
                )
                specgen_context.checkpoint_successful_verification()
                logger.success(msg)
                break  # Move on to the next function to verify.

            recover_from_failure()

    if args.save_conversation:
        _write_conversation_log(conversation_log)

    _save_functions_with_specs(parsec_result_without_direct_recursive_functions, output_file_path)


def _generate_and_verify(
    specification_generator: LlmSpecificationGenerator,
    specgen_context: SpecificationGenerationContext,
    num_repair_attempts: int,
) -> list[LlmGenerateVerifyIteration]:
    attempts = []
    conversation = [{"role": "system", "content": DEFAULT_SYSTEM_PROMPT}]

    # Initial specification generation.
    llm_invocation_result = specification_generator.generate_specifications(
        specgen_context, conversation
    )

    # Update the ParseC result and output file.
    _update_parsec_result_and_output_file(llm_invocation_result.response, specgen_context)

    # Verify the result.
    verification_result = verify_one_function(specgen_context)

    attempts.append(
        LlmGenerateVerifyIteration(
            function=specgen_context.get_function_name(),
            llm_invocation_result=llm_invocation_result,
            iteration_metadata=GenerateRepairMetadata(specgen_context),
            verification_result=verification_result,
        )
    )

    if isinstance(verification_result, Success):
        # Go no further if the initial specification verifies.
        specgen_context.add_verified_function(specgen_context.get_function_name())
        return attempts

    # Attempt to repair the faulty specification.
    repair_iterations = _run_repair_loop(
        specification_generator,
        specgen_context,
        verification_result,
        conversation,
        num_repair_attempts,
    )

    attempts.extend(repair_iterations)
    return attempts


def _run_repair_loop(
    specification_generator: LlmSpecificationGenerator,
    specgen_context: SpecificationGenerationContext,
    initial_verification_failure: Failure,
    conversation: list[dict[str, str]],
    num_repair_attempts: int,
) -> list[LlmGenerateVerifyIteration]:
    verification_result: VerificationResult = initial_verification_failure
    repair_attempts: list[LlmGenerateVerifyIteration] = []
    for n in range(num_repair_attempts):
        logger.info(
            f"Running repair for '{specgen_context.get_function_name()}' specs: "
            f"attempt {n + 1}/{num_repair_attempts}"
        )

        llm_invocation_result = specification_generator.repair_specifications(
            specgen_context, verification_result, conversation
        )
        _update_parsec_result_and_output_file(llm_invocation_result.response, specgen_context)

        verification_result = verify_one_function(specgen_context)
        repair_attempts.append(
            LlmGenerateVerifyIteration(
                specgen_context.get_function_name(),
                llm_invocation_result,
                GenerateRepairMetadata(specgen_context),
                verification_result,
            )
        )
        if isinstance(verification_result, Success):
            specgen_context.add_verified_function(specgen_context.get_function_name())
            return repair_attempts

    return repair_attempts


def recover_from_failure() -> None:
    """Implement recovery logic."""


def _update_parsec_result_and_output_file(
    llm_response: str, specgen_context: SpecificationGenerationContext
) -> str:
    """Update the ParseC result and output file with the function with specifications.

    Note: The return value of this function will be used in functions in future commits.

    Args:
        llm_response (str): The response from the LLM.
        specgen_context (SpecificationGenerationContext): The specification generation context.

    Returns:
        str: The contents of the updated file.
    """
    updated_function_content = extract_function(llm_response)
    return function_util.update_function_declaration(
        specgen_context.get_function_name(),
        updated_function_content,
        specgen_context.parsec_result,
        specgen_context.output_file_path,
    )


def verify_one_function(specgen_context: SpecificationGenerationContext) -> Success | Failure:
    """Return the result of verifying the function named `func_name` with CBMC.

    Args:
        specgen_context (SpecificationGenerationContext): The specification generation context.

    Raises:
        RuntimeError: Raised when an error occurs in executing the verification command.

    Returns:
        Success | Failure: Success if the function successfully verifies, Failure if the
            function does not verify.
    """
    func_name = specgen_context.get_function_name()
    output_file_path = specgen_context.output_file_path.absolute()
    replace_args = "".join(
        [f"--replace-call-with-contract {f} " for f in specgen_context.verified_functions]
    )
    verification_command = (
        f"goto-cc -o {func_name}.goto {output_file_path} --function {func_name} && "
        f"goto-instrument --partial-loops --unwind 5 {func_name}.goto {func_name}.goto && "
        f"goto-instrument {replace_args}"
        f"--enforce-contract {func_name} "
        f"{func_name}.goto checking-{func_name}-contracts.goto && "
        f"cbmc checking-{func_name}-contracts.goto --function {func_name} --depth 100"
    )

    logger.debug(f"Running command: {verification_command}")
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
