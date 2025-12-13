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
    ParsecFile,
    copy_file_to_folder,
    extract_function,
    function_util,
    ensure_lines_at_beginning,
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
    output_file_path = copy_file_to_folder(input_file_path, "specs")
    header_lines = [f"#include <{header}>" for header in DEFAULT_HEADERS_IN_OUTPUT]
    ensure_lines_at_beginning(header_lines, output_file_path)

    parsec_result = ParsecFile(output_file_path)

    # Get a list of functions in reverse topological order.
    func_ordering = parsec_result.copy(
        remove_self_edges_in_call_graph=True
    ).get_function_names_in_topological_order(reverse_order=True)
    verified_functions: list[str] = []
    trusted_functions: list[str] = []
    conversation_log: dict[str, list[LlmGenerateVerifyIteration]] = defaultdict(list)
    specification_generator = LlmSpecificationGenerator(MODEL, parsec_result)
    verifier: VerificationClient = CbmcVerificationClient()

    for func_name in func_ordering:
        conversation = [{"role": "system", "content": DEFAULT_SYSTEM_PROMPT}]

        logger.info(f"Processing function {func_name}...")
        function_to_verify = parsec_result.get_function(func_name)

        # Generate the initial specifications for verification.
        llm_invocation_result = specification_generator.generate_specifications(
            func_name,
            conversation,
            args.num_specification_generation_samples,
            args.model_temperature,
        )

        # Create a temporary file with the candidate specs.
        function_with_candidate_specs = extract_function(llm_invocation_result.responses[0])
        file_with_candidate_specs = function_util.get_file_with_updated_function(
            func_name,
            function_with_candidate_specs,
            parsec_result,
            output_file_path,
        )
        # If the function is recursive, accept the generated specs and continue.
        if function_to_verify.is_direct_recursive():
            logger.info(
                f"Generated specs for direct-recursive function '{func_name}', "
                "its specifications will be trusted"
            )
            trusted_functions.append(func_name)
            _update_with_verified_function(
                func_name,
                function_with_candidate_specs,
                file_with_candidate_specs,
                parsec_result,
                output_file_path,
            )
            if args.save_conversation:
                conversation_log[func_name].append(
                    LlmGenerateVerifyIteration(func_name, llm_invocation_result, Success())
                )
            continue

        verification_result = verifier.verify(
            function_name=func_name,
            names_of_verified_functions=verified_functions,
            names_of_trusted_functions=trusted_functions,
            file_path=file_with_candidate_specs,
        )
        if args.save_conversation:
            conversation_log[func_name].append(
                LlmGenerateVerifyIteration(func_name, llm_invocation_result, verification_result)
            )

        if isinstance(verification_result, Success):
            logger.success(f"Verification succeeded for '{func_name}'")
            verified_functions.append(func_name)
            # Update the ParsecFile and output file
            _update_with_verified_function(
                func_name,
                function_with_candidate_specs,
                file_with_candidate_specs,
                parsec_result,
                output_file_path,
            )
            continue
        logger.warning(
            f"Verification failed for '{func_name}'; attempting to repair the generated specs"
        )

        for n in range(args.num_repair):
            llm_invocation_result = specification_generator.repair_specifications(
                func_name,
                verification_result,
                conversation,
            )
            # Create a temporary file with the candidate specs.
            function_with_candidate_specs = extract_function(llm_invocation_result.responses[0])
            file_with_candidate_specs = function_util.get_file_with_updated_function(
                func_name,
                function_with_candidate_specs,
                parsec_result,
                output_file_path,
            )
            verification_result = verifier.verify(
                function_name=func_name,
                names_of_verified_functions=verified_functions,
                names_of_trusted_functions=trusted_functions,
                file_path=file_with_candidate_specs,
            )
            if args.save_conversation:
                conversation_log[func_name].append(
                    LlmGenerateVerifyIteration(
                        func_name, llm_invocation_result, verification_result
                    )
                )
            if isinstance(verification_result, Success):
                logger.success(f"Verification succeeded for '{func_name}'")
                verified_functions.append(func_name)
                _update_with_verified_function(
                    func_name,
                    function_with_candidate_specs,
                    file_with_candidate_specs,
                    parsec_result,
                    output_file_path,
                )
                break
            logger.warning(f"Verification failed for '{func_name}'; on repair attempt {n + 1}")

        if func_name not in verified_functions:
            logger.warning(
                f"{func_name} failed to verify after {args.num_repair} repair attempt(s)"
            )
            recover_from_failure()
    if args.save_conversation:
        _write_conversation_log(conversation_log)

    _save_functions_with_specs(parsec_result, output_file_path)


def recover_from_failure() -> None:
    """Implement recovery logic."""


def _update_with_verified_function(
    function_name: str,
    function_with_verified_specs: str,
    path_to_file_with_verified_specs: Path,
    parsec_result: ParsecFile,
    path_to_verified_output: Path,
) -> None:
    """Update the Parsec result and the verified output file with the newly-verified function.

    Args:
        function_name (str): The name of the newly-verified function.
        function_with_verified_specs (str): The source code of the newly-verified function.
        path_to_file_with_verified_specs (Path): The file with the newly-verified specs.
        parsec_result (ParsecFile): The parsec result to update.
        path_to_verified_output (Path): The path to the verified output file.
    """
    function_util.update_parsec_result(function_name, function_with_verified_specs, parsec_result)
    verified_file_content = path_to_file_with_verified_specs.read_text(encoding="utf-8")
    path_to_verified_output.write_text(verified_file_content, encoding="utf-8")
    path_to_file_with_verified_specs.unlink()


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


def _save_functions_with_specs(parsec_result: ParsecFile, output_file_path: Path) -> None:
    """Write functions from a ParseC result that have specifications to disk.

    This is needed for specification translation. Ideally, the specified functions would be read
    directly from the source file resulting directly from specification generation. However, CBMC
    specifications are not legal C code, and are not able to be easily parsed (e.g., with ParseC).

    Args:
        parsec_result (ParsecFile): The ParseC result in which to look for specified functions.
        output_file_path (Path): The file where the result of specification generation is saved.
    """
    functions_with_specs = [f for f in parsec_result.functions.values() if f.has_specification()]
    result_file = output_file_path.with_suffix("")
    with Path(f"{result_file}-specified-functions.pkl").open("wb") as f:
        pkl.dump(functions_with_specs, f)


if __name__ == "__main__":
    main()
