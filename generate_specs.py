#!/opt/miniconda3/bin/python

"""Script to generate specifications for C functions using an LLM and verify them with CBMC."""

from __future__ import annotations

import argparse
import heapq
import json
import pickle as pkl
import time
from collections import defaultdict
from pathlib import Path

from loguru import logger

from specifications import LlmSpecificationGenerator, SpecifiedFunctionSample
from util import (
    ParsecResult,
    copy_file_to_folder,
    extract_function,
    function_util,
    insert_lines_at_beginning,
    overwrite_file,
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
    insert_lines_at_beginning(header_lines, output_file_path)

    parsec_result = ParsecResult(output_file_path)
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
        if not function_to_verify:
            msg = f"Failed to find function '{func_name}' to verify"
            raise RuntimeError(msg)

        # Generate the initial specifications for verification.
        llm_invocation_result = specification_generator.generate_specifications(
            func_name,
            conversation,
            args.num_specification_generation_samples,
            args.model_temperature,
        )

        # Create specified function samples for each LLM response.
        specified_function_samples = SpecifiedFunctionSample.get_specified_function_samples(
            func_name, llm_invocation_result, parsec_result, output_file_path
        )
        # Keep track of the failing samples, ordered the number of failures.
        failing_samples: list[tuple[int, int, SpecifiedFunctionSample]] = []

        # Check if any of the samples verify before moving on to repair.
        for i, sample in enumerate(specified_function_samples):
            verification_result = verifier.verify(
                function_name=func_name,
                names_of_verified_functions=verified_functions,
                names_of_trusted_functions=trusted_functions,
                file_path=sample.path_to_file,
            )
            sample.verification_result = verification_result
            if isinstance(sample.verification_result, Success):
                logger.success(f"Verification succeeded for '{func_name}' for sample {i + 1}")
                verified_functions.append(func_name)
                # Update the ParsecResult and output file with the verified function.
                _update_with_verified_function(
                    func_name,
                    sample.specified_function,
                    sample.path_to_file,
                    parsec_result,
                    output_file_path,
                )
                break
            # Order the samples by the number of failures reported.
            heapq.heappush(failing_samples, (sample.verification_result.num_failures, i, sample))

        if any(
            isinstance(sample.verification_result, Success) for sample in specified_function_samples
        ):
            for sample in specified_function_samples:
                sample.delete_temporary_files()
            continue

        if function_to_verify.is_direct_recursive():
            # Trust the generated specification, continue on to other functions.
            logger.debug(f"'{func_name}' is direct recursive, its specifications will be trusted")
            trusted_functions.append(func_name)
            _, _, sample_with_fewest_failures = heapq.heappop(failing_samples)
            _update_with_verified_function(
                func_name,
                sample_with_fewest_failures.specified_function,
                sample_with_fewest_failures.path_to_file,
                parsec_result,
                output_file_path,
            )
            for sample in specified_function_samples:
                sample.delete_temporary_files()
            continue

        # Perform repair.
        logger.warning(f"Verification failed for '{func_name}' for all samples, attempting repair.")

        repaired_specification: SpecifiedFunctionSample | None = None
        while failing_samples:
            _, _, failing_sample = heapq.heappop(failing_samples)
            repaired_specification = _get_repaired_specification(
                failing_sample,
                specification_generator,
                verifier,
                conversation,
                args.num_repair,
                verified_functions,
                trusted_functions,
                conversation_log,
                args.save_conversation,
            )
            if repaired_specification:
                logger.success(f"Verification succeeded for '{func_name}'")
                verified_functions.append(func_name)
                # Update the ParsecResult and output file
                _update_with_verified_function(
                    func_name,
                    repaired_specification.specified_function,
                    repaired_specification.path_to_file,
                    parsec_result,
                    output_file_path,
                )
                break

        if repaired_specification:
            for sample in specified_function_samples:
                sample.delete_temporary_files()
            continue

        logger.warning(
            f"Function '{func_name}' failed to verify after {args.num_repair} repair attempts "
            f"for {args.num_specification_generation_samples} samples"
        )
        recover_from_failure()

    if args.save_conversation:
        _write_conversation_log(conversation_log)

    _save_functions_with_specs(parsec_result, output_file_path)


def recover_from_failure() -> None:
    """Implement recovery logic."""


def _get_repaired_specification(
    failing_function_sample: SpecifiedFunctionSample,
    specification_generator: LlmSpecificationGenerator,
    verification_client: VerificationClient,
    conversation: list[dict[str, str]],
    num_repair_iterations: int,
    verified_functions: list[str],
    trusted_functions: list[str],
    conversation_log: dict[str, list[LlmGenerateVerifyIteration]],
    should_save_conversation: bool,
) -> SpecifiedFunctionSample | None:
    sample_under_repair = failing_function_sample
    for i in range(num_repair_iterations):
        name_of_function_under_repair = sample_under_repair.function_name
        if not sample_under_repair.verification_result:
            raise ValueError("Sample under repair is missing a verification result")

        llm_invocation_result = specification_generator.repair_specifications(
            sample_under_repair,
            conversation,
        )
        # Create a temporary file with the candidate specs.
        function_with_repaired_specs = extract_function(llm_invocation_result.responses[0])
        path_to_repaired_spec = (
            sample_under_repair.path_to_file.parent
            / f"repair_{i + 1}{sample_under_repair.path_to_file.suffix}"
        )
        file_with_repaired_specs = function_util.get_file_with_updated_function(
            name_of_function_under_repair,
            function_with_repaired_specs,
            sample_under_repair.parsec_result,
            sample_under_repair.path_to_file,
            path_to_repaired_spec,
        )
        verification_result = verification_client.verify(
            function_name=name_of_function_under_repair,
            names_of_verified_functions=verified_functions,
            names_of_trusted_functions=trusted_functions,
            file_path=file_with_repaired_specs,
        )
        if should_save_conversation:
            conversation_log[name_of_function_under_repair].append(
                LlmGenerateVerifyIteration(
                    failing_function_sample.function_name,
                    llm_invocation_result,
                    verification_result,
                )
            )
        latest_repair_sample = SpecifiedFunctionSample(
            name_of_function_under_repair,
            function_with_repaired_specs,
            file_with_repaired_specs,
            verification_result,
        )
        if latest_repair_sample.is_verified():
            return latest_repair_sample
        sample_under_repair = latest_repair_sample
    return None


def _update_with_verified_function(
    function_name: str,
    function_with_verified_specs: str,
    path_to_file_with_verified_specs: Path,
    parsec_result: ParsecResult,
    path_to_verified_output: Path,
) -> None:
    """Update the Parsec result and the verified output file with the newly-verified function.

    Args:
        function_name (str): The name of the newly-verified function.
        function_with_verified_specs (str): The source code of the newly-verified function.
        path_to_file_with_verified_specs (Path): The path to the file with the newly-verified specs.
        parsec_result (ParsecResult): The parsec result to update.
        path_to_verified_output (Path): The path to the verified output file.
    """
    function_util.update_parsec_result(function_name, function_with_verified_specs, parsec_result)
    verified_file_content = path_to_file_with_verified_specs.read_text(encoding="utf-8")
    overwrite_file(verified_file_content, path_to_verified_output)
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
