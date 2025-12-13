"""Main entry point for specification generation and verification."""

# !/opt/miniconda3/bin/python

import argparse
from pathlib import Path

from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    FunctionSpecification,
    ParsecFunction,
    ParsecResult,
    copy_file_to_folder,
    insert_lines_at_beginning,
)
from verification import CbmcVerificationClient, ProofState, VerificationClient

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_SPECIFICATION_CANDIDATES = 1
DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS = 10
DEFAULT_MODEL_TEMPERATURE = 1.0
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")

GLOBAL_WORKSTACKS = []


def main() -> None:
    """Generate specifications for C functions using an LLM and verify them with CBMC."""
    parser = argparse.ArgumentParser(
        prog="main.py", description="Generate and verify CBMC specifications for a C file."
    )
    parser.add_argument(
        "--file",
        required=True,
        help="Path to the C file for which to generate and verify specifications.",
    )
    parser.add_argument(
        "--num-specification-candidates",
        required=False,
        help="The number of candidate specifications to generate for a function.",
        default=DEFAULT_NUM_SPECIFICATION_CANDIDATES,
        type=int,
    )
    parser.add_argument(
        "--num-specification-repair-iterations",
        required=False,
        help="The number of times to attempt to repair a faulty specification.",
        default=DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS,
        type=int,
    )
    args = parser.parse_args()

    input_file_path = Path(args.file)
    output_file_path = copy_file_to_folder(input_file_path, "specs")
    header_lines = [f"#include <{header}>" for header in DEFAULT_HEADERS_IN_OUTPUT]
    insert_lines_at_beginning(header_lines, output_file_path)

    parsec_result = ParsecResult(input_file_path)
    verifier: VerificationClient = CbmcVerificationClient()
    specification_generator = LlmSpecificationGenerator(
        MODEL,
        system_prompt=DEFAULT_SYSTEM_PROMPT,
        verifier=verifier,
        num_specification_generation_candidates=args.num_specification_generation_candidates,
    )

    functions_in_reverse_topological_order = _get_functions_in_reverse_topological_order(
        parsec_result
    )
    _verify_program(functions_in_reverse_topological_order)


if __name__ == "__main__":
    main()


def _get_functions_in_reverse_topological_order(
    parsec_result: ParsecResult,
) -> list[ParsecFunction]:
    # Get a list of functions in reverse topological order,
    # i.e., starting from the leaves of the call graph.
    function_names = parsec_result.copy(
        remove_self_edges_in_call_graph=True
    ).get_function_names_in_topological_order(reverse_order=True)
    functions: list[ParsecFunction] = []
    for function_name in function_names:
        if function := parsec_result.get_function(function_name):
            functions.append(function)
        else:
            logger.warning(f"Function '{function_name}' was missing from the ParsecResult")
    return functions


def _verify_program(
    functions: list[ParsecFunction], specification_generator: LlmSpecificationGenerator
) -> dict[str, FunctionSpecification]:
    initial_workstack: list[tuple[ParsecFunction, str]] = [(function, "") for function in functions]
    initial_proof_state = ProofState(workstack=initial_workstack)
    raise NotImplementedError("Implement me")
