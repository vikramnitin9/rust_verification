"""Main entry point for specification generation and verification."""

# !/opt/miniconda3/bin/python

import argparse
import copy
from pathlib import Path

from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    BacktrackingStrategy,
    FunctionSpecification,
    ParsecFile,
    ParsecFunction,
    SpecConversation,
    copy_file_to_folder,
    ensure_lines_at_beginning,
)
from verification import (
    CbmcVerificationClient,
    ProofState,
    VerificationClient,
    VerificationInput,
    VerificationResult,
    WorkStack,
)

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_SPECIFICATION_CANDIDATES = 1
DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS = 10
DEFAULT_MODEL_TEMPERATURE = 1.0
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")

GLOBAL_PROOFSTATES: list[ProofState] = []
VERIFIER_CACHE: dict[VerificationInput, VerificationResult] = {}


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
    ensure_lines_at_beginning(header_lines, output_file_path)

    parsec_file = ParsecFile(input_file_path)
    verifier: VerificationClient = CbmcVerificationClient(VERIFIER_CACHE)
    specification_generator = LlmSpecificationGenerator(
        MODEL,
        system_prompt=DEFAULT_SYSTEM_PROMPT,
        verifier=verifier,
        num_specification_candidates=args.num_specification_generation_candidates,
        num_repair_iterations=args.num_specification_repair_iterations,
    )

    functions_in_reverse_topological_order = _get_functions_in_reverse_topological_order(
        parsec_file
    )
    _verify_program(functions_in_reverse_topological_order, specification_generator, parsec_file)


if __name__ == "__main__":
    main()


def _get_functions_in_reverse_topological_order(
    parsec_file: ParsecFile,
) -> list[ParsecFunction]:
    # Get a list of functions in reverse topological order,
    # i.e., starting from the leaves of the call graph.
    function_names = parsec_file.copy(
        remove_self_edges_in_call_graph=True
    ).get_function_names_in_topological_order(reverse_order=True)
    functions: list[ParsecFunction] = []
    for function_name in function_names:
        if function := parsec_file.get_function(function_name):
            functions.append(function)
        else:
            logger.warning(f"Function '{function_name}' was missing from the ParsecFile")
    return functions


def _verify_program(
    functions: list[ParsecFunction],
    specification_generator: LlmSpecificationGenerator,
    parsec_file: ParsecFile,
) -> dict[str, FunctionSpecification]:
    initial_workstack: WorkStack = WorkStack([(function, "") for function in functions])
    initial_proof_state = ProofState(workstack=initial_workstack)

    GLOBAL_PROOFSTATES.append(initial_proof_state)

    while GLOBAL_PROOFSTATES:
        proof_state = GLOBAL_PROOFSTATES.pop()
        next_proofstates = _step(
            proof_state=proof_state,
            specification_generator=specification_generator,
            parsec_file=parsec_file,
        )

        for next_proofstate in next_proofstates:
            if next_proofstate.is_workstack_empty():
                return next_proofstate.get_specifications()
            GLOBAL_PROOFSTATES.append(next_proofstate)

    # We timed out or ran out of proof states to specify without finding one
    # with an empty work stack.
    raise RuntimeError()


def _step(
    proof_state: ProofState,
    specification_generator: LlmSpecificationGenerator,
    parsec_file: ParsecFile,  # noqa: ARG001
) -> list[ProofState]:
    work_item = proof_state.peek_workstack()
    spec_conversations_for_function: list[SpecConversation] = (
        specification_generator.generate_and_repair_spec(
            function=work_item.function,
            backtracking_hint=work_item.backtracking_hint,
            proof_state=proof_state,
        )
    )

    # TODO: actually perform pruning, here.
    pruned_spec_conversations_for_function = spec_conversations_for_function

    result: list[ProofState] = []

    for spec_conversation in pruned_spec_conversations_for_function:
        next_proof_state = copy.copy(proof_state)  # `copy.copy` returns a shallow copy.
        next_proof_state.set_specification(
            function=work_item.function, spec=spec_conversation.specification
        )
        latest_llm_response = spec_conversation.get_latest_llm_response()
        if (
            spec_conversation.backtracking_strategy == BacktrackingStrategy.REGENERATE_CALLEE_SPEC
            or spec_conversation.backtracking_strategy == BacktrackingStrategy.REPAIR_SPEC
        ):
            next_proof_state.push_onto_workstack(
                function=work_item.function, hint=latest_llm_response
            )
        else:
            # No backtracking to consider.
            next_proof_state.pop_workstack()
    return result
