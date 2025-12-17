"""Main entry point for specification generation and verification."""

# !/opt/miniconda3/bin/python

import argparse
import copy
from pathlib import Path

from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    AssumeSpec,
    BacktrackStrategy,
    BacktrackToCallee,
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

type Workstack = list[tuple[ParsecFunction, str]]

GLOBAL_PROOFSTATES: list[ProofState] = []


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
    _verify_program(functions_in_reverse_topological_order, specification_generator, parsec_result)


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
    functions: list[ParsecFunction],
    specification_generator: LlmSpecificationGenerator,
    parsec_result: ParsecResult,
) -> dict[str, FunctionSpecification]:
    initial_workstack: Workstack = [(function, "") for function in functions]
    initial_proof_state = ProofState(workstack=initial_workstack)

    GLOBAL_PROOFSTATES.append(initial_proof_state)

    while GLOBAL_PROOFSTATES:
        proof_state = GLOBAL_PROOFSTATES.pop()
        next_proofstates = _step(
            proof_state=proof_state,
            specification_generator=specification_generator,
            parsec_result=parsec_result,
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
    parsec_result: ParsecResult,
) -> list[ProofState]:
    function, hints = proof_state.peek_workstack()
    specs_for_function: list[FunctionSpecification] = specification_generator._generate_specs(
        function=function, backtracking_hint=hints
    )
    next_steps: list[tuple[FunctionSpecification, BacktrackStrategy]] = _choose_next_step(
        function=function, candidate_specs=specs_for_function, proof_state=proof_state
    )
    result: list[ProofState] = []

    for candidate_spec, backtrack_strategy in next_steps:
        next_proof_state = copy.copy(proof_state)  # `copy.copy` returns a shallow copy.
        next_proof_state.set_specification(function=function, spec=candidate_spec)
        _update_proof_state(
            function=function,
            proof_state=next_proof_state,
            backtrack_strategy=backtrack_strategy,
            parsec_result=parsec_result,
        )
        result.append(next_proof_state)
    return result


def _update_proof_state(
    function: ParsecFunction,
    proof_state: ProofState,
    backtrack_strategy: BacktrackStrategy,
    parsec_result: ParsecResult,
) -> ProofState:
    match backtrack_strategy:
        case AssumeSpec(_):
            proof_state.assume_function(function=function)
            # INVARIANT: the top element of the proof state's workstack should be the function
            # under specification generation + verification.
            proof_state.pop_workstack()
        case BacktrackToCallee(_, callee_name):
            if callee := parsec_result.get_function(callee_name):
                proof_state.push_onto_workstack(function=callee)
            else:
                msg = f"{callee_name} was missing from the ParsecResult"
                raise RuntimeError(msg)
        case unsupported_strategy:
            # This should never happen.
            msg = f"Unsupported backtracking strategy: {unsupported_strategy}"
            raise RuntimeError(msg)
    return proof_state


def _choose_next_step(
    function: ParsecFunction, candidate_specs: list[FunctionSpecification], proof_state: ProofState
) -> list[tuple[FunctionSpecification, BacktrackStrategy]]:
    return []
