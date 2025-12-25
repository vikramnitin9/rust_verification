#!/opt/miniconda3/bin/python

"""Main entry point for specification generation and verification."""

import argparse
import copy
import tempfile
from pathlib import Path

from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    BacktrackingStrategy,
    CFunction,
    FunctionSpecification,
    ParsecFile,
    SpecConversation,
    copy_file_to_folder,
    ensure_lines_at_beginning,
    function_util,
)
from verification import (
    CbmcVerificationClient,
    ProofState,
    VerificationClient,
    VerificationContextManager,
    VerificationInput,
    VerificationResult,
    WorkStack,
)

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_SPECIFICATION_CANDIDATES = 10
DEFAULT_NUM_REPAIR_CANDIDATES = 1
DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS = 3
DEFAULT_MODEL_TEMPERATURE = 1.0
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")
DEFAULT_RESULT_DIR = "specs"

GLOBAL_PROOFSTATES: list[ProofState] = []
VERIFIER_CACHE: dict[VerificationInput, VerificationResult] = {}
CONTEXT_MANAGER: VerificationContextManager = VerificationContextManager()

tempfile.tempdir = DEFAULT_RESULT_DIR


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
        "--num-repair-candidates",
        required=False,
        help="The number of repaired specifications to return during a repair iteration.",
        default=DEFAULT_NUM_REPAIR_CANDIDATES,
        type=int,
    )
    parser.add_argument(
        "--num-specification-repair-iterations",
        required=False,
        help="The number of times to attempt to repair a faulty specification.",
        default=DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS,
        type=int,
    )
    parser.add_argument(
        "--use-llm-response-cache",
        action="store_true",
        help="Whether to use cached LLM responses for specification generation and repair.",
    )
    args = parser.parse_args()

    input_file_path = Path(args.file)
    output_file_path = copy_file_to_folder(input_file_path, DEFAULT_RESULT_DIR)
    header_lines = [f"#include <{header}>" for header in DEFAULT_HEADERS_IN_OUTPUT]
    ensure_lines_at_beginning(header_lines, output_file_path)
    parsec_file = ParsecFile(input_file_path)
    verifier: VerificationClient = CbmcVerificationClient(
        cache=VERIFIER_CACHE, context_manager=CONTEXT_MANAGER
    )
    specification_generator = LlmSpecificationGenerator(
        MODEL,
        system_prompt=DEFAULT_SYSTEM_PROMPT,
        verifier=verifier,
        verification_context_manager=CONTEXT_MANAGER,
        parsec_file=parsec_file,
        num_specification_candidates=args.num_specification_candidates,
        num_repair_candidates=args.num_repair_candidates,
        num_repair_iterations=args.num_specification_repair_iterations,
        use_cache=args.use_llm_response_cache,
    )

    functions_in_reverse_topological_order = _get_functions_in_reverse_topological_order(
        parsec_file
    )
    _verify_program(functions_in_reverse_topological_order, specification_generator)


def _get_functions_in_reverse_topological_order(
    parsec_file: ParsecFile,
) -> list[CFunction]:
    # Get a list of functions in reverse topological order,
    # i.e., starting from the leaves of the call graph.
    function_names = parsec_file.get_function_names_in_topological_order(reverse_order=True)
    functions: list[CFunction] = []
    for function_name in function_names:
        if function := parsec_file.get_function(function_name):
            functions.append(function)
        else:
            logger.warning(f"Function '{function_name}' was missing from the ParsecFile")
    return functions


def _verify_program(
    functions: list[CFunction],
    specification_generator: LlmSpecificationGenerator,
) -> dict[str, FunctionSpecification]:
    initial_workstack: WorkStack = WorkStack([(function, "") for function in functions[::-1]])
    initial_proof_state = ProofState(workstack=initial_workstack)

    GLOBAL_PROOFSTATES.append(initial_proof_state)

    while GLOBAL_PROOFSTATES:
        proof_state = GLOBAL_PROOFSTATES.pop()
        next_proofstates = _step(
            proof_state=proof_state,
            specification_generator=specification_generator,
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
) -> list[ProofState]:
    work_item = proof_state.peek_workstack()
    spec_conversations_for_function: list[SpecConversation] = (
        specification_generator.generate_and_repair_spec(
            function=work_item.function,
            backtracking_hint=work_item.backtracking_hint,
            proof_state=proof_state,
        )
    )

    pruned_spec_conversations_for_function = _prune_specs(
        function=work_item.function,
        spec_conversations=spec_conversations_for_function,
        proof_state=proof_state,
    )

    result: list[ProofState] = []

    for spec_conversation in pruned_spec_conversations_for_function:
        # A deep copy is desirable here because the original proof state should not be modified.
        next_proof_state = copy.deepcopy(proof_state)
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
            # The specification has been successfully verified; no backtracking to consider
            next_proof_state.pop_workstack()
            # TODO: Uncomment once we have a strategy around writing verified specs to disk.
            # _write_verified_spec(
            #     function=work_item.function, specification=spec_conversation.specification
            # )
        result.append(next_proof_state)
    return result


def _prune_specs(
    function: CFunction, spec_conversations: list[SpecConversation], proof_state: ProofState
) -> list[SpecConversation]:
    pruned_specs = []
    for spec_conversation in spec_conversations:
        contents_of_verified_file = spec_conversation.contents_of_file_to_verify
        if contents_of_verified_file is None:
            msg = f"{spec_conversation} was missing file contents that were run under verification"
            raise ValueError(msg)
        vcontext = CONTEXT_MANAGER.current_context(function=function, proof_state=proof_state)
        vinput = VerificationInput(
            function=function,
            spec=spec_conversation.specification,
            context=vcontext,
            contents_of_file_to_verify=contents_of_verified_file,
        )
        if vresult := VERIFIER_CACHE.get(vinput):
            if vresult.succeeded:
                pruned_specs.append(spec_conversation)
    return pruned_specs


def _write_verified_spec(function: CFunction, specification: FunctionSpecification) -> None:
    path_to_original_file = Path(function.file_name)
    original_file_dir = str(path_to_original_file.parent).lstrip("/")
    result_file_dir = Path(DEFAULT_RESULT_DIR) / Path(original_file_dir)
    result_file = result_file_dir / path_to_original_file.name

    if not result_file.exists():
        # Create the result file by copying over the original file.
        result_file.write_text(path_to_original_file.read_text(), encoding="utf-8")

    parsec_file = ParsecFile(result_file)
    function_with_verified_spec = function_util.get_source_code_with_inserted_spec(
        function_name=function.name,
        specification=specification,
        parsec_file=parsec_file,
        comment_out_spec=True,
    )

    function_util.update_function_declaration(
        function_name=function.name,
        updated_function_content=function_with_verified_spec,
        parsec_file=parsec_file,
        file=result_file,
    )


if __name__ == "__main__":
    main()
