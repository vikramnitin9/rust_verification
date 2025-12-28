#!/opt/miniconda3/bin/python

"""Main entry point for specification generation and verification."""

import argparse
import copy
import tempfile
from collections import defaultdict, deque
from pathlib import Path
from types import MappingProxyType

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

GLOBAL_OBSERVED_PROOFSTATES: set[ProofState] = set()
# Every ProofState in this queue is incomplete (i.e., their worklists are non-empty.)
GLOBAL_INCOMPLETE_PROOFSTATES: deque[ProofState] = deque()
# Every ProofState in this queue is complete (i.e., their worklists are empty.)
GLOBAL_COMPLETE_PROOFSTATES: deque[ProofState] = deque()
# MDE: This should be a `diskcache` rather than a Python dict.
VERIFIER_CACHE: dict[VerificationInput, VerificationResult] = {}
CONTEXT_MANAGER: VerificationContextManager = VerificationContextManager()

tempfile.tempdir = DEFAULT_RESULT_DIR


def main() -> None:
    """Generate specifications for C functions using an LLM and verify them with CBMC."""
    # MDE: Is it all the C functions in a file?  In multiple files?  Can it be a subset of them?
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
        help="The LLM generates this many candidate specifications for each function.",
        default=DEFAULT_NUM_SPECIFICATION_CANDIDATES,
        type=int,
    )
    parser.add_argument(
        "--num-repair-candidates",
        required=False,
        help="The LLM rectuns this many repaired specifications for each unverifiable spec.",
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
    # MDE: I think this should default to true.
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

    functions_in_reverse_topological_order = parsec_file.get_functions_in_topological_order(
        reverse_order=True
    )
    _verify_program(functions_in_reverse_topological_order, specification_generator)


# MDE: When does this function exit?
def _verify_program(
    functions: list[CFunction],
    specification_generator: LlmSpecificationGenerator,
) -> MappingProxyType[CFunction, list[FunctionSpecification]]:
    """Return an immutable map of function names to their CBMC specifications.

    Each returned specification is either verified or assumed.

    Args:
        functions (list[CFunction]): The functions for which to generate and verify specifications,
            in reverse topological order.
        specification_generator (LlmSpecificationGenerator): The specification generator.

    Returns:
        MappingProxyType[CFunction, FunctionSpecification]: An immutable map of function to their
            CBMC-verified specifications.
            # MDE: I'm not clear about the purpose of the map.  Could a list of
            # FunctionSpecification be returned instead?
    """
    # MDE: Please comment why the last element of `functions` does not appear in the workstack.
    initial_workstack: WorkStack = WorkStack([(function, "") for function in functions])
    initial_proof_state = ProofState(workstack=initial_workstack)

    GLOBAL_OBSERVED_PROOFSTATES.add(initial_proof_state)
    GLOBAL_INCOMPLETE_PROOFSTATES.append(initial_proof_state)

    while GLOBAL_INCOMPLETE_PROOFSTATES:
        # MDE: I don't think we want a depth-first search here.  I think a breadth-first search
        # (achieved by making GLOBAL_PROOFSTATES a queue rather than a stack) is more appropriate,
        # to avoid getting stuck in an unproductive corner of the proof space.
        proof_state = GLOBAL_INCOMPLETE_PROOFSTATES.pop()
        next_proofstates = _step(
            proof_state=proof_state,
            specification_generator=specification_generator,
        )

        for next_proofstate in next_proofstates:
            if next_proofstate.is_workstack_empty():
                GLOBAL_COMPLETE_PROOFSTATES.append(next_proofstate)
            elif next_proofstate not in GLOBAL_OBSERVED_PROOFSTATES:
                GLOBAL_INCOMPLETE_PROOFSTATES.append(next_proofstate)
            else:
                logger.debug(f"Skipping duplicate ProofState {next_proofstate}")

    verified_specs: dict[CFunction, list[FunctionSpecification]] = defaultdict(list)
    for function in functions:
        for complete_proofstate in GLOBAL_COMPLETE_PROOFSTATES:
            if specs_for_function := complete_proofstate.get_specification(function=function):
                verified_specs[function].append(specs_for_function)
    return MappingProxyType(verified_specs)


def _step(
    proof_state: ProofState,
    specification_generator: LlmSpecificationGenerator,
) -> list[ProofState]:
    """Given a ProofState, returns of list of ProofStates, each of which makes a "step" of progress.

    A step of progress is one of:
    * verify the function at the top of the workstack and pop it off
    * assume the function at the top of the workstack and pop it off
    * backtrack: add a previously-completed function to the workstack, with the goal of obtaining a
      specification for it that is more useful to the function that is currently at the top of the
      workstack.

    This is the key unit of parallelism for the specification generation process. It effectively
    represents "branching points" in the tree of specifications; each node (i.e., specification)
    can serve as parent of n "new" specifications to explore.

    Args:
        proof_state (ProofState): The proof state from which to generate new proof states.
        specification_generator (LlmSpecificationGenerator): The specification generator.

    Returns:
        list[ProofState]: The list of new proof states to explore.

    """
    work_item = proof_state.peek_workstack()
    # Each SpecConversation represents an attempt at generating & verifying a spec for the function.
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
        next_proof_state = _get_next_proof_state(
            prev_proof_state=proof_state,
            function=work_item.function,
            spec_conversation=spec_conversation,
        )
        result.append(next_proof_state)
    return result


def _get_next_proof_state(
    prev_proof_state: ProofState, function: CFunction, spec_conversation: SpecConversation
) -> ProofState:
    """Return the next proof state, which is based on `spec_conversation`.

    A new proof state is a copy of the given proof state with two key differences:

        1. The new proof state's map of functions to specifications is updated with the given
           function and its specification from the SpecConversation.
        2. The new proof state's work stack may be smaller (if the function's spec verified
           successfully or is assumed), or larger (if the function failed to verify and the
           proof process will backtrack).

    Args:
        prev_proof_state (ProofState): The previous proof state.
        function (CFunction): The function for which specifications are being generated or repaired.
        spec_conversation (SpecConversation): The spec conversation.

    Returns:
        ProofState: The next proof state for the function, given the conversation.
    """
    # A deep copy is desirable here because the previous proof state should not be modified.
    next_proof_state = copy.deepcopy(prev_proof_state)
    next_proof_state.set_specification(function=function, spec=spec_conversation.specification)
    match spec_conversation.backtracking_strategy:
        case None | BacktrackingStrategy.ASSUME_SPEC:
            next_proof_state.pop_workstack()
        case s if s.is_regenerate_strategy:
            # MDE: If the strategy is repair, then shouldn't the workstack be popped then pushed,
            # rather than only pushed?
            next_proof_state.push_onto_workstack(
                function=function, hint=spec_conversation.get_latest_llm_response()
            )
    return next_proof_state


def _prune_specs(
    function: CFunction, spec_conversations: list[SpecConversation], proof_state: ProofState
) -> list[SpecConversation]:
    """Given a list of SpecConversations, returns a subset of them (which prunes the others).

    Note: The current strategy is simply to return just the specifications that successfully verify.

    Args:
        function (CFunction): The function whose SpecConversations to prune.
        spec_conversations (list[SpecConversation]): The SpecConversations to prune.
        proof_state (ProofState): The ProofState associated with this function and its list of
            SpecConversation.
            # MDE: Do we need to pass the function?  I think it's the one on the top of the
            # ProofState's workstack.

    Raises:
        ValueError: Raised when a SpecConversation does not have any file contents that were run
            under a verifier.

    Returns:
        list[SpecConversation]: A subset of the given SpecConversations.
    """
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
    return pruned_specs or spec_conversations


def _write_verified_spec(function: CFunction, specification: FunctionSpecification) -> None:
    """Write a function's verified specification to a file on disk.

    # MDE: Are assumed specifications also written to disk, or only proven ones?

    Verified specifications are written to a file under the `DEFAULT_RESULT_DIR` directory, in a
    file that has the same name (and path) as the original (non-specified) file.

    Args:
        function (CFunction): The function for which to write a verified specification to disk.
        specification (FunctionSpecification): The specification to write to disk.
    """
    path_to_original_file = Path(function.file_name)
    original_file_dir = str(path_to_original_file.parent).lstrip("/")
    result_file_dir = Path(DEFAULT_RESULT_DIR) / Path(original_file_dir)
    result_file = result_file_dir / path_to_original_file.name

    if not result_file.exists():
        # Create the result file by copying over the original file.
        # MDE: Either use a function like shutil.copy, or document why you do not.
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
