#!/opt/miniconda3/bin/python

"""Main entry point for specification generation and verification."""

import argparse
import shutil
import tempfile
import time
from collections import deque
from pathlib import Path

from diskcache import Cache  # ty: ignore
from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    CFunction,
    ParsecFile,
    SpecConversation,
    SpecificationGenerationNextStep,
    copy_file_to_folder,
    ensure_lines_at_beginning,
    function_util,
    parse_backtracking_info,
)
from verification import (
    CbmcVerificationClient,
    ProofState,
    VerificationClient,
    VerificationInput,
    WorkItem,
)

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["stdlib.h", "limits.h"]
DEFAULT_NUM_SPECIFICATION_CANDIDATES = 10
DEFAULT_NUM_REPAIR_CANDIDATES = 1  # MDE: This seems too low to me.
DEFAULT_MODEL_TEMPERATURE = 1.0  # MDE: This is incompatible
# with "DEFAULT_NUM_SPECIFICATION_CANDIDATES = 10"
DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS = 3  # MDE: This might be too high.
# MDE: Is this a timeout per function, per file, or per program?
# Default timeout of 5 minutes for specification generation and repair.
DEFAULT_SPECIFICATION_GENERATION_TIMEOUT_SEC = 300
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")
DEFAULT_VERIFIER_CACHE_DIR = "data/caching/verifier"
DEFAULT_RESULT_DIR = "specs"
# MDE: What is the destinction from DEFAULT_VERIFIER_CACHE_DIR which has the same value?
DEFAULT_VERIFIER_RESULT_CACHE_DIR = "data/caching/verifier"

GLOBAL_OBSERVED_PROOFSTATES: set[ProofState] = set()
# Every ProofState in this queue is incomplete (i.e., their worklists are non-empty.)
GLOBAL_INCOMPLETE_PROOFSTATES: deque[ProofState] = deque()
# Every ProofState in this queue is complete (i.e., their worklists are empty.)
# MDE: Why is this a deque rather than a list?  I don't think it is ever removed from.
GLOBAL_COMPLETE_PROOFSTATES: deque[ProofState] = deque()
# The keys for VERIFIER_CACHE are `VerificationInput` and the values are `VerificationResult`.
VERIFIER_CACHE: Cache = Cache(directory=DEFAULT_VERIFIER_RESULT_CACHE_DIR)

tempfile.tempdir = DEFAULT_RESULT_DIR


def main() -> None:
    """Generate specifications for a given C file using an LLM and verify them with CBMC.

    The current implementation operates over all the C functions in one file.
    """
    parser = argparse.ArgumentParser(
        prog="main.py", description="Generate and verify CBMC specifications for a C file."
    )
    parser.add_argument(
        # MDE: I don't feel "--file" is informative.  It doesn't indicate whether the file is used
        # for input or output (that omission somewhat implies both) or what is in the file.  I
        # suggest that the file names be passed directly on the command line, as a non-flag
        # argument.
        "--file",
        required=True,
        help="The C file for which to generate and verify specifications.",
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
        help="The LLM generates this many repaired specifications for each unverifiable spec.",
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
        "--specification-generation-timeout-sec",
        required=False,
        # MDE: Is this per function or per program?
        help="The timeout for specification generation (in seconds, defaults to 5 minutes).",
        default=DEFAULT_SPECIFICATION_GENERATION_TIMEOUT_SEC,
        type=float,
    )
    parser.add_argument(
        "--disable-llm-sample-cache",
        action="store_true",
        help=("Always call the LLM, do not use cached answers (defaults to False)."),
    )
    args = parser.parse_args()

    input_file_path = Path(args.file)
    parsec_file = ParsecFile(input_file_path)

    # MDE: Will this path be repeatedly overwritten during the verification process?  If so, that is
    # a serious problem for concurrency.
    output_file_path = copy_file_to_folder(input_file_path, DEFAULT_RESULT_DIR)
    header_lines = [f"#include <{header}>" for header in DEFAULT_HEADERS_IN_OUTPUT]
    ensure_lines_at_beginning(header_lines, output_file_path)

    verifier: VerificationClient = CbmcVerificationClient(cache=VERIFIER_CACHE)
    specification_generator = LlmSpecificationGenerator(
        MODEL,
        system_prompt=DEFAULT_SYSTEM_PROMPT,
        verifier=verifier,
        parsec_file=parsec_file,
        num_specification_candidates=args.num_specification_candidates,
        num_specification_repair_candidates=args.num_repair_candidates,
        num_specification_repair_iterations=args.num_specification_repair_iterations,
        disable_cache=args.disable_llm_sample_cache,
    )

    functions_in_reverse_topological_order = parsec_file.get_functions_in_topological_order(
        reverse_order=True
    )
    _verify_program(
        functions=functions_in_reverse_topological_order,
        specification_generator=specification_generator,
        specgen_timeout_sec=args.specification_generation_timeout_sec,
    )


def _verify_program(
    functions: list[CFunction],
    specification_generator: LlmSpecificationGenerator,
    specgen_timeout_sec: float,
) -> tuple[ProofState, ...]:
    """Return a set of ProofStates, each of which has a specification for each function.

    This function exits when GLOBAL_INCOMPLETE_PROOFSTATES is empty.
    # MDE: or timeout?

    Args:
        functions (list[CFunction]): The functions for which to generate and verify specifications,
            in reverse topological order.
        specification_generator (LlmSpecificationGenerator): The LLM specification generator.
        specgen_timeout_sec (float): The timeout for specification generation (in seconds).

    Returns:
        tuple[ProofState, ...]: A set of ProofStates with specifications for each function.

    """
    initial_proof_state = ProofState.from_functions(functions=functions[::-1])
    GLOBAL_OBSERVED_PROOFSTATES.add(initial_proof_state)
    # This is the global worklist.
    GLOBAL_INCOMPLETE_PROOFSTATES.append(initial_proof_state)

    specgen_timeout_limit = time.time() + specgen_timeout_sec

    # Since `functions` is in reverse topological order,
    # the first element popped from the stack will be a leaf.
    while GLOBAL_INCOMPLETE_PROOFSTATES and not _is_timeout_reached(specgen_timeout_limit):
        # Use BFS to avoid getting stuck in an unproductive search over a proof state.
        proof_state = GLOBAL_INCOMPLETE_PROOFSTATES.popleft()
        next_proofstates = _step(
            proof_state=proof_state,
            specification_generator=specification_generator,
        )

        for next_proofstate in next_proofstates:
            if next_proofstate in GLOBAL_OBSERVED_PROOFSTATES:
                # Avoid re-processing proof states we've already seen.
                logger.debug(f"Skipping duplicate ProofState {next_proofstate}")
                continue
            GLOBAL_OBSERVED_PROOFSTATES.add(next_proofstate)

            if next_proofstate.is_workstack_empty():
                GLOBAL_COMPLETE_PROOFSTATES.append(next_proofstate)
            else:
                GLOBAL_INCOMPLETE_PROOFSTATES.append(next_proofstate)

    return tuple(GLOBAL_COMPLETE_PROOFSTATES)


def _step(
    proof_state: ProofState,
    specification_generator: LlmSpecificationGenerator,
) -> list[ProofState]:
    """Given a ProofState, returns of list of ProofStates, each of which makes a "step" of progress.

    A step of progress is one of (where `top_fn` is the function ot the top of the workstack):
    * Generate a verifiable spec for `top_fn` and pop the workstack.
    * Generate an assumed spec for `top_fn` and pop the workstack.
    * Backtrack: add a previously-completed function to the workstack, with the goal of obtaining a
      specification for it that is more useful to `top_fn`.

    The next step focuses on a different function, even if it is possible that the algorithm may
    revisit this function later due to backtracking.

    Args:
        proof_state (ProofState): The proof state from which to generate new proof states.
        specification_generator (LlmSpecificationGenerator): The specification generator.

    Returns:
        list[ProofState]: The list of new proof states to explore.

    """
    work_item = proof_state.peek_workstack()
    # Each SpecConversation in this list represents a completed attempt at generating and verifying
    # a spec for the function.
    spec_conversations_for_function: list[SpecConversation] = (
        specification_generator.generate_and_repair_spec(
            function=work_item.function,
            hint=work_item.hint,
            proof_state=proof_state,
        )
    )

    pruned_spec_conversations_for_function = _prune_specs_heuristically(
        proof_state=proof_state,
        spec_conversations=spec_conversations_for_function,
    )

    # MDE: `_call_llm_for_backtracking_strategy` can be called here in this function or can be
    # called in `_get_next_proof_state()`, rather than hiding it within
    # `generate_and_repair_spec()`.

    result: list[ProofState] = [
        _get_next_proof_state(
            prev_proof_state=proof_state,
            spec_conversation=spec_conversation,
        )
        for spec_conversation in pruned_spec_conversations_for_function
    ]
    return result


def _get_next_proof_state(
    prev_proof_state: ProofState, spec_conversation: SpecConversation
) -> ProofState:
    """Return the next proof state, which modifies `prev_proof_state` based on `spec_conversation`.

        The new proof state is a copy of the given proof state with two differences:

            1. The new proof state's map of functions to specifications is updated with the given
               function and its specification from the SpecConversation.
            2. The new proof state's work stack is either smaller (if the function's spec verified
               successfully or is assumed) or larger (if the function failed to verify and the
               proof process will backtrack).

    Args:
        prev_proof_state (ProofState): The previous proof state.
        spec_conversation (SpecConversation): The spec conversation in which an LLM generated a
            specification for the function on the teop of the workstack of `prev_proof_state`.

    Returns:
        ProofState: The next proof state for the program, given the conversation.
    """
    specs_for_next_proof_state = prev_proof_state.get_specifications() | {
        spec_conversation.function: spec_conversation.specification
    }
    # MDE: `specgen_next_step` is not the same field name as used in the algorithm description.
    match spec_conversation.specgen_next_step:
        case None:
            msg = f"{spec_conversation} was missing a next step"
            raise ValueError(msg)
        case (
            SpecificationGenerationNextStep.ACCEPT_VERIFIED_SPEC
            | SpecificationGenerationNextStep.ASSUME_SPEC_AS_IS
        ):
            # There could be more than one valid specification generated (i.e., when we sample more
            # than once from the LLM). For now, we take the last (valid) specification and write it.
            _write_spec_to_disk(spec_conversation=spec_conversation)
            workstack_for_next_proof_state = prev_proof_state.get_workstack().pop()
            return ProofState(
                specs=specs_for_next_proof_state, workstack=workstack_for_next_proof_state
            )
        case SpecificationGenerationNextStep.BACKTRACK_TO_CALLEE:
            backtracking_info = parse_backtracking_info(
                llm_response=spec_conversation.get_latest_llm_response(),
            )
            # TODO: Fetching the callee from the same file in which the function under spec. gen.
            # is defined is a brittle assumption that should be fixed with multi-file ParseC
            # support.
            result_file = _get_result_file(function=spec_conversation.function)
            callee = ParsecFile(result_file).get_function_or_none(
                function_name=backtracking_info.callee_name
            )
            if not callee:
                msg = (
                    f"'{result_file}' was missing a definition for callee: "
                    f"'{backtracking_info.callee_name}' during backtracking"
                )
                raise ValueError(msg)
            work_item_for_callee = WorkItem(
                function=callee,
                hint=backtracking_info.postcondition_strengthening_description,
            )
            workstack_for_next_proof_state = prev_proof_state.get_workstack().push(
                work_item_for_callee
            )
            return ProofState(
                specs=specs_for_next_proof_state,
                workstack=workstack_for_next_proof_state,
            )
        case _:
            msg = f"Unexpected next step strategy: '{SpecConversation.specgen_next_step}'"
            raise ValueError(msg)


def _prune_specs_heuristically(
    proof_state: ProofState,
    spec_conversations: list[SpecConversation],
) -> list[SpecConversation]:
    """Given a list of SpecConversations, returns a subset of them (which prunes the others).

    Note: The current strategy is:
    If any specification verifies, return all the specifications that verify.
    Otherwise, return all the input specifications.

    Args:
        proof_state (ProofState): The ProofState. The topmost function on its workstack is the
            function for which specifications are being generated/repaired.
        spec_conversations (list[SpecConversation]): The SpecConversations to prune.

    Raises:
        ValueError: Raised when a SpecConversation does not have any file contents that were run
            under a verifier.

    Returns:
        list[SpecConversation]: A subset of the given SpecConversations.
    """
    pruned_specs = []
    for spec_conversation in spec_conversations:
        # MDE: abstract out the creation of a VerificationInput (everything through the blank line)
        # into its own function.
        function = spec_conversation.function
        vcontext = proof_state.get_current_context(function=function)
        contents_of_verified_file = spec_conversation.contents_of_file_to_verify
        if contents_of_verified_file is None:
            msg = f"{spec_conversation} was missing file contents that were run under verification"
            raise ValueError(msg)
        vinput = VerificationInput(
            function=function,
            spec=spec_conversation.specification,
            context=vcontext,
            contents_of_file_to_verify=contents_of_verified_file,
        )

        if vresult := VERIFIER_CACHE.get(vinput):
            if vresult.succeeded:
                pruned_specs.append(spec_conversation)
        else:
            msg = f"Cache miss for previously-executed vinput: {vinput}"
            raise RuntimeError(msg)
    # MDE: Maybe this is the only place that the `next_step` field is needed.  If so, I suggest that
    # the return tye of the function is a list of (boolean, SpecConversation) pairs, where the
    # boolean indicates whether verification succeeded.  I think that is clearer and cleaner than
    # permanently putting information in the SpecConversation that is only transiently useful.
    return pruned_specs or spec_conversations


def _write_spec_to_disk(spec_conversation: SpecConversation) -> None:
    """Write a function specification to a file on disk.

    # MDE: What is the reason for this stricture?  Because this function hard-codes the file name?
    This function should be called to update the files which will be the end-result of verification,
    not the temporary files used in iteratively verifying candidate specifications.

    The contents of the file that is being written to are identical to the corresponding file in the
    unverified (input) program, but some functions may be specified (i.e., have CBMC annotations)
    as specification generation progresses.
    # MDE: "as specification generation progresses" is in conflict with "the end-result of
    # verification".  Please clarify.  Is one of them about function verification and the other
    # about program verification, or is one of the comments just wrong?

    # MDE: This is very bad for parallelism.  Two parallel processes might both find different
    # successful specs at the same time.
    Specifications are written to a file under the `DEFAULT_RESULT_DIR` directory that has the same
    same name (and path) as the original (non-specified) file.

    Args:
        spec_conversation (SpecConversation): The SpecConversation comprising the specification that
            should be written to the result file.

    """
    function = spec_conversation.function
    path_to_original_file = Path(function.file_name)
    result_file = _get_result_file(function=function)

    if not result_file.exists():
        # Create the result file by copying over the original file.
        result_file.parent.mkdir(exist_ok=True, parents=True)
        shutil.copy(path_to_original_file, result_file)

    parsec_file = ParsecFile(result_file)
    function_with_verified_spec = function_util.get_source_code_with_inserted_spec(
        function_name=function.name,
        specification=spec_conversation.specification,
        parsec_file=parsec_file,
        comment_out_spec=True,
    )

    function_util.update_function_declaration(
        function_name=function.name,
        updated_function_content=function_with_verified_spec,
        parsec_file=parsec_file,
        file=result_file,
    )


def _get_result_file(function: CFunction) -> Path:
    """Return the name of the result file for a function.

    The "result file" is where the verified or assumed specification for a function is written.

    Args:
        function (CFunction): The function for which to obtain the result file.

    Returns:
        Path: The result file.
    """
    # Examples of original and result file names:
    # * "my_research/myfile.c" => "specs/my_research/myfile.c"
    # * "/home/jquser/my_research/myfile.c" => "specs/home/jquser/my_research/myfile.c"
    path_to_original_file = Path(function.file_name)
    original_file_dir = str(path_to_original_file.parent).lstrip("/")
    result_file_dir = Path(DEFAULT_RESULT_DIR) / Path(original_file_dir)
    return result_file_dir / path_to_original_file.name


def _is_timeout_reached(timeout_limit_sec: float) -> bool:
    """Return True iff the timeout limit has been reached (or exceeded).

    Args:
        timeout_limit_sec (float): The timeout limit (in seconds).

    Returns:
        bool: True iff the timeout limit has been reached (or exceeded).
    """
    return time.time() >= timeout_limit_sec


if __name__ == "__main__":
    main()
