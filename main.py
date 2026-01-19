#!/opt/miniconda3/bin/python

"""Main entry point for specification generation and verification."""

import argparse
import os
import shutil
import tempfile
import time
from collections import deque
from pathlib import Path

from diskcache import Cache  # ty: ignore
from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    AcceptVerifiedSpec,
    AssumeSpecAsIs,
    BacktrackToCallee,
    CFunction,
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
    VerificationInput,
    WorkItem,
)

MODEL = "gpt-4o"
DEFAULT_HEADERS_IN_OUTPUT = ["#include <stdlib.h>", "#include <limits.h>"]
DEFAULT_NUM_SPECIFICATION_CANDIDATES = 10
DEFAULT_NUM_REPAIR_CANDIDATES = 10
DEFAULT_MODEL_TEMPERATURE = 1.0
DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS = 2
# Default timeout of 5 minutes for specification generation and repair for an entire program.
DEFAULT_SPECIFICATION_GENERATION_TIMEOUT_SEC = 300
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")
DEFAULT_RESULT_DIR = "specs"
DEFAULT_VERIFIER_RESULT_CACHE_DIR = "data/caching/verifier"

GLOBAL_OBSERVED_PROOFSTATES: set[ProofState] = set()
# Every ProofState in this queue is incomplete (i.e., their worklists are non-empty.)
GLOBAL_INCOMPLETE_PROOFSTATES: deque[ProofState] = deque()
# Every ProofState in this queue is complete (i.e., their worklists are empty.)
GLOBAL_COMPLETE_PROOFSTATES: list[ProofState] = []
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
        "file",
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
        help=(
            "The timeout for specification generation for a given program in seconds, "
            "defaults to 5 minutes"
        ),
        default=DEFAULT_SPECIFICATION_GENERATION_TIMEOUT_SEC,
        type=float,
    )
    parser.add_argument(
        "--disable-llm-cache",
        action="store_true",
        help=("Always call the LLM, do not use cached answers (defaults to False)."),
    )
    args = parser.parse_args()

    input_file_path = Path(args.file)
    parsec_file = ParsecFile(input_file_path)

    # MDE: Will this path be repeatedly overwritten during the verification process?  If so, that is
    # a serious problem for concurrency.
    output_file_path = copy_file_to_folder(input_file_path, DEFAULT_RESULT_DIR)
    ensure_lines_at_beginning(DEFAULT_HEADERS_IN_OUTPUT, output_file_path)

    verifier: VerificationClient = CbmcVerificationClient(cache=VERIFIER_CACHE)
    specification_generator = LlmSpecificationGenerator(
        MODEL,
        system_prompt=DEFAULT_SYSTEM_PROMPT,
        verifier=verifier,
        num_specification_candidates=args.num_specification_candidates,
        num_specification_repair_candidates=args.num_repair_candidates,
        num_specification_repair_iterations=args.num_specification_repair_iterations,
        disable_llm_cache=args.disable_llm_cache,
    )

    _verify_program(
        parsec_file=parsec_file,
        specification_generator=specification_generator,
        specgen_timeout_sec=args.specification_generation_timeout_sec,
    )


def _verify_program(
    parsec_file: ParsecFile,
    specification_generator: LlmSpecificationGenerator,
    specgen_timeout_sec: float,
) -> tuple[ProofState, ...]:
    """Return a set of ProofStates, each of which has a specification for each function.

    This function exits when GLOBAL_INCOMPLETE_PROOFSTATES is empty or when execution time
    exceeds the user-specified or defaulted specification generation timeout.

    Args:
        parsec_file (ParsecFile): The file to verify.
        specification_generator (LlmSpecificationGenerator): The LLM specification generator.
        specgen_timeout_sec (float): The timeout for specification generation (in seconds).

    Returns:
        tuple[ProofState, ...]: A set of ProofStates, each of which has specifications for each
            function.

    """
    functions = parsec_file.get_functions_in_topological_order(reverse_order=True)

    # Since `functions` is in reverse topological order,
    # the first element processed will be a leaf.
    initial_proof_state = ProofState.from_functions(functions=functions[::-1])
    GLOBAL_OBSERVED_PROOFSTATES.add(initial_proof_state)
    # This is the global worklist.
    GLOBAL_INCOMPLETE_PROOFSTATES.append(initial_proof_state)

    specgen_timeout_limit = time.time() + specgen_timeout_sec

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

    Let `top_fn` is the function ot the top of the workstack.

    A step of progress is one of:
    * Generate a verifiable spec for `top_fn` and pop the workstack.
    * Generate an assumed spec for `top_fn` and pop the workstack.
    * Backtrack: add a previously-completed function to the workstack, with the goal of obtaining a
      specification for it that is more useful to `top_fn`.

    The next step will focus on a different function than `top_fn`, even if it is possible that the
    algorithm may revisit `top_fn` later due to backtracking.

    Args:
        proof_state (ProofState): The proof state from which to generate new proof states.
        specification_generator (LlmSpecificationGenerator): The specification generator.

    Returns:
        list[ProofState]: The list of new proof states to explore.

    """
    work_item = proof_state.peek_workstack()
    # Each SpecConversation represents a completed attempt at generating and verifying
    # a spec for the function.
    speccs_for_function: list[SpecConversation] = specification_generator.generate_and_repair_spec(
        function=work_item.function,
        hint=work_item.hint,
        proof_state=proof_state,
    )

    speccs_with_next_steps = [
        _set_next_step(
            spec_conversation=specc,
            proof_state=proof_state,
            specification_generator=specification_generator,
        )
        for specc in speccs_for_function
    ]

    result: list[ProofState] = [
        _get_next_proof_state(
            prev_proof_state=proof_state,
            spec_conversation=specc,
        )
        for specc in speccs_with_next_steps
    ]
    return result


def _set_next_step(
    spec_conversation: SpecConversation,
    proof_state: ProofState,
    specification_generator: LlmSpecificationGenerator,
) -> SpecConversation:
    """Return the given SpecConversation with its `next_step` field set.

    Args:
        spec_conversation (SpecConversation): The SpecConversation whose next `step_field` to set.
        proof_state (ProofState): The ProofState.
        specification_generator (LlmSpecificationGenerator): The specification generator.

    Raises:
        RuntimeError: Raised when a previously-verified spec is missing from the verifier cache.

    Returns:
        SpecConversation: The given SpecConversation with its `next_step` field set.
    """
    vinput = VerificationInput(
        function=spec_conversation.function,
        spec=spec_conversation.specification,
        context=proof_state.get_current_context(function=spec_conversation.function),
        contents_of_file_to_verify=spec_conversation.contents_of_file_to_verify,
    )
    if vresult := VERIFIER_CACHE.get(vinput):
        if vresult.succeeded:
            spec_conversation.next_step = AcceptVerifiedSpec()
            return spec_conversation
        return specification_generator.call_llm_for_backtracking_strategy(
            spec_conversation=spec_conversation, proof_state=proof_state
        )
    msg = f"Previously-verified spec '{spec_conversation}' was missing from the verifier cache"
    raise RuntimeError(msg)


def _get_next_proof_state(
    prev_proof_state: ProofState, spec_conversation: SpecConversation
) -> ProofState:
    """Return the next proof state by modifying `prev_proof_state` based on `spec_conversation`.

        The new proof state is a copy of the given proof state with two differences:

            1. The new proof state's map of functions to specifications is updated with the given
               function and its specification from the SpecConversation.
            2. The new proof state's work stack is either smaller (if the function's spec verified
               successfully or is assumed) or larger (if the function failed to verify and the
               proof process will backtrack).

    Args:
        prev_proof_state (ProofState): The previous proof state.
        spec_conversation (SpecConversation): The spec conversation in which an LLM generated a
            specification for the function on the top of the workstack of `prev_proof_state`.

    Returns:
        ProofState: The next proof state for the program, given the conversation.
    """
    specs_for_next_proof_state = prev_proof_state.get_specifications() | {
        spec_conversation.function: spec_conversation.specification
    }
    match spec_conversation.next_step:
        case None:
            msg = f"{spec_conversation} was missing a next step"
            raise ValueError(msg)
        case AcceptVerifiedSpec() | AssumeSpecAsIs():
            # There could be more than one valid specification generated (i.e., when we sample more
            # than once from the LLM). For now, we take the last (valid) specification and write it.
            _write_spec_to_disk(spec_conversation=spec_conversation)
            workstack_for_next_proof_state = prev_proof_state.get_workstack().pop()
            return ProofState(
                specs=specs_for_next_proof_state, workstack=workstack_for_next_proof_state
            )
        case BacktrackToCallee(callee, hint):
            # TODO: Fetching the callee from the same file in which the function under spec. gen.
            # is defined is a brittle assumption that should be fixed with multi-file ParseC
            # support.
            result_file = _get_result_file(function=spec_conversation.function)
            callee = ParsecFile(result_file).get_function_or_none(function_name=callee)
            if not callee:
                msg = (
                    f"'{result_file}' was missing a definition for callee: "
                    f"'{callee}' during backtracking"
                )
                raise ValueError(msg)
            work_item_for_callee = WorkItem(function=callee, hint=hint)
            workstack_for_next_proof_state = prev_proof_state.get_workstack().push(
                work_item_for_callee
            )
            return ProofState(
                specs=specs_for_next_proof_state,
                workstack=workstack_for_next_proof_state,
            )
        case _:
            msg = f"Unexpected next step strategy: '{SpecConversation.next_step}'"
            raise ValueError(msg)


def _write_spec_to_disk(spec_conversation: SpecConversation) -> None:
    """Write a function specification to a file on disk.

    This function iteratively builds up the final output of verification, which is the set of
    input files that are specified with CBMC annotations. The contents of the file that is being
    written to are identical to the corresponding file in the unverified (input) program, but some
    functions may be specified (i.e., have CBMC annotations) as specification generation runs for

    Specifications are written to a file under the `DEFAULT_RESULT_DIR` directory that has the same
    same name (and path) as the original (non-specified) file under a directory that is specific to
    each process (i.e., the directory's name is the pid of the process where specification
    generation is running).

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
    # * "my_research/myfile.c" => "specs/<PID>/my_research/myfile.c"
    # * "/home/jquser/my_research/myfile.c" => "specs/<PID>/home/jquser/my_research/myfile.c"
    path_to_original_file = Path(function.file_name)
    original_file_dir = str(path_to_original_file.parent).lstrip("/")
    pid_dir = Path(str(os.getpid()))
    result_file_dir = Path(DEFAULT_RESULT_DIR) / pid_dir / Path(original_file_dir)
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
