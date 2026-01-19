#!/opt/miniconda3/bin/python

"""Main entry point for specification generation and verification."""

import argparse
import shutil
import tempfile
import time
from collections import deque
from pathlib import Path
from typing import Any

from diskcache import Cache  # ty: ignore
from loguru import logger

from specifications import LlmSpecificationGenerator
from util import (
    CFunction,
    FunctionSpecification,
    ParsecFile,
    SpecConversation,
    SpecificationGenerationNextStep,
    copy_file_to_folder,
    ensure_lines_at_beginning,
    function_util,
    parse_object,
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
DEFAULT_NUM_REPAIR_CANDIDATES = 1
DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS = 3
DEFAULT_MODEL_TEMPERATURE = 1.0
# Default timeout of 5 minutes for specification generation and repair.
DEFAULT_SPECIFICATION_GENERATION_TIMEOUT_SEC = 300
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")
DEFAULT_VERIFIER_CACHE_DIR = "data/caching/verifier"
DEFAULT_RESULT_DIR = "specs"
DEFAULT_VERIFIER_RESULT_CACHE_DIR = "data/caching/verifier"

GLOBAL_OBSERVED_PROOFSTATES: set[ProofState] = set()
# Every ProofState in this queue is incomplete (i.e., their worklists are non-empty.)
GLOBAL_INCOMPLETE_PROOFSTATES: deque[ProofState] = deque()
# Every ProofState in this queue is complete (i.e., their worklists are empty.)
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
        help="The timeout for specification generation (in seconds, defaults to 5 minutes).",
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
    output_file_path = copy_file_to_folder(input_file_path, DEFAULT_RESULT_DIR)
    header_lines = [f"#include <{header}>" for header in DEFAULT_HEADERS_IN_OUTPUT]
    ensure_lines_at_beginning(header_lines, output_file_path)
    parsec_file = ParsecFile(input_file_path)
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
    """Return a set of ProofStates with specifications for each function.

    This function exits when GLOBAL_INCOMPLETE_PROOFSTATES is empty.

    Args:
        parsec_file (ParsecFile): The file to verify.
        specification_generator (LlmSpecificationGenerator): The specification generator.
        specgen_timeout_sec (float): The timeout for specification generation (in seconds).

    Returns:
        tuple[ProofState, ...]: A set of ProofStates with specifications for each function.

    """
    functions = parsec_file.get_functions_in_topological_order()

    initial_proof_state = ProofState.from_functions(functions=functions)
    GLOBAL_OBSERVED_PROOFSTATES.add(initial_proof_state)
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

    return tuple(complete_proofstate for complete_proofstate in GLOBAL_COMPLETE_PROOFSTATES)


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
    represents "branching points" in the search for a program specification; each node (i.e.,
    partial program specification) can serve as parent of multiple "new" specifications to explore.

    Args:
        proof_state (ProofState): The proof state from which to generate new proof states.
        specification_generator (LlmSpecificationGenerator): The specification generator.

    Returns:
        list[ProofState]: The list of new proof states to explore.

    """
    work_item = proof_state.peek_workstack()
    # Each SpecConversation represents a completed attempt at generating and verifying a spec for
    # the function.  That is, the next step focuses on a different function, even if it is possible
    # that the algorithm may revisit this function later due to backtracking.
    spec_conversations_for_function: list[SpecConversation] = (
        specification_generator.generate_and_repair_spec(
            function=work_item.function,
            hint=work_item.hint,
            proof_state=proof_state,
        )
    )

    pruned_spec_conversations_for_function = _prune_specs(
        proof_state=proof_state,
        spec_conversations=spec_conversations_for_function,
    )

    result: list[ProofState] = []

    for spec_conversation in pruned_spec_conversations_for_function:
        next_proof_state = _get_next_proof_state(
            prev_proof_state=proof_state,
            spec_conversation=spec_conversation,
        )
        result.append(next_proof_state)
    return result


def _get_next_proof_state(
    prev_proof_state: ProofState, spec_conversation: SpecConversation
) -> ProofState:
    """Return the next proof state, which is based on `spec_conversation`.

    A new proof state is a copy of the given proof state with two key differences:

        1. The new proof state's map of functions to specifications is updated with the given
           function and its specification from the SpecConversation.
        2. The new proof state's work stack is either smaller (if the function's spec verified
           successfully or is assumed) or larger (if the function failed to verify and the
           proof process will backtrack).

    Args:
        prev_proof_state (ProofState): The previous proof state.
        spec_conversation (SpecConversation): The spec conversation comprising the function and the
            specification under verification.

    Returns:
        ProofState: The next proof state for the function, given the conversation.
    """
    # MDE: The two calls to `set_specification` and `set_workstack` make two copies of the
    # proofstate, and the proofstate is not used in between.  For efficiency -- and for clarity
    # regarding which data structures are actually needed -- please remove the two functions and
    # replace them by one ProofState constructor function that takes three arguments (the function,
    # the specification, and the workstack).
    specs_for_next_proof_state = prev_proof_state.get_specifications() | {
        spec_conversation.function: spec_conversation.specification
    }
    workstack_for_next_proof_state = prev_proof_state.get_workstack()
    match spec_conversation.specgen_next_step:
        case None:
            msg = f"{spec_conversation} was missing a next step"
            raise ValueError(msg)
        case (
            SpecificationGenerationNextStep.ACCEPT_VERIFIED_SPEC
            | SpecificationGenerationNextStep.ASSUME_SPEC_AS_IS
        ):
            workstack_for_next_proof_state = workstack_for_next_proof_state.pop()
        case s if s.is_regenerate_strategy:
            work_item = WorkItem(
                function=spec_conversation.function,
                # MDE: I had assumed there would only be a hint when backtracking.  (Or, maybe that
                # is actually true?  If so, I suggest explicitly splitting `case s if
                # s.is_regenerate_strategy:` into two `SpecificationGenerationNextStep` items,
                # because there is no need to pop the workstack and then to push an equal (but not
                # identical) WorkItem onto it.  Doing so is confusing to the reader and is also
                # inefficient both in terms of memory used and in cost of equality checks.) When not
                # backtracking, all the information that the LLM needs is in the conversation. The
                # point of the hint is that a WorkItem does not carry a SpecConversation, so the
                # only way to pass information from previous LLM invocations is via the hint.
                hint=_parse_reasoning(spec_conversation.get_latest_llm_response()) or "",
            )
            workstack_for_next_proof_state = workstack_for_next_proof_state.pop().push(
                work_item=work_item
            )
    return ProofState(specs=specs_for_next_proof_state, workstack=workstack_for_next_proof_state)


def _parse_reasoning(llm_response: str) -> str | None:
    """Return the value mapped to the "reasoning" key in an LLM response.

    Args:
        llm_response (str): The LLM response.

    Returns:
        str | None: The value mapped to the "reasoning" key in an LLM response.
    """
    parsed_llm_response: dict[str, Any] = parse_object(text=llm_response)
    return str(parsed_llm_response.get("reasoning"))


def _prune_specs(
    proof_state: ProofState,
    spec_conversations: list[SpecConversation],
) -> list[SpecConversation]:
    """Given a list of SpecConversations, returns a subset of them (which prunes the others).

    Note: The current strategy is simply to return just the specifications that successfully verify.

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
        function = spec_conversation.function
        contents_of_verified_file = spec_conversation.contents_of_file_to_verify
        if contents_of_verified_file is None:
            msg = f"{spec_conversation} was missing file contents that were run under verification"
            raise ValueError(msg)
        vcontext = proof_state.get_current_context(function=function)
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
    return pruned_specs or spec_conversations


def _write_verified_or_assumed_spec(
    function: CFunction, specification: FunctionSpecification
) -> None:
    """Write a function's verified or assumed specification to a file on disk.

    This function should be called to update the files which will be the end-result of verification,
    not the temporary files used in iteratively verifying candidate specifications.

    The contents of the file that is being written to are identical to the corresponding file in the
    unverified (input) program, but some functions may be specified (i.e., have CBMC annotations)
    as specification generation progresses.

    Specifications are written to a file under the `DEFAULT_RESULT_DIR` directory that has the same
    same name (and path) as the original (non-specified) file.

    Args:
        function (CFunction): The function for which to write a verified specification to disk.
        specification (FunctionSpecification): The specification to write to disk.

    """
    # Examples of original and result file names:
    # * "my_research/myfile.c" => "specs/my_research/myfile.c"
    # * "/home/jquser/my_research/myfile.c" => "specs/home/jquser/my_research/myfile.c"
    path_to_original_file = Path(function.file_name)
    original_file_dir = str(path_to_original_file.parent).lstrip("/")
    result_file_dir = Path(DEFAULT_RESULT_DIR) / Path(original_file_dir)
    result_file = result_file_dir / path_to_original_file.name

    if not result_file.exists():
        # Create the result file by copying over the original file.
        result_file.parent.mkdir(exist_ok=True, parents=True)
        shutil.copy(path_to_original_file, result_file)

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
