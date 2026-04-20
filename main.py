#!/usr/bin/env python3

"""Main entry point for specification generation and verification."""

import argparse
import pickle as pkl
import sys
import tempfile
from collections import deque
from collections.abc import Sequence
from pathlib import Path

from diskcache import Cache
from loguru import logger

from models import OPENAI_MODEL_TEMPERATURE_RANGE
from specifications import LlmSpecificationGenerator
from util import (
    AcceptVerifiedSpec,
    AssumeSpecAsIs,
    CFunction,
    CFunctionGraph,
    FunctionSpecification,
    SpecConversation,
    SpecGenGranularity,
    copy_file_to_folder,
    copy_folder_to_folder,
    ensure_lines_at_beginning,
    run_with_timeout,
)
from verification import (
    CbmcVerificationClient,
    ProofState,
    ProofStateStepper,
    VerificationClient,
    VerificationInput,
    VerificationResult,
    VerificationStatus,
)

VALID_LOG_LEVELS = ("DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL")

MODEL = "gpt-4o"
DEFAULT_HEADERS_FOR_VERIFICATION: Sequence[str] = (
    "#include <stdlib.h>",
    "#include <limits.h>",
)
DEFAULT_NUM_SPECIFICATION_CANDIDATES = 10
DEFAULT_NUM_REPAIR_CANDIDATES = 10
DEFAULT_MODEL_TEMPERATURE = 0.8
DEFAULT_NUM_SPECIFICATION_REPAIR_ITERATIONS = 2
# Default timeout of 5 minutes for specification generation and repair for an entire program.
DEFAULT_SPECIFICATION_GENERATION_TIMEOUT_SEC = 300
DEFAULT_SYSTEM_PROMPT = Path("prompts/system-prompt.txt").read_text(encoding="utf-8")
DEFAULT_RESULT_DIR = "specs"

# Directory to store the `cache.db` file containing the text responses from LLM.
DEFAULT_LLM_CACHE_DIR = "data/caching/llm"
# Directory to store the `cache.db` file for verification results.
DEFAULT_VERIFIER_RESULT_CACHE_DIR = "data/caching/verifier"

GLOBAL_OBSERVED_PROOFSTATES: set[ProofState] = set()
# Every ProofState in this queue is incomplete (i.e., their worklists are non-empty.)
GLOBAL_INCOMPLETE_PROOFSTATES: deque[ProofState] = deque()
# Every ProofState in this queue is complete (i.e., their worklists are empty.)
GLOBAL_COMPLETE_PROOFSTATES: list[ProofState] = []
# The keys for VERIFIER_CACHE are `VerificationInput` and the values are `VerificationResult`.
VERIFIER_CACHE: Cache | None = Cache(directory=DEFAULT_VERIFIER_RESULT_CACHE_DIR)

tempfile.tempdir = DEFAULT_RESULT_DIR


def main() -> None:
    """Generate specifications for a given C project using an LLM and verify them with CBMC."""
    parser = argparse.ArgumentParser(
        prog="main.py",
        description="Generate and verify CBMC specifications for a C project.",
    )
    parser.add_argument(
        "--input-path",
        required=True,
        help="The path to the C file, or the root directory of the C project for which to generate \
            specifications. If a directory is provided, it must contain compile_commands.json.",
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
        "--model-temperature",
        required=False,
        help=(
            "The temperature to use in invoking a model for specification generation and repair. "
            f"Defaults to {DEFAULT_MODEL_TEMPERATURE}."
        ),
        default=DEFAULT_MODEL_TEMPERATURE,
        type=OPENAI_MODEL_TEMPERATURE_RANGE.validate_temperature,
    )
    parser.add_argument(
        "--disable-llm-cache",
        action="store_true",
        help=("Always call the LLM, do not use cached answers (defaults to False)."),
    )
    parser.add_argument(
        "--disable-verifier-cache",
        action="store_true",
        help=(
            "Always re-run the verifier, do not use cached verifier results (defaults to False)."
        ),
    )
    parser.add_argument(
        "--fix-illegal-syntax",
        action="store_true",
        help=(
            "Apply syntax fixes to generated specification, e.g., "
            "illegal array range syntax, ellipses. (defaults to False)."
        ),
    )
    parser.add_argument(
        "--normalize-specs",
        action="store_true",
        help=(
            "Normalize generated specs, i.e., enforce consistent whitespaces and unique "
            "quantifier bounds. (defaults to False)."
        ),
    )
    parser.add_argument(
        "--specgen-granularity",
        required=False,
        default=SpecGenGranularity.CLAUSE.value,
        choices=[granularity.value for granularity in SpecGenGranularity],
        help=("The granularity at which specification generation occurs (defaults to clauses)."),
    )
    parser.add_argument(
        "--skip-functions-with-status",
        nargs="+",
        choices=[VerificationStatus.SUCCEEDED.value, VerificationStatus.ASSUMED.value],
        default=[],
        help=(
            "Do not add functions whose cached specifications match the given statuses to the"
            "workstack of functions. (defaults to not skipping any functions)"
        ),
    )
    parser.add_argument(
        "--path-to-llm-response-cache-dir",
        type=str,
        required=False,
        default=DEFAULT_LLM_CACHE_DIR,
        help=("Path to the directory that holds the cache.db file used for storing LLM responses."),
    )
    parser.add_argument(
        "--path-to-save-proofstates",
        type=str,
        required=False,
        help=("Path to the directory at which to save complete ProofStates."),
    )
    parser.add_argument(
        "--stub-out-llm",
        action="store_true",
        help=(
            "Stub out the LLM client (e.g., for integration tests). Otherwise, the constructor "
            "looks for an environment variable (LLM_API_KEY) that is not available on a CI runner."
        ),
    )
    parser.add_argument(
        "--log-level",
        required=False,
        default="INFO",
        choices=VALID_LOG_LEVELS,
        help="Set the logging verbosity level (defaults to INFO).",
    )
    args = parser.parse_args()

    logger.remove()
    logger.add(sys.stderr, level=args.log_level)

    input_path = Path(args.input_path).resolve()
    # Verify that it exists
    if not input_path.exists():
        msg = f"Input path '{input_path}' does not exist."
        raise FileNotFoundError(msg)

    if input_path.is_file():
        # This path is overwritten only when _write_spec_to_disk is called for a function in
        # the file, and that only happens when a spec for the function is verified or assumed.
        output_file_path = copy_file_to_folder(input_path, DEFAULT_RESULT_DIR)
        ensure_lines_at_beginning(DEFAULT_HEADERS_FOR_VERIFICATION, output_file_path)
        function_graph = CFunctionGraph(output_file_path)
    elif input_path.is_dir():  # input_path is a directory
        output_directory = copy_folder_to_folder(input_path, DEFAULT_RESULT_DIR)
        for c_file in output_directory.rglob("*.c"):
            ensure_lines_at_beginning(DEFAULT_HEADERS_FOR_VERIFICATION, c_file)
        function_graph = CFunctionGraph(output_directory)
    else:
        msg = f"Input path '{input_path}' is neither a file nor a directory."
        raise ValueError(msg)

    specgen_granularity = SpecGenGranularity(args.specgen_granularity)

    global VERIFIER_CACHE
    if args.disable_verifier_cache:
        VERIFIER_CACHE = None

    verifier: VerificationClient = CbmcVerificationClient(cache=VERIFIER_CACHE)
    specification_generator = LlmSpecificationGenerator(
        MODEL,
        temperature=args.model_temperature,
        system_prompt=DEFAULT_SYSTEM_PROMPT,
        verifier=verifier,
        num_specification_candidates=args.num_specification_candidates,
        num_specification_repair_candidates=args.num_repair_candidates,
        num_specification_repair_iterations=args.num_specification_repair_iterations,
        fix_illegal_syntax=args.fix_illegal_syntax,
        normalize_specs=args.normalize_specs,
        path_to_llm_response_cache_dir=args.path_to_llm_response_cache_dir,
        is_running_as_stub=args.stub_out_llm,
        disable_llm_cache=args.disable_llm_cache,
        specgen_granularity=specgen_granularity,
    )

    try:
        run_with_timeout(
            _verify_program,
            function_graph,
            specification_generator,
            {VerificationStatus(s) for s in args.skip_functions_with_status},
            args.path_to_save_proofstates,
            timeout_sec=args.specification_generation_timeout_sec,
        )
    except TimeoutError as te:
        logger.error(
            f"'_verify_program' timed out after {args.specification_generation_timeout_sec}",
            te,
        )
        sys.exit(0)


def _verify_program(
    function_graph: CFunctionGraph,
    specification_generator: LlmSpecificationGenerator,
    skip_statuses: set[VerificationStatus],
    path_to_save_proofstates: str | None,
) -> tuple[ProofState, ...]:
    """Return a set of ProofStates, each of which has a specification for each function.

    This function exits when GLOBAL_INCOMPLETE_PROOFSTATES is empty or when execution time
    exceeds the user-specified or defaulted specification generation timeout.

    Args:
        function_graph (CFunctionGraph): The graph representing the program to verify.
        specification_generator (LlmSpecificationGenerator): The LLM specification generator.
        skip_statuses (set[VerificationStatus]): Functions whose cached specifications have any of
            these statuses are not added to the workstack.
        path_to_save_proofstates (str | None): Path to where complete ProofStates should be written.

    Returns:
        tuple[ProofState, ...]: A set of ProofStates, each of which has specifications for each
            function.

    """
    # Since the initial list of functions is in reverse topological order,
    # the first element processed will be a leaf.
    functions = function_graph.get_functions_in_topological_order()
    if not functions:
        msg = f"'{function_graph.input_path}' did not have any functions to specify"
        logger.error(msg)
        sys.exit(1)

    if skip_statuses:
        functions_for_workstack: list[CFunction] = []
        existing_specs: dict[CFunction, FunctionSpecification] = {}
        for function in functions:
            if cached_vresult := _get_cached_vresult_with_status(function, skip_statuses):
                spec = cached_vresult.get_spec()
                function.set_specifications(spec)
                existing_specs[function] = spec
                logger.debug(
                    f"Setting {cached_vresult.status} cached specification for '{function.name}'"
                )
            else:
                functions_for_workstack.append(function)
    else:
        functions_for_workstack = functions
        existing_specs = {}

    if not functions_for_workstack:
        # There are specs in the cache for all the functions.
        # How should we re-construct ProofStates from the cache?
        sys.exit(0)

    # Construct the initial proof state from client code only; generate specs for external functions
    # lazily.
    client_functions = [f for f in functions_for_workstack if not f.is_external_function]
    if not client_functions:
        # This is extremely unlikely.
        logger.info(
            f"No client functions for which to generate specs in {function_graph.input_path}"
        )
        sys.exit(1)

    initial_proof_state = ProofState.from_functions(
        functions=client_functions, existing_specs=existing_specs
    )
    GLOBAL_OBSERVED_PROOFSTATES.add(initial_proof_state)
    # This is the global worklist.
    GLOBAL_INCOMPLETE_PROOFSTATES.append(initial_proof_state)

    proof_state_stepper = ProofStateStepper(
        result_dir=Path(DEFAULT_RESULT_DIR), cache=VERIFIER_CACHE
    )

    while GLOBAL_INCOMPLETE_PROOFSTATES:
        # Use BFS to avoid getting stuck in an unproductive search over a proof state.
        proof_state = GLOBAL_INCOMPLETE_PROOFSTATES.popleft()
        top_fn = proof_state.peek_workstack().function.name
        workstack_depth = proof_state.get_workstack().len()
        logger.info(f"Processing '{top_fn}' (workstack depth: {workstack_depth})")
        next_proofstates = _step(
            proof_state=proof_state,
            specification_generator=specification_generator,
            function_graph=function_graph,
            proof_state_stepper=proof_state_stepper,
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

    if proofstate_file_path := path_to_save_proofstates:
        output_path = Path(proofstate_file_path)
        if not output_path.exists():
            output_path.mkdir(parents=True, exist_ok=True)
        with Path(f"{proofstate_file_path}/proofstates.pkl").open("wb") as f:
            pkl.dump(GLOBAL_COMPLETE_PROOFSTATES, f, protocol=pkl.HIGHEST_PROTOCOL)

    return tuple(GLOBAL_COMPLETE_PROOFSTATES)


def _step(
    proof_state: ProofState,
    specification_generator: LlmSpecificationGenerator,
    function_graph: CFunctionGraph,
    proof_state_stepper: ProofStateStepper,
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
        function_graph (CFunctionGraph): The graph representing the program being verified.
        proof_state_stepper (ProofStateStepper): Computes the successor ProofState for each
            SpecConversation and writes accepted/assumed specs to disk.

    Returns:
        list[ProofState]: The list of new proof states to explore.

    """
    work_item = proof_state.peek_workstack()
    # Each SpecConversation represents a completed attempt at generating and verifying a spec for
    # the function.  That is, the next step focuses on a different function, even if it is possible
    # that the algorithm may revisit this function later due to backtracking.
    speccs_for_function: list[SpecConversation] = specification_generator.generate_and_repair_spec(
        function=work_item.function,
        function_graph=function_graph,
        hint=work_item.hint,
        proof_state=proof_state,
    )

    if work_item.assume_without_verification:
        for specc in speccs_for_function:
            specc.next_step = AssumeSpecAsIs()

    speccs_with_next_steps = [
        _set_next_step(
            spec_conversation=specc,
            proof_state=proof_state,
            specification_generator=specification_generator,
        )
        for specc in speccs_for_function
    ]

    result: list[ProofState] = [
        proof_state_stepper.get_next_proof_state(
            current_proof_state=proof_state,
            spec_conversation=specc,
            function_graph=function_graph,
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

    Returns:
        SpecConversation: The given SpecConversation with its `next_step` field set.
    """
    # Check whether the next step has already been set. This may occur when a failing specification
    # for a recursive function was previously encountered, in which case the spec is assumed and
    # repair is short-circuited.
    if spec_conversation.next_step:
        return spec_conversation

    vinput = VerificationInput(
        function=spec_conversation.function,
        spec=spec_conversation.specification,
        context=proof_state.get_current_context(function=spec_conversation.function),
        contents_of_file_to_verify=spec_conversation.contents_of_file_to_verify,
    )
    if VERIFIER_CACHE is not None:
        # Use the cache directly (not via verify()) to avoid extra log messages:
        # verify() logs on every call (including cache hits), but _set_next_step is called
        # after generate_and_repair_spec which already verified and cached these results.
        vresult = VERIFIER_CACHE.get(vinput)
    else:
        vresult = specification_generator.get_verification_client().verify(vinput)
    if vresult is not None:
        if vresult.succeeded:
            spec_conversation.next_step = AcceptVerifiedSpec()
            return spec_conversation
        # We currently determine a *single* next step. But, this might change in the future.
        next_steps = specification_generator.call_llm_for_next_steps(
            spec_conversation=spec_conversation, proof_state=proof_state
        )
        return next_steps[0]
    msg = f"Previously-verified spec '{spec_conversation}' was missing from the verifier cache"
    raise RuntimeError(msg)


def _get_cached_vresult_with_status(
    function: CFunction, statuses: set[VerificationStatus]
) -> VerificationResult | None:
    """Return a cached VerificationResult for a function whose status is in `statuses`.

    When multiple cached results match, the one with the highest priority status is returned
    (SUCCEEDED > ASSUMED > FAILED), regardless of cache iteration order.

    The lookup matches on function name, signature, and source filename only, so that a cached spec
    remains valid even if the file contents have changed (e.g., because other specs were written
    into it).

    Args:
        function (CFunction): The function whose cached specification is requested.
        statuses (set[VerificationStatus]): The set of statuses to match against.

    Returns:
        VerificationResult | None: The cached verification result for function if one with a
            matching status exists in the cache, otherwise None.
    """
    # Lower index = higher priority when multiple cached results match.
    vresult_priority: list[VerificationStatus] = [
        VerificationStatus.SUCCEEDED,
        VerificationStatus.ASSUMED,
    ]
    highest_priority_vresult: VerificationResult | None = None
    if VERIFIER_CACHE is not None:
        for vinput in VERIFIER_CACHE.iterkeys():
            # This is very inefficient, but still faster than adding all the functions to workstacks
            # and reading from the cache repeatedly.
            vresult = VERIFIER_CACHE[vinput]
            if vresult.status not in statuses or function != vresult.get_function():
                continue
            if highest_priority_vresult is None or (
                vresult_priority.index(vresult.status)
                < vresult_priority.index(highest_priority_vresult.status)
            ):
                highest_priority_vresult = vresult
    return highest_priority_vresult


if __name__ == "__main__":
    main()
