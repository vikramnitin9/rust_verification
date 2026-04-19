"""Class for creating new ProofState(s) based on a SpecConversation."""

import os
import shutil
from pathlib import Path

from diskcache import Cache
from loguru import logger

from util import (
    AcceptVerifiedSpec,
    AssumeSpecAsIs,
    BacktrackToCallee,
    CFunction,
    CFunctionGraph,
    SpecConversation,
    function_util,
)
from util.function_specification import FunctionSpecification
from verification.verification_input import VerificationInput

from .proof_state import ProofState, WorkItem
from .verification_result import VerificationResult, VerificationStatus


class ProofStateStepper:
    """Class for creating new proof state(s) based on a SpecConversation and a previous proof state.

    Attributes:
        _result_dir (Path): The root directory under which verified/assumed specs are written.
        _cache (Cache | None): The verifier cache. When set, the status of assumed specs is updated
            to `VerificationStatus.ASSUMED` in the cache.
    """

    _result_dir: Path
    _cache: Cache | None

    def __init__(self, result_dir: Path, cache: Cache | None = None) -> None:
        """Create a new ProofStateStepper."""
        self._result_dir = result_dir
        self._cache = cache

    def get_next_proof_state(
        self,
        prev_proof_state: ProofState,
        spec_conversation: SpecConversation,
        function_graph: CFunctionGraph,
    ) -> ProofState:
        """Return the next ProofState after prev_proof_state, based on spec_conversation.

        The new proof state is a copy of the given proof state with two differences:

            1. The new proof state's map of functions to specifications is updated with the given
               function and its specification from the SpecConversation.
            2. The new proof state's work stack is either smaller (A) or larger (B).

        (A) Occurs when a function's specification is assumed (e.g., for recursive functions whose
        specs failed repair) or successfully verified. (B) Occurs if backtracking must take place
        (i.e., revisiting the specification of the failing function's callee specifications.)

        Args:
            prev_proof_state (ProofState): The previous proof state.
            spec_conversation (SpecConversation): The spec conversation in which an LLM generated a
                specification for the function on the top of the workstack of prev_proof_state.
            function_graph (CFunctionGraph): The project being verified.

        Returns:
            ProofState: The next proof state for the program, given the conversation.
        """
        specs_for_next_proof_state = prev_proof_state.get_specifications() | {
            spec_conversation.function: spec_conversation.specification
        }
        match spec_conversation.next_step:
            case None:
                msg = f"{spec_conversation} `next_step` field is not set"
                raise ValueError(msg)
            case AcceptVerifiedSpec() | AssumeSpecAsIs():
                # There could be more than one valid specification generated (i.e., when we sample
                # more than once from the LLM). For now, we take the last (valid) specification and
                # write it to disk (see below).
                self._write_spec_to_disk(spec_conversation=spec_conversation)
                if isinstance(spec_conversation.next_step, AssumeSpecAsIs):
                    self._update_cache_for_assumed_spec(
                        specc=spec_conversation,
                        prev_proof_state=prev_proof_state,
                    )
                workstack_for_next_proof_state = prev_proof_state.get_workstack().pop()
                return ProofState(
                    specs=specs_for_next_proof_state,
                    workstack=workstack_for_next_proof_state,
                )
            case BacktrackToCallee(_, _):
                return self._get_proofstate_for_backtracking(
                    specs_for_next_proof_state,
                    prev_proof_state,
                    spec_conversation,
                    function_graph,
                )

            case _:
                msg = f"Unexpected next step strategy: '{spec_conversation.next_step}'"
                raise ValueError(msg)

    def _update_cache_for_assumed_spec(
        self, specc: SpecConversation, prev_proof_state: ProofState
    ) -> None:
        """Update the cache entry for the given spec to `VerificationStatus.ASSUMED`.

        This is called when a spec is assumed (i.e., accepted without successful verification). The
        existing cache entry for this spec is updated to reflect that outcome.

        Args:
            specc (SpecConversation): The spec conversation whose spec is being assumed.
            prev_proof_state (ProofState): The proof state in which the spec was assumed, used to
                reconstruct the `VerificationInput` key.
        """
        if self._cache is None:
            return
        vcontext = prev_proof_state.get_current_context(specc.function)
        vinput = VerificationInput(
            specc.function, specc.specification, vcontext, specc.contents_of_file_to_verify
        )
        if vresult := self._cache.get(vinput):
            self._cache[vinput] = VerificationResult(
                verification_input=vresult.verification_input,
                verification_command=vresult.verification_command,
                status=VerificationStatus.ASSUMED,
                stdout=vresult.stdout,
                stderr=vresult.stderr,
            )

    def _write_spec_to_disk(self, spec_conversation: SpecConversation) -> None:
        """Write a single function specification to a file on disk.

        The resulting file is identical to the corresponding file in the unverified (input)
        program, but some functions may be specified (i.e., have CBMC annotations).

        Specifications are written to a file under result_dir that has the same name (and path)
        as the original (non-specified) file under a directory that is specific to each process
        (i.e., the directory's name is the pid of the process where specification generation is
        running).

        Args:
            spec_conversation (SpecConversation): The SpecConversation comprising the function
                specification to be written to the result file.
        """
        function = spec_conversation.function
        path_to_original_file = Path(function.file_name)
        result_file = self._get_result_file(function=function)

        if not result_file.exists():
            # Create the result file by copying over the original file.
            result_file.parent.mkdir(exist_ok=True, parents=True)
            shutil.copy(path_to_original_file, result_file)

        function_graph = CFunctionGraph(result_file)
        function_with_verified_spec = function_util.get_source_code_with_inserted_spec(
            function_name=function.name,
            specification=spec_conversation.specification,
            function_graph=function_graph,
            comment_out_spec=True,
        )

        function_util.update_function_definition(
            function_name=function.name,
            updated_function_content=function_with_verified_spec,
            function_graph=function_graph,
            file=result_file,
        )

    def _get_result_file(self, function: CFunction) -> Path:
        """Return the path to the result file for a function.

        The "result file" is where the verified or assumed specification for a function is written.

        Examples of original and result file names:
            * "my_research/myfile.c"               => "<result_dir>/<PID>/my_research/myfile.c"
            * "/home/jquser/my_research/myfile.c"
              => "<result_dir>/<PID>/home/jquser/my_research/myfile.c"

        Args:
            function (CFunction): The function for which to obtain the result file.

        Returns:
            Path: The result file.
        """
        path_to_original_file = Path(function.file_name)
        original_file_dir = str(path_to_original_file.parent).lstrip("/")
        pid_dir = Path(str(os.getpid()))
        result_file_dir = self._result_dir / pid_dir / Path(original_file_dir)
        return result_file_dir / path_to_original_file.name

    def _get_proofstate_for_backtracking(
        self,
        specs_for_next_proof_state: dict[CFunction, FunctionSpecification],
        prev_proof_state: ProofState,
        spec_conversation: SpecConversation,
        function_graph: CFunctionGraph,
    ) -> ProofState:
        """Return a proof state given a backtracking step in a spec conversation.

        Backtracking is one possibility when the specification of procedure p does not verify.
        When backtracking from p, the callee named in `spec_conversation.next_step` is pushed onto
        the work stack so it will be re-specified before p is retried. If the callee is an
        external function, its work item is marked `assume_without_verification` so that the
        generated spec is assumed rather than verified.

        Backtracking from p is skipped (and the failing spec for p is assumed instead) in two cases:
            1. The callee does not appear in the function graph.
            2. Both the callee and p are external functions, since re-specifying one
               external stub in terms of another would not make progress.

        Args:
            specs_for_next_proof_state (dict[CFunction, FunctionSpecification]): The specs for the
                next proof state that is being constructed.
            prev_proof_state (ProofState): The previous proof state.
            spec_conversation (SpecConversation): The spec conversation so far.
            function_graph (CFunctionGraph): The function graph under specification generation.

        Returns:
            ProofState: The next proof state to continue to.
        """
        if not isinstance(spec_conversation.next_step, BacktrackToCallee):
            msg = "Next step should be BacktrackToCallee, but is " + spec_conversation.next_step
            raise TypeError(msg)
        callee_name = spec_conversation.next_step.callee
        caller = spec_conversation.function
        callee = function_graph.get_function_or_none(callee_name)
        if not callee or (callee.is_external_function and caller.is_external_function):
            if not callee:
                msg = (
                    f"Backtracking is not possible for callee '{callee_name}'; "
                    "its implementation is missing from the call graph"
                )
            else:
                msg = (
                    f"Backtracking to an external callee '{callee_name}' from an external caller "
                    f"'{caller.name}' is not permitted"
                )
            logger.warning(msg)
            # Since backtracking is not possible, assume the (failing) specs here, and move to the
            # next function to verify.
            spec_conversation.next_step = AssumeSpecAsIs()
            self._write_spec_to_disk(spec_conversation=spec_conversation)
            self._update_cache_for_assumed_spec(spec_conversation, prev_proof_state)

            workstack_for_next_proof_state = prev_proof_state.get_workstack().pop()
            return ProofState(
                specs=specs_for_next_proof_state, workstack=workstack_for_next_proof_state
            )

        assume_callee_specs_after_generation = callee.is_external_function
        if assume_callee_specs_after_generation:
            logger.info(
                f"Backtracking to an external callee '{callee_name}'; generating and assuming specs"
            )
        work_item_for_callee = WorkItem(
            function=callee,
            hint=spec_conversation.next_step.hint,
            assume_without_verification=assume_callee_specs_after_generation,
        )
        workstack_for_next_proof_state = prev_proof_state.get_workstack().push(work_item_for_callee)
        return ProofState(
            specs=specs_for_next_proof_state,
            workstack=workstack_for_next_proof_state,
        )
