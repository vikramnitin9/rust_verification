"""Class for creating new ProofState(s) based on a SpecConversation."""

import os
import shutil
from pathlib import Path

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

from .proof_state import ProofState, WorkItem


class ProofStateStepper:
    """Class for creating new proof state(s) based on a SpecConversation and a previous proof state.

    Attributes:
        result_dir (Path): The root directory under which verified/assumed specs are written.
    """

    _result_dir: Path

    def __init__(self, result_dir: Path) -> None:
        """Create a new ProofStateStepper."""
        self._result_dir = result_dir

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
                workstack_for_next_proof_state = prev_proof_state.get_workstack().pop()
                return ProofState(
                    specs=specs_for_next_proof_state,
                    workstack=workstack_for_next_proof_state,
                )
            case BacktrackToCallee(callee_name, hint):
                if callee := function_graph.get_function_or_none(function_name=callee_name):
                    work_item_for_callee = WorkItem(function=callee, hint=hint)
                    workstack_for_next_proof_state = prev_proof_state.get_workstack().push(
                        work_item_for_callee
                    )
                    return ProofState(
                        specs=specs_for_next_proof_state,
                        workstack=workstack_for_next_proof_state,
                    )
                logger.warning(
                    f"Backtracking is not possible for callee '{callee_name}', as the project does "
                    "not provide an implementation; it may be a library function"
                )
                # Since backtracking is not possible, assume the (failing) specs here, and move to
                # the next function to verify.
                self._write_spec_to_disk(spec_conversation=spec_conversation)
                workstack_for_next_proof_state = prev_proof_state.get_workstack().pop()
                return ProofState(
                    specs=specs_for_next_proof_state,
                    workstack=workstack_for_next_proof_state,
                )

            case _:
                msg = f"Unexpected next step strategy: '{spec_conversation.next_step}'"
                raise ValueError(msg)

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
