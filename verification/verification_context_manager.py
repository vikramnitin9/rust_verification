"""Class for working with verification contexts and proof states."""

from util import CFunction, ParsecFile

from .proof_state import ProofState
from .verification_input import VerificationContext


class VerificationContextManager:
    """Class for working with verification contexts and proof states."""

    def current_context(
        self, function: CFunction, parsec_file: ParsecFile, proof_state: ProofState
    ) -> VerificationContext:
        """Return the current verification context for the function.

        Args:
            function (CFunction): The function for which to return a context.
            parsec_file (ParsecFile): The ParsecFile.
            proof_state (ProofState): The ProofState.

        Returns:
            VerificationContext: The current verification context for the function.
        """
        callees_for_function = parsec_file.get_callees(function=function)
        callee_specs = {
            callee.name: proof_state.get_specifications()[callee.name]
            for callee in callees_for_function
        }
        return VerificationContext(
            callee_specs=callee_specs,
            global_variable_specs={},
        )
