"""Class for working with verification contexts and proof states."""
# MDE: Please make the description more specific than "working with".  What does this class
# represent or do?

from pathlib import Path

from util import CFunction, FunctionSpecification, ParsecFile

from .proof_state import ProofState
from .verification_input import VerificationContext


class VerificationContextManager:
    """Class for working with verification contexts and proof states."""

    _verified_specs: dict[str, FunctionSpecification]

    def __init__(self) -> None:
        """Create a VerificationContextManager."""
        self._verified_specs = {}

    def set_verified_spec(self, function: CFunction, verified_spec: FunctionSpecification) -> None:
        """Set the given function's verified spec in this context manager.

        Args:
            function (CFunction): The function whose verified spec to set in this context manager.
            verified_spec (FunctionSpecification): The verified spec to set in this context manager.
        """
        self._verified_specs[function.name] = verified_spec

    def get_verified_spec(self, function: CFunction) -> FunctionSpecification | None:
        """Return this function's verified spec, if it exists.

        Args:
            function (CFunction): The function whose specs to return.

        Returns:
            FunctionSpecification | None: The verified spec to return, otherwise None.
        """
        return self._verified_specs.get(function.name)

    # MDE: I think this can be a method of ProofState.  It is not related to the fields of
    # VerificationContextManager.
    def current_context(self, function: CFunction, proof_state: ProofState) -> VerificationContext:
        """Return the current verification context for the function.

        Args:
            function (CFunction): The function for which to return a context.
            proof_state (ProofState): The ProofState.

        Returns:
            VerificationContext: The current verification context for the function.
        """
        parsec_file = ParsecFile(file_path=Path(function.file_name))
        callees_for_function = parsec_file.get_callees(function=function)
        callee_specs = {
            callee.name: callee_spec
            for callee in callees_for_function
            # MDE: I think the RHS can be: proof_state.get_specification(callee)
            if (callee_spec := proof_state.get_specifications().get(callee.name))
        }
        return VerificationContext(
            callee_specs=callee_specs,
            global_variable_specs={},
        )
