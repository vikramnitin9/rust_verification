"""Class for managing verification contexts, proof states, and verified."""

from pathlib import Path
from types import MappingProxyType

from util import CFunction, FunctionSpecification, ParsecFile

from .proof_state import ProofState
from .verification_input import VerificationContext


class VerificationContextManager:
    """Class for managing verification contexts, proof states, and verified specs.

    Each proof state in the system is associated with a function. Ideally, every proof state should
    know about each of the verified specifications in a program. However, this requires every extant
    proof state to be updated whenever a specification is verified.

    The VerificationContextManager attempts to mitigate this by maintaining a global store of
    verified specs that can be queried.
    """

    _verified_specs: dict[CFunction, FunctionSpecification]

    def __init__(self) -> None:
        """Create a VerificationContextManager."""
        self._verified_specs = {}

    def set_verified_spec(self, function: CFunction, verified_spec: FunctionSpecification) -> None:
        """Set the given function's verified spec in this context manager.

        Args:
            function (CFunction): The function whose verified spec to set in this context manager.
            verified_spec (FunctionSpecification): The verified spec to set in this context manager.
        """
        self._verified_specs[function] = verified_spec

    def get_verified_spec(self, function: CFunction) -> FunctionSpecification | None:
        """Return this function's verified spec, if it exists.

        Args:
            function (CFunction): The function whose specs to return.

        Returns:
            FunctionSpecification | None: The verified spec to return, otherwise None.
        """
        return self._verified_specs.get(function)

    def get_verified_specs(self) -> MappingProxyType[CFunction, FunctionSpecification]:
        """Return an immutable view of the verified specs of this program.

        Returns:
            MappingProxyType[CFunction, FunctionSpecification]: An immutable view of the verified
                specs of this program.
        """
        return MappingProxyType(self._verified_specs)

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
            if (callee_spec := proof_state.get_specification(callee))
        }
        return VerificationContext(
            callee_specs=callee_specs,
            global_variable_specs={},
        )
