"""Client for verifying source code."""

from pathlib import Path
from typing import Protocol

from util import CFunction, FunctionSpecification

from .proof_state import ProofState
from .verification_result import VerificationResult


class VerificationClient(Protocol):
    """Client for verifying source code."""

    def verify(
        self,
        function: CFunction,
        spec: FunctionSpecification,
        proof_state: ProofState,
        path_to_file: Path,
    ) -> VerificationResult:
        """Return the result of verifying the given function.

        Args:
            function (CFunction): The function to verify.
            spec (FunctionSpecification): The specification for the function to verify.
            proof_state (ProofState): The proof state.
            path_to_file (Path): The path to the file containing the function to verify.

        Returns:
            VerificationResult: The result of verifying the given function.
        """
        ...
