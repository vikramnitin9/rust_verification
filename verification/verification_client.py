"""Client for verifying source code."""

from pathlib import Path
from typing import Protocol

from util import FunctionSpecification

from .proof_state import ProofState
from .verification_result import VerificationResult


class VerificationClient(Protocol):
    """Client for verifying source code."""

    def verify(
        self,
        function_name: str,
        names_of_verified_functions: list[str],
        names_of_trusted_functions: list[str],
        file_path: Path,
    ) -> VerificationResult:
        """Return the result of verifying the function named `function_name`.

        Args:
            function_name (str): The name of the function to verify.
            names_of_verified_functions (list[str]): The names of functions that have been verified.
            names_of_trusted_functions (list[str]): The names of functions whose specifications
                should be trusted by the verifier.
            file_path (Path): The path to the file in which the function to verify is defined.

        Raises:
            RuntimeError: Raised when an error occurs in executing the verification command.

        Returns:
            VerificationResult: The verification result for this function.
        """
        ...

    def verify_function_with_spec(
        self, function_name: str, spec: FunctionSpecification, proof_state: ProofState
    ) -> VerificationResult:
        """Return the result of verifying the function with the given specification.

        Args:
            function_name (str): The name of the function to verify.
            spec (FunctionSpecification): The specifications for the function to verify.
            proof_state (ProofState): The proof state.

        Returns:
            VerificationResult: The verification result for this function.
        """
        ...
