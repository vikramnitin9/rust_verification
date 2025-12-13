"""Client for verifying source code."""

from pathlib import Path
from typing import Protocol

from .verification_result import Failure, Success


class VerificationClient(Protocol):
    """Client for verifying source code."""

    def verify(
        self,
        function_name: str,
        names_of_verified_functions: list[str],
        names_of_trusted_functions: list[str],
        file_path: Path,
    ) -> Success | Failure:
        """Return the result of verifying the function named `function_name`.

        Args:
            function_name (str): The name of the function to verify.
            names_of_verified_functions (list[str]): The names of functions that have been verified.
            names_of_trusted_functions (list[str]): The names of functions whose specifications
                should be trusted by the verifier.
            file_path (Path): The file in which the function to verify is defined.

        Raises:
            RuntimeError: Raised when an error occurs in executing the verification command.

        Returns:
            Success | Failure: Success if the function successfully verifies, Failure if the
                function does not verify.
        """
        ...
