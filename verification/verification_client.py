"""Client for invoking a verifier on C source code."""

from typing import Protocol

from .verification_result import VerificationInput, VerificationResult


class VerificationClient(Protocol):
    """Client for invoking a verifier on C source code."""

    def verify(
        self,
        vinput: VerificationInput,
    ) -> VerificationResult:
        """Return the result of verifying the verification input.

        Args:
            vinput (VerificationInput): The verification input.

        Returns:
            VerificationResult: The result of verifying the given verification input.
        """
        ...
