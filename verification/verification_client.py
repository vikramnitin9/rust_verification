"""Client for verifying source code."""

from typing import Protocol

from .specification_generation_context import SpecificationGenerationContext
from .verification_result import Failure, Success


class VerificationClient(Protocol):
    """Client for verifying source code."""

    def verify(
        self, specification_generation_context: SpecificationGenerationContext
    ) -> Success | Failure:
        """Return the result of verifying the function in the given spec. generation context.

        Args:
            specification_generation_context (SpecificationGenerationContext): The specification
                generation context to be used in verification.

        Raises:
            RuntimeError: Raised when an error occurs in executing the verification command.

        Returns:
            Success | Failure: Success if the function successfully verifies, Failure if the
                function does not verify.
        """
        ...
