"""Class representing a verification result."""

from dataclasses import dataclass

from util import CFunction, FunctionSpecification

from .verification_input import VerificationInput


@dataclass(frozen=True)
class VerificationResult:
    """Class representing a verification result (i.e., the output of verifying a function).

    Attributes:
        verification_input (VerificationInput): The input that resulted in this verification result.
        succeeded (bool): True iff the input for this verification result successfully verified.
        failure_messages (str | None): Any failure messages for this verification result, if its
            input failed verification.
    """

    verification_input: VerificationInput
    succeeded: bool
    failure_messages: str | None

    def get_function(self) -> CFunction:
        """Return the function associated with this verification result's input.

        Returns:
            CFunction: The function associated with this verification result's input.
        """
        return self.verification_input.function

    def get_spec(self) -> FunctionSpecification:
        """Return the specification associated with this verification result's input.

        Returns:
            FunctionSpecification: Return the specification associated with this verification
                result's input.
        """
        return self.verification_input.spec

    def get_source_code_contents(self) -> str:
        """Return the source code from this verification result (i.e., what the verifier ran on).

        Returns:
            str: The source code from this verification result.
        """
        return self.verification_input.contents_of_file_to_verify
