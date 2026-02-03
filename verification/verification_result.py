"""Class representing a verification result."""

from dataclasses import dataclass

from util import CFunction, FunctionSpecification

from .verification_input import VerificationInput


@dataclass(frozen=True)
class VerificationResult:
    """Class representing a verification result: the output of running a verifier on a function.

    Attributes:
        verification_input (VerificationInput): The input that resulted in this verification result.
        verification_command (str): The command used to invoke the verifier.
        succeeded (bool): True iff the input for this verification result successfully verified.
        failure_messages (str | None): Any failure messages for this verification result, if its
            input failed verification.
    """

    verification_input: VerificationInput
    verification_command: str
    succeeded: bool
    stdout: str
    stderr: str

    def get_function(self) -> CFunction:
        """Return the function being verified.

        Returns:
            CFunction: The function being verified.
        """
        return self.verification_input.function

    def get_spec(self) -> FunctionSpecification:
        """Return the specification being verified.

        Returns:
            FunctionSpecification: Return the specification being verified.
        """
        return self.verification_input.spec

    def get_source_code_contents(self) -> str:
        """Return the source code that the verifier ran on.

        Returns:
            str: The source code that the verifier ran on.
        """
        return self.verification_input.contents_of_file_to_verify
