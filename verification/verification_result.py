"""Class representing a verification result."""

from dataclasses import dataclass
from enum import StrEnum

from util import CFunction, FunctionSpecification

from .verification_input import VerificationInput


class VerificationStatus(StrEnum):
    """Enum representing the outcome of a verification run.

    SUCCEEDED and FAILED refer to cases when a specification is successfully verified (or fails to
    verify). A specification can be ASSUMED when:

        1. It is the result of generating a spec for an external callee. For example, this might
           occur when a spec is generated for a CBMC stub function (see the functions in the .c
           files in verification/cbmc_stubs/).
        2. It is the result of generating a spec for a self-recursive function.

    """

    SUCCEEDED = "succeeded"
    ASSUMED = "assumed"
    FAILED = "failed"


@dataclass(frozen=True)
class VerificationResult:
    """Class representing a verification result: the output of running a verifier on a function.

    Attributes:
        verification_input (VerificationInput): The input that resulted in this verification result.
        verification_command: The command used to invoke the verifier.
        status (VerificationStatus): The outcome of this verification run.
        stdout (str): The standard output of the verifier.
        stderr (str): The standard error of the verifier.
    """

    verification_input: VerificationInput
    verification_command: str
    status: VerificationStatus
    stdout: str
    stderr: str

    @property
    def succeeded(self) -> bool:
        """Return True iff this verification result has status `SUCCEEDED`.

        Returns:
            bool: True iff this verification result has status `SUCCEEDED`.
        """
        return self.status == VerificationStatus.SUCCEEDED

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
