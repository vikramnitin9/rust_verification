"""Class representing a verification result."""

from dataclasses import dataclass

from util import CFunction, FunctionSpecification, ParsecFile

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

    def get_parsec_file(self) -> ParsecFile:
        """Return the ParsecFile parsed from this verification result's input file.

        Returns:
            ParsecFile: The ParsecFile parsed from this verification result's input file.
        """
        return ParsecFile.parse_source_with_cbmc_annotations(
            self.verification_input.path_to_input_file
        )


class Failure(VerificationResult):
    """Stub to make sure the build passes.

    TODO: Remove me and replace all usages of me with `VerificationResult`.

    """


class Success(VerificationResult):
    """Stub to make sure the build passes.

    TODO: Remove me and replace all usages of me with `VerificationResult`.

    """
