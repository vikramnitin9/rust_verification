"""Class representing a verification result."""

from dataclasses import dataclass

from util import FunctionSpecification, ParsecFunction

from .verification_input import VerificationInput


@dataclass(frozen=True)
class VerificationResult:
    """Class representing a verification result (i.e., the output of verifying a function).

    Attributes:
        _input (VerificationInput): The input for this verification result.
        succeeded (bool): True iff the input for this verification result successfully verified.
        failure_messages (str | None): Any failure messages for this verification result, if its
            input failed verification.
    """

    _input: VerificationInput
    succeeded: bool
    failure_messages: str | None

    def get_function(self) -> ParsecFunction:
        """Return the function associated with this verification result's input.

        Returns:
            ParsecFunction: The function associated with this verification result's input.
        """
        return self._input.function

    def get_spec(self) -> FunctionSpecification:
        """Return the specification associated with this verification result's input.

        Returns:
            FunctionSpecification: Return the specification associated with this verification
                result's input.
        """
        return self._input.spec
