"""Class representing a verification result."""

from dataclasses import dataclass

from util import FunctionSpecification, ParsecFunction

from .verification_input import VerificationInput


@dataclass(frozen=True)
class VerificationResult:
    _input: VerificationInput
    succeeded: bool
    failure_messages: str | None

    def get_function(self) -> ParsecFunction:
        return self._input.function

    def get_spec(self) -> FunctionSpecification:
        return self._input.spec
