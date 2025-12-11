"""Class representing a verification result."""

from dataclasses import dataclass

from .verification_input import VerificationInput


@dataclass(frozen=True)
class VerificationResult:
    _input: VerificationInput
    _succeeded: bool
    _failure_messages: str | None
