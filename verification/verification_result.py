"""Module to represent verification results."""

from dataclasses import dataclass


@dataclass(frozen=True)
class VerificationResult:
    """Represents a verifier result."""


@dataclass(frozen=True)
class Success(VerificationResult):
    """Represents a successful verification result."""


@dataclass(frozen=True)
class Failure(VerificationResult):
    """Represents an unsuccessful verification result.

    Attributes:
        stdout (str): The stdout output from an unsuccessful verification result.
        stderr (str): The stderr output from an unsuccessful verification result.
    """

    stdout: str
    stderr: str
