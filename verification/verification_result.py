"""Module to represent verification results."""

from dataclasses import dataclass
from pathlib import Path


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
        source (Path): The path to the file that failed to verify.
        stdout (str): The stdout output from an unsuccessful verification result.
        stderr (str): The stderr output from an unsuccessful verification result.
        num_failures (int): The number of reported failures in an unsuccessful verification result.
    """

    source: Path
    stdout: str
    stderr: str
    num_failures: int
