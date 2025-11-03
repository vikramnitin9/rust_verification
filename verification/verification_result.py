"""Module to represent verification results."""

from dataclasses import dataclass


@dataclass
class VerificationResult:
    """Top-level class to represent a verification result."""


@dataclass
class Success(VerificationResult):
    """Represents a successful verification result."""


@dataclass
class Failure(VerificationResult):
    """Represents an unsuccessful verification result.

    Attributes:
        error_message (str): The error message stemming from an unsuccessful verification result.
    """

    error_message: str
