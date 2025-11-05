"""Module to represent verification results."""

from abc import ABC
from dataclasses import dataclass


@dataclass(frozen=True)
class VerificationResult(ABC):
    """Top-level class to represent a verification result."""


@dataclass(frozen=True)
class Success(VerificationResult):
    """Represents a successful verification result."""


@dataclass(frozen=True)
class Failure(VerificationResult):
    """Represents an unsuccessful verification result.

    Attributes:
        error_message (str): The error message stemming from an unsuccessful verification result.
    """

    error_message: str
