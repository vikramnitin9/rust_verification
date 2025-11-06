"""Module to represent verification results."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Success:
    """Represents a successful verification result."""


@dataclass(frozen=True)
class Failure:
    """Represents an unsuccessful verification result.

    Attributes:
        error_message (str): The error message stemming from an unsuccessful verification result.
    """

    error_message: str
