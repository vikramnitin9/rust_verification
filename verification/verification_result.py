"""Module to represent verification results."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Success:
    """Represents a successful verification result."""


@dataclass(frozen=True)
class Failure:
    """Represents an unsuccessful verification result.

    Attributes:
        stdout (str): The stdout output from an unsuccessful verification result.
        stderr (str): The stderr output from an unsuccessful verification result.
    """

    stdout: str
    stderr: str
