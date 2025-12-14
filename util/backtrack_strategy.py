"""Class to represent backtracking strategies."""

from dataclasses import dataclass


@dataclass
class BacktrackStrategy:
    """Top-level type for backtracking information."""

    reasoning: str


@dataclass
class AssumeSpec(BacktrackStrategy):
    """Represent the backtracking strategy that assumes a failing spec."""


@dataclass
class BacktrackToCallee(BacktrackStrategy):
    """Represent the backtracking strategy that re-generates specs for a function.

    Attributes:
        callee_name (str): The name of the callee function to backtrack to.

    """

    callee_name: str

    def __init__(self, reasoning: str, callee_name: str) -> None:
        self.reasoning = reasoning
        self.callee_name = callee_name
