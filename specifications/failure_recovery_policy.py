"""Module to represent the failure recovery policy for generated specifications."""

from dataclasses import dataclass


@dataclass
class FailureRecoveryPolicy:
    """Represents a failure recovery policy for generated specifications.

    Attributes:
        reasoning (str): The reasoning provided by a model for the policy.
    """

    reasoning: str


@dataclass
class AssumeSpec(FailureRecoveryPolicy):
    """Policy where the generated specs should be assumed (i.e., trusted)."""


@dataclass
class BacktrackToCallee(FailureRecoveryPolicy):
    """Policy where the policy is to backtrack to a callee and re-generate its specifications.

    Attributes:
        callee_to_backtrack_to (str): The name of the callee to backtrack to.
    """

    callee_to_backtrack_to: str

    def __init__(self, reasoning: str, callee_to_backtrack_to: str):
        self.reasoning = reasoning
        self.callee_to_backtrack_to = callee_to_backtrack_to
