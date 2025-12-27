"""Class to represent a function on a proof state's workstack."""

from dataclasses import dataclass

from util import CFunction


@dataclass(frozen=True)
class WorkItem:
    """Class to represent a function on a proof state's workstack.

    Attributes:
        function (CFunction): The function on a proof state's workstack.
        backtracking_hint: The hints to use in generating or repairing specifications.
    """

    function: CFunction
    backtracking_hint: str
