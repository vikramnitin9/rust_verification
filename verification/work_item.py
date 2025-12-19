"""Class to represent a function on a proof state's workstack."""

from dataclasses import dataclass

from util import ParsecFunction


@dataclass(frozen=True)
class WorkItem:
    """Class to represent a function on a proof state's workstack.

    Attributes:
        function (ParsecFunction): The function on a proof state's workstack.
        backtracking_hint: The hints to use in generating or repairing specifications.
    """

    function: ParsecFunction
    backtracking_hint: str
