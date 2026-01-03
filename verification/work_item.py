"""Class to represent a function on a proof state's workstack."""

from dataclasses import dataclass

from util import CFunction


@dataclass(frozen=True)
class WorkItem:
    """Class to represent a function on a proof state's workstack.

    Attributes:
        function (CFunction): The function on a proof state's workstack.
        next_step_hint: The hint(s) to use in repairing specifications or re-generating callee
            specifications.
    """

    function: CFunction
    next_step_hint: str
