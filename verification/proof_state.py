"""Class representing a program's proof state."""

from dataclasses import dataclass

from util import FunctionSpecification, ParsecFunction

from .work_item import WorkItem


@dataclass
class WorkStack:
    """Class to represent a stack of functions and hints (i.e., WorkItem) to process.

    Attributes:
        work_items (list[WorkItem]): The stack of functions and hints to process.
    """

    work_items: list[WorkItem]

    def __init__(self, functions_and_hints: list[tuple[ParsecFunction, str]]) -> None:
        """Create a new WorkStack."""
        self.work_items = [
            WorkItem(function=function, backtracking_hint=hint)
            for function, hint in functions_and_hints
        ]

    def push(self, function: ParsecFunction, backtracking_hint: str) -> None:
        """Push the function and backtracking hint to this workstack.

        Args:
            function (ParsecFunction): The function to process.
            backtracking_hint (str): The hint for the function to process.
        """
        self.work_items.append(WorkItem(function=function, backtracking_hint=backtracking_hint))

    def peek(self) -> WorkItem:
        """Return the item at the top of this workstack.

        Returns:
            WorkItem: The item at the top of this workstack.
        """
        return self.work_items[-1]

    def pop(self) -> WorkItem:
        """Remove the item at the top of this workstack and return it.

        Returns:
            WorkItem: The removed item at the top of this workstack.
        """
        return self.work_items.pop()

    def is_empty(self) -> bool:
        """Return True iff there are no elements in this workstack.

        Returns:
            bool: True iff there are no elements in this workstack.
        """
        return len(self.work_items) == 0


class ProofState:
    """Class representing a program's proof state.

    Attributes:
        _specs (dict[str, FunctionSpecification]): The current specifications for each function.
            These specs may or may not be verified.
        _workstack (WorkStack): A stack of functions that must be (re)processed.
        _verified_functions (list[str]): A list of functions whose specs have been successfully
            verified.
        _assumed_functions (list[str]): A list of functions whose specs are assumed for
            verification.
    """

    _specs: dict[str, FunctionSpecification]
    _workstack: WorkStack
    _verified_functions: list[str]
    _assumed_functions: list[str]

    def __init__(self, workstack: WorkStack) -> None:
        """Create a new ProofState."""
        self._specs = {}
        self._workstack = workstack
        self._verified_functions = []
        self._assumed_functions = []

    def push_onto_workstack(self, function: ParsecFunction, hint: str = "") -> None:
        """Push the given function and (optional) hint onto this proof state's workstack.

        Args:
            function (ParsecFunction): The function to push onto this proof state's workstack.
            hint (str, optional): The hint(s) for spec generation. Defaults to "".
        """
        self._workstack.push(function=function, backtracking_hint=hint)

    def peek_workstack(self) -> WorkItem:
        """Return the top element of the workstack.

        Returns:
            WorkItem: The top element of the workstack.
        """
        return self._workstack.peek()

    def pop_workstack(self) -> None:
        """Remove the top element of the workstack."""
        self._workstack.pop()

    def is_workstack_empty(self) -> bool:
        """Return True iff this proof state's workstack is empty.

        Returns:
            bool: True iff this proof state's workstack is empty.
        """
        return self._workstack.is_empty()

    def get_specifications(self) -> dict[str, FunctionSpecification]:
        """Return this proof state's specifications.

        Returns:
            dict[str, FunctionSpecification]: This proof state's specifications.
        """
        return self._specs

    def set_specification(self, function: ParsecFunction, spec: FunctionSpecification) -> None:
        """Set this proof state's spec for a given function.

        Args:
            function (ParsecFunction): The function whose specs to set.
            spec (FunctionSpecification): The specs to set.
        """
        self._specs[function.name] = spec

    def assume_function(self, function: ParsecFunction) -> None:
        """Update this proof state's list of functions with assumed specs.

        Args:
            function (ParsecFunction): The function whose spec should be assumed.
        """
        self._assumed_functions.append(function.name)
