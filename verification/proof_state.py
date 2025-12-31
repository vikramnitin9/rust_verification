"""Class representing a program's proof state."""

from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType

from util import CFunction, FunctionSpecification, ParsecFile

from .verification_input import VerificationContext
from .work_item import WorkItem


@dataclass
class WorkStack:
    """Class to represent a stack of functions and hints (i.e., `WorkItem`s) to process.

    Attributes:
        work_items (list[WorkItem]): The stack of functions and hints to process.
    """

    work_items: list[WorkItem]

    def __init__(self, functions_and_hints: list[tuple[CFunction, str]]) -> None:
        """Create a new WorkStack."""
        self.work_items = [
            WorkItem(function=function, next_step_hint=hint)
            for function, hint in functions_and_hints
        ]

    def push(self, function: CFunction, next_step_hint: str) -> None:
        """Push the function and next step hint to this workstack.

        Args:
            function (CFunction): The function to process.
            next_step_hint (str): The hint for the function to process.
        """
        self.work_items.append(WorkItem(function=function, next_step_hint=next_step_hint))

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
        return not self.work_items


class ProofState:
    """Class representing a proof state.

    A proof state consists of a set of completed functions (with proven or assumed specifications)
    and a workstack of functions yet to be specified and verified.  If the workstack is empty, then
    every function in the program has a proven or assumed specification.

    Attributes:
        _specs (dict[str, FunctionSpecification]): For each function, its current specification.
            These specs may or may not be verified.
            # MDE: How are identically-named functions in different files distinguished?
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

    def push_onto_workstack(self, function: CFunction, hint: str = "") -> None:
        """Push the given function and (optional) hint onto this proof state's workstack.

        Args:
            function (CFunction): The function to push onto this proof state's workstack.
            hint (str, optional): The hint(s) for spec generation. Defaults to "".
        """
        self._workstack.push(function=function, next_step_hint=hint)

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

    def get_specifications(self) -> MappingProxyType[str, FunctionSpecification]:
        """Return this proof state's specifications.

        Returns:
            dict[str, FunctionSpecification]: This proof state's specifications.
        """
        return MappingProxyType(self._specs)

    def set_specification(self, function: CFunction, spec: FunctionSpecification) -> None:
        """Set this proof state's spec for a given function.

        Args:
            function (CFunction): The function whose specs to set.
            spec (FunctionSpecification): The specs to set.
        """
        self._specs[function.name] = spec

    # MDE: I'm not clear on the rules about when a function is represented by its name (as in the
    # mapping returned by get_specifications) and when it is represented by a CFunction (as here).
    # (At the place where get_specifications is called, the CFunction is available.)
    def get_specification(self, function: CFunction) -> FunctionSpecification | None:
        """Return the function's specification from this proof state.

        Args:
            function (CFunction): The function for which to retrieve a specification.

        Returns:
            FunctionSpecification | None: The specification for this function, otherwise None.
        """
        return self._specs.get(function.name)

    def get_current_context(self, function: CFunction) -> VerificationContext:
        """Return the current verification context for the function.

        Args:
            function (CFunction): The function for which to return a context.

        Returns:
            VerificationContext: The current verification context for the function.
        """
        parsec_file = ParsecFile(file_path=Path(function.file_name))
        callees_for_function = parsec_file.get_callees(function=function)
        callee_specs = {
            callee.name: callee_spec
            for callee in callees_for_function
            if (callee_spec := self.get_specification(callee))
        }
        return VerificationContext(
            callee_specs=callee_specs,
            global_variable_specs={},
        )
