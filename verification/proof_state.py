"""Class representing a program's proof state."""

from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType

from util import CFunction, FunctionSpecification, ParsecFile

from .verification_input import VerificationContext
from .work_item import WorkItem


@dataclass(frozen=True)
class WorkStack:
    """Class to represent a stack of functions and hints (i.e., `WorkItem`s) to process.

    Attributes:
        work_items (tuple[WorkItem, ...]): The immutable stack of functions and hints to process.
    """

    work_items: tuple[WorkItem, ...]

    def push(self, work_item: WorkItem) -> "WorkStack":
        """Return a new workstack with the given work item on top.

        Args:
            work_item (WorkItem): The work item to be on top of the new work stack.

        Returns:
            WorkStack: A new workstack with the work item on top.
        """
        return WorkStack((*self.work_items, work_item))

    def peek(self) -> WorkItem:
        """Return the item at the top of this workstack.

        Returns:
            WorkItem: The item at the top of this workstack.
        """
        return self.work_items[-1]

    def pop(self) -> "WorkStack":
        """Return a new workstack with the top element removed.

        Returns:
            WorkStack: A new workstack with the top element removed.
        """
        return WorkStack(work_items=self.work_items[:-1])

    def is_empty(self) -> bool:
        """Return True iff there are no elements in this workstack.

        Returns:
            bool: True iff there are no elements in this workstack.
        """
        return not self.work_items


class ProofState:
    """Class representing an immutable proof state.

    A proof state consists of a set of completed functions (with proven or assumed specifications)
    and a workstack of functions yet to be specified and verified.  If the workstack is empty, then
    every function in the program has a proven or assumed specification.

    Attributes:
        _specs (MappingProxyType[str, FunctionSpecification]): The current specifications for
            each function. These specifications may or may not be verified.
            # MDE: How are identically-named functions in different files distinguished?
        _workstack (WorkStack): A stack of functions that must be (re)processed.
        _verified_functions (list[str]): A list of functions whose specs have been successfully
            verified.
        _assumed_functions (list[str]): A list of functions whose specs are assumed for
            verification.

    """

    _specs: MappingProxyType[str, FunctionSpecification]
    _workstack: WorkStack
    _verified_functions: list[str]
    _assumed_functions: list[str]

    def __init__(self, specs: dict[str, FunctionSpecification], workstack: WorkStack) -> None:
        """Create a new ProofState."""
        self._specs = MappingProxyType(specs)
        self._workstack = workstack

    def peek_workstack(self) -> WorkItem:
        """Return the top element of the workstack.

        Returns:
            WorkItem: The top element of the workstack.
        """
        return self._workstack.peek()

    def is_workstack_empty(self) -> bool:
        """Return True iff this proof state's workstack is empty.

        Returns:
            bool: True iff this proof state's workstack is empty.
        """
        return self._workstack.is_empty()

    def get_workstack(self) -> WorkStack:
        """Return this proof state's work stack.

        Returns:
            WorkStack: This proof state's work stack.
        """
        return self._workstack

    def set_workstack(self, workstack: WorkStack) -> "ProofState":
        """Return a new proof state updated with the given work stack.

        Args:
            workstack (WorkStack): The work stack for the new proof state.

        Returns:
            ProofState: The new proof state updated with the given work stack.
        """
        return ProofState(specs=self._specs.copy(), workstack=workstack)

    def get_specifications(self) -> MappingProxyType[str, FunctionSpecification]:
        """Return this proof state's specifications.

        Returns:
            dict[str, FunctionSpecification]: This proof state's specifications.
        """
        return MappingProxyType(self._specs)

    def set_specification(
        self, function: CFunction, specification: FunctionSpecification
    ) -> "ProofState":
        """Return a new proof state with updated specifications for the given function.

        Args:
            function (CFunction): The function.
            specification (FunctionSpecification): The specification.

        Returns:
            ProofState: A new proof state with updated specifications for the given function.
        """
        updated_specs = self._specs | {function.name: specification}
        return ProofState(specs=updated_specs, workstack=self._workstack)

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
            callee: callee_spec
            for callee in callees_for_function
            if (callee_spec := self._specs.get(callee.name))
        }
        return VerificationContext(
            callee_specs=callee_specs,
            global_variable_specs={},
        )
