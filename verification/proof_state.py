"""Class representing a program's proof state."""

from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Self

from util import CFunction, FunctionSpecification, ParsecProject

from .verification_input import VerificationContext


@dataclass(frozen=True)
class WorkItem:
    """Class to represent a function on a proof state's workstack.

    Attributes:
        function (CFunction): A function that needs to be specified.  The function might need to be
            processed for the first time (in which case the hint is empty), or it might need to be
            reprocessed because of backtracking (in which case the hint is non-empty).  To process a
            function is to take a step:
            * an LLM generates a specification
            * the verifier is called, and the specification may be repaired
            * the LLM decides what to do next
        hint: The hint(s) to use in re-generating callee specifications during backtracking.
            Not used during specification repair.
    """

    function: CFunction
    hint: str


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
        _specs (dict[CFunction, FunctionSpecification]): The current specifications for
            each function. These specifications may or may not be verified.
            # TODO: How are identically-named functions in different files distinguished?
        _workstack (WorkStack): A stack of functions that must be (re)processed.
        # TODO: Do we need to explicitly consider assumed specifications?

    """

    _specs: dict[CFunction, FunctionSpecification]
    _workstack: WorkStack

    def __init__(self, specs: dict[CFunction, FunctionSpecification], workstack: WorkStack) -> None:
        """Create a new ProofState."""
        self._specs = specs
        self._workstack = workstack

    @classmethod
    def from_functions(cls, functions: list[CFunction]) -> Self:
        """Create a new ProofState with a workstack constructed from the given functions.

        Args:
            functions (list[CFunction]): The functions from which to construct a new ProofState,
                in reverse topological order.

        Returns:
            Self: A new ProofState with a workstack constructed from the given functions.
        """
        initial_workstack = WorkStack(tuple(WorkItem(function, "") for function in functions))
        return cls(specs={}, workstack=initial_workstack)

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

    def get_specifications(self) -> MappingProxyType[CFunction, FunctionSpecification]:
        """Return this proof state's specifications.

        Returns:
            dict[CFunction, FunctionSpecification]: This proof state's specifications.
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
        updated_specs = self._specs | {function: specification}
        return ProofState(specs=updated_specs, workstack=self._workstack)

    def get_specification(self, function: CFunction) -> FunctionSpecification | None:
        """Return the function's specification from this proof state.

        Args:
            function (CFunction): The function for which to retrieve a specification.

        Returns:
            FunctionSpecification | None: The specification for this function, otherwise None.
        """
        return self._specs.get(function)

    def get_current_context(self, function: CFunction) -> VerificationContext:
        """Return the current verification context for the function.

        Args:
            function (CFunction): The function for which to return a context.

        Returns:
            VerificationContext: The current verification context for the function.
        """
        parsec_project = ParsecProject(input_path=Path(function.file_name))
        callees_for_function = parsec_project.get_callees(function=function)
        callee_specs = {
            callee: callee_spec
            for callee in callees_for_function
            if (callee_spec := self._specs.get(callee))
        }
        return VerificationContext(
            callee_specs=callee_specs,
            global_variable_specs={},
        )
