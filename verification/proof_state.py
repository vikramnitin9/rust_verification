"""Class representing a program's proof state."""

from util import FunctionSpecification, ParsecFunction


class ProofState:
    """Class representing a program's proof state.

    Attributes:
        _specs (dict[str, FunctionSpecification]): The current specifications for each function.
            These specs may or may not be verified.
        _workstack (list[tuple[ParsecFunction, str]]): A stack of functions that must be
            (re)processed.
        _verified_functions (list[str]): A list of functions whose specs have been successfully
            verified.
        _assumed_functions (list[str]): A list of functions whose specs are assumed for
            verification.
    """

    _specs: dict[str, FunctionSpecification]
    _workstack: list[tuple[ParsecFunction, str]]
    _verified_functions: list[str]
    _assumed_functions: list[str]

    def __init__(self, workstack: list[tuple[ParsecFunction, str]]) -> None:
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
        self._workstack.append((function, hint))

    def peek_workstack(self) -> tuple[ParsecFunction, str]:
        """Return the top element of the workstack.

        Returns:
            tuple[ParsecFunction, str]: The top element of the workstack.
        """
        return self._workstack[-1]

    def pop_workstack(self) -> None:
        """Remove the top element of the workstack."""
        self._workstack.pop()

    def is_workstack_empty(self) -> bool:
        """Return True iff this proof state's workstack is empty.

        Returns:
            bool: True iff this proof state's workstack is empty.
        """
        return len(self._workstack) == 0

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
