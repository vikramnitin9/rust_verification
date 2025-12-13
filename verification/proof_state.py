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
        self._specs = {}
        self._workstack = workstack
        self._verified_functions = []
        self._assumed_functions = []

    def peek_workstack(self) -> tuple[ParsecFunction, str]:
        return self._workstack[-1]

    def is_workstack_empty(self) -> bool:
        return len(self._workstack) == 0

    def get_specifications(self) -> dict[str, FunctionSpecification]:
        return self._specs
