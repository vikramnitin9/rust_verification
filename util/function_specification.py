"""Class representing the pre and postconditions of a function."""

from collections.abc import Iterator
from dataclasses import dataclass


@dataclass
class FunctionSpecification:
    """Represents the pre and postconditions of a function, if present.

    # MDE: What is the format of each string?  (I think maybe it's a CBMC macro as it would appear
    # in C source code.  But a reader would be forgiven for thinking that it is just the expression
    # part, especially since the preconditions and postconditions are separated.
    Attributes:
        # MDE: Why is this two lists?  I don't see anywhere in the code
        # that makes any distinction between them.
        # MDE: Should you document that it is an error for both to be empty?  Should the code test
        # that?
        preconditions (list[str]): The preconditions of the function.
        postconditions (list[str]): The postconditions of the function.
    """

    preconditions: list[str]
    postconditions: list[str]

    def __iter__(self) -> Iterator[list[str]]:
        """Return a singleton iterator that yields a list of this specification's clauses.

        This function allows tuple-based unpacking and assignments, e.g.,

            function_spec = ...
            pre, post = function_spec

        Returns:
            Iterator[list[str]]: An iterator comprising a tuple of pre and postconditions.
        """
        return iter((self.preconditions, self.postconditions))
