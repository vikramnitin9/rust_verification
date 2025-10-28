"""Class representing the pre and postconditions of a function."""

from collections.abc import Iterator
from dataclasses import dataclass


@dataclass
class FunctionSpecification:
    """Represents the pre and postconditions of a function, if present.

    Attributes:
        preconditions (list[str]): The preconditions of the function.
        postconditions (list[str]): The postconditions of the function.
    """

    preconditions: list[str]
    postconditions: list[str]

    # TODO: What is the point of this?
    def __iter__(self) -> Iterator[list[str]]:
        """Return a singleton iterator that yields a list this specification's clauses.

        Returns:
            Iterator[list[str]]: An iterator comprising a tuple of pre and postconditions.
        """
        return iter((self.preconditions, self.postconditions))
