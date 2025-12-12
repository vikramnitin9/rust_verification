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

    def __iter__(self) -> Iterator[list[str]]:
        """Return a singleton iterator that yields a list of this specification's clauses.

        This function allows tuple-based unpacking and assignments, e.g.,

            function_spec = ...
            pre, post = function_spec

        Returns:
            Iterator[list[str]]: An iterator comprising a tuple of pre and postconditions.
        """
        return iter((self.preconditions, self.postconditions))

    def __eq__(self, other) -> bool:
        """Return True iff the other specification comprises the same pre and postconditions.

        Args:
            other (object): The object to which to compare this specification to.

        Returns:
            bool: True iff the other specification comprises the same pre and postconditions.
        """
        if not isinstance(other, "FunctionSpecification"):
            return False
        is_preconditions_same = sorted(self.preconditions) == sorted(self.preconditions)
        is_postconditions_same = sorted(self.postconditions) == sorted(self.postconditions)
        return is_preconditions_same and is_postconditions_same
