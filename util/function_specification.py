"""Class representing the pre and postconditions of a function."""

from collections.abc import Iterator
from dataclasses import dataclass


@dataclass
class FunctionSpecification:
    """Represents the pre and postconditions of a function, if present.

    Both the pre and postconditions array comprise strings that are CBMC macros.

    For example, a preconditions array may be: ["__CPROVER_requires(a < INT_MAX)"], while a
    postconditions array might be: ["__CPROVER_ensures(*b == old(a))"].

    Attributes:
        preconditions (list[str]): The preconditions of the function.
        postconditions (list[str]): The postconditions of the function.
    """

    preconditions: list[str]
    postconditions: list[str]

    def __init__(self, preconditions: list[str], postconditions: list[str]) -> None:
        """Create a new FunctionSpecification."""
        if not preconditions and not postconditions:
            msg = "Both the pre and postconditions of a function specification cannot be empty"
            raise ValueError(msg)
        self.preconditions = sorted(preconditions)
        self.postconditions = sorted(postconditions)

    def __iter__(self) -> Iterator[list[str]]:
        """Return a singleton iterator that yields a list of this specification's clauses.

        This function allows tuple-based unpacking and assignments, e.g.,

            function_spec = ...
            pre, post = function_spec

        Returns:
            Iterator[list[str]]: An iterator comprising a tuple of pre and postconditions.
        """
        return iter((self.preconditions, self.postconditions))

    def __eq__(self, other: object) -> bool:
        """Return True iff the other specification comprises the same pre and postconditions.

        Args:
            other (object): The object to which to compare this specification to.

        Returns:
            bool: True iff the other specification comprises the same pre and postconditions,
                in the same order.
        """
        if not isinstance(other, FunctionSpecification):
            return False
        return (
            self.preconditions == other.preconditions
            and self.postconditions == other.postconditions
        )

    def __hash__(self) -> int:
        """Return this function specification's hash, based on its pre and postconditions.

        Returns:
            int: This function specification's hash, based on its pre and postconditions.
        """
        precondition_str = ",".join(self.preconditions)
        postcondition_str = ",".join(self.postconditions)
        return hash((precondition_str, postcondition_str))

    def get_prompt_str(self) -> str:
        """Return this function specification as it is summarized in a prompt.

        Returns:
            str: This function specification as it is summarized in a prompt.
        """
        pres = ", ".join(self.preconditions)
        posts = ", ".join(self.postconditions)
        return f"Preconditions:\n{pres}\nPostconditions:\n{posts}"

    def eq_setwise_inde_(self, other: object) -> bool:
        """Return True iff the other specification has the same pre and postconditions in any order.

        Args:
            other (object): The object to which to compare this specification to.

        Returns:
            bool: True iff the other specification comprises the same pre and postconditions,
                in any order.
        """
        if not isinstance(other, FunctionSpecification):
            return False
        return set(self.preconditions) == set(other.preconditions) and set(
            self.postconditions
        ) == set(other.postconditions)
