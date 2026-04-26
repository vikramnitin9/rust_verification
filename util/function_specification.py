"""Class representing the pre and postconditions of a function."""

from collections.abc import Iterator
from dataclasses import dataclass
from string import Template
from textwrap import dedent


@dataclass
class FunctionSpecification:
    """Represents the pre and postconditions of a function, if present.

    Both the pre and postconditions array comprise strings that are CBMC macros.

    For example, a preconditions array may be: ["__CPROVER_requires(a < INT_MAX)"], while a
    postconditions array might be: ["__CPROVER_ensures(*b == old(a))"].

    Attributes:
        preconditions (tuple[str]): The preconditions of the function.
        postconditions (tuple[str]): The postconditions of the function.
    """

    preconditions: tuple[str]
    postconditions: tuple[str]

    def __init__(self, preconditions: list[str], postconditions: list[str]) -> None:
        """Create a new FunctionSpecification."""
        if not preconditions and not postconditions:
            msg = "Both the pre and postconditions of a function specification cannot be empty"
            raise ValueError(msg)
        self.preconditions = tuple(sorted(preconditions))  # ty: ignore # bug in ty?
        self.postconditions = tuple(sorted(postconditions))  # ty: ignore # bug in ty?

    def __iter__(self) -> Iterator[tuple[str]]:
        """Return a iterator that yields specification's clauses.

        The iterator has length two.  The first element is preconditions, the second is
        postconditions.

        This function allows tuple-based unpacking and assignments, e.g.,

            function_spec = ...
            pre, post = function_spec

        Returns:
            Iterator[tuple[str]]: A length-2 iterator: preconditions then postconditions.
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
        return hash((self.preconditions, self.postconditions))

    def get_prompt_str(self) -> str:
        """Return this function specification as it is summarized in a prompt.

        Returns:
            str: This function specification as it is summarized in a prompt.
        """
        pres = "\n".join(self.preconditions)
        posts = "\n".join(self.postconditions)
        template = dedent("""\
            <PRECONDITIONS>
            $preconditions
            </PRECONDITIONS>

            <POSTCONDITIONS>
            $postconditions
            </POSTCONDITIONS>
                      """)
        return Template(template).substitute(preconditions=pres, postconditions=posts)
