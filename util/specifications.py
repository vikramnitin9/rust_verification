from dataclasses import dataclass
from typing import Iterator


@dataclass
class Specifications:
    """Represents the pre and postconditions of a function, if present.

    Attributes:
        preconditions (list[str]): The preconditions of the function.
        postconditions (list[str]): The postconditions of the function.
    """

    preconditions: list[str]
    postconditions: list[str]

    def __iter__(self) -> Iterator[list[str]]:
        """Return an iterator comprising a tuple of this specification's pre and postconditions.

        Returns:
            Iterator[list[str]]: An iterator comprising a tuple of this specification's pre and postconditions.
        """
        return iter((self.preconditions, self.postconditions))
