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
        return iter((self.preconditions, self.postconditions))
