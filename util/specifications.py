from dataclasses import dataclass
from typing import Iterator


@dataclass
class Specifications:
    preconditions: list[str]
    postconditions: list[str]

    def __iter__(self) -> Iterator[list[str]]:
        return iter((self.preconditions, self.postconditions))
