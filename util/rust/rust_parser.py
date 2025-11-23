"""Module for Rust parsing code."""

from dataclasses import dataclass
from typing import Protocol


@dataclass(frozen=True)
class RustFunction:
    """Lightweight representation of a Rust function.

    Attributes:
        name (str): The name of the function.
        param_to_type (dict[str, str]): The parameters (and their type) of the function.
    """

    name: str
    param_to_type: dict[str, str]


class RustParser(Protocol):
    """Protocol for classes that implement basic Rust source code parsing.

    Note: This is to provide a uniform interface for different Rust parsers (e.g.,
    tree-sitter-rust, ParseRust).
    """

    def get_functions_defined_in_file(self, file_name: str) -> list[RustFunction]:
        """Return the Rust functions defined in the file at the given path.

        Args:
            file_name (str): The name of the file to parse.

        Returns:
            list[RustFunction]: The Rust functions defined in the file with the given name.
        """
        ...
