"""Module for Rust parsing code."""

from dataclasses import dataclass
from types import MappingProxyType
from typing import Protocol


@dataclass
class RustTypeWrapper:
    """Lightweight representation of a Rust type.

    Attributes:
        rust_type (str): Represents the base Rust type (e.g., i32).
        is_reference (bool): True iff this is a reference type.
        is_mutable (bool): True iff this type is mutable.
    """

    rust_type: str
    is_reference: bool
    is_mutable: bool = False

    def declaration(self, variable_name: str, val: str) -> str:
        """Return a declaration (an inhabitant) for this type.

        Args:
            variable_name (str): The variable to declare for this type.
            val (str): The value to assign to the variable.

        Returns:
            str: The declaration for this type.
        """
        variable_and_type = f"{variable_name}: {self.rust_type}"
        mut = "mut " if self.is_mutable else ""
        return f"let {mut}{variable_and_type} = {val}"

    def to_argument(self, name: str) -> str:
        """Return the given name as if it is an argument to a function.

        This returns either:
            The name itself, or
            The name prefixed by "&mut " for a mutable reference.

        Args:
            name (str): The name to express as an argument to a function.

        Returns:
            str: The name expressed as an argument to function.
        """
        if self.is_mutable and self.is_reference:
            return f"&mut {name}"
        if not self.is_mutable and self.is_reference:
            return f"&{name}"
        return f"{name}"


@dataclass(frozen=True)
class RustFunction:
    """Lightweight representation of a Rust function.

    Attributes:
        name (str): The name of the function.
        param_to_type (MappingProxyType[str, RustTypeWrapper]): The parameters (and their type) of
            the function.
    """

    name: str
    param_to_type: MappingProxyType[str, RustTypeWrapper]


class RustParser(Protocol):
    """Protocol for classes that implement basic Rust source code parsing.

    Note: This is to provide a uniform interface for different Rust parsers (e.g.,
    tree-sitter-rust, ParseRust).
    """

    def get_functions_defined_in_file(self, file_name: str) -> dict[str, RustFunction]:
        """Return the Rust functions defined in the file at the given path mapped to their name.

        Args:
            file_name (str): The name of the file to parse.

        Returns:
            dict[str, RustFunction]: The Rust functions defined in the file with the given name.
        """
        ...
