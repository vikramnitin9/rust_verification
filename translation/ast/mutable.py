"""Class to represent AST nodes from which mutant nodes can be generated."""

from typing import Protocol

from .cbmc_ast import CBMCAst


class Mutable(Protocol):
    """Class to represent AST nodes from which mutant nodes can be generated."""

    def get_mutation_candidates(self) -> list[type[CBMCAst]]:
        """Return the type(s) of CBMCAst nodes that this node may be mutated into.

        Returns:
            list[type[CBMCAst]]: The type(s) of CBMCAst nodes that this node may be mutated into.
        """
        return []
