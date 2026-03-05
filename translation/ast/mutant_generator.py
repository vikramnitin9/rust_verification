"""Class to create mutants of AST nodes."""

from translation.ast.cbmc_ast import Bool, CBMCAst


class MutantGenerator:
    """Class to create mutants of AST nodes."""

    def get_mutant(self, node: CBMCAst) -> CBMCAst:
        """Return a mutant of the given AST node.

        Args:
            node (CBMCAst): The AST node for which to create a mutant.

        Returns:
            CBMCAst: The mutant of the given AST node.
        """
        match node:
            # Handle special cases first, e.g., clauses and literals.
            case Bool(value):
                return Bool(not value)
            case _:
                return node
