"""Class to create mutants of AST nodes."""

from typing import cast

from translation.ast.cbmc_ast import (
    BinOp,
    Bool,
    CBMCAst,
    EnsuresClause,
    NegOp,
    Quantifier,
    RequiresClause,
)


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
            # Handle special cases first, e.g., clauses, boolean literals, negations.
            case NegOp(value):
                return value
            case Bool(value):
                return Bool(not value)
            case RequiresClause(meta, expr):
                return RequiresClause(meta=meta, expr=self.get_mutant(expr))
            case EnsuresClause(meta, expr):
                return EnsuresClause(meta=meta, expr=self.get_mutant(expr))
            case BinOp(left, right):
                # There is only one mutation candidate, for now.
                binop_mutation_candidates: list[type[BinOp]] = cast(
                    "list[type[BinOp]]", node.get_mutation_candidates()
                )
                assert len(binop_mutation_candidates) >= 1, (
                    f"Expected at least one mutation candidate for a binary operation: {node}"
                )
                binop_constructor = binop_mutation_candidates[0]
                return binop_constructor(self.get_mutant(left), self.get_mutant(right))
            case Quantifier(decl, range_expr, expr, _):
                quantifier_mutation_candidates: list[type[Quantifier]] = cast(
                    "list[type[Quantifier]]", node.get_mutation_candidates()
                )
                assert len(quantifier_mutation_candidates) == 1, (
                    f"Expected exactly one mutation candidate for a quantifier expression: {node}"
                )
                quantifier_constructor = quantifier_mutation_candidates[0]
                # TODO: Should we also mutate the range expression?
                return quantifier_constructor(
                    decl, range_expr, self.get_mutant(expr), quantifier_constructor.kind
                )
            case _:
                return node
