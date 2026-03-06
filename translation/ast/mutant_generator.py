"""Class to create mutants of AST nodes."""

from __future__ import annotations

from typing import cast

from loguru import logger

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
        """Return a mutant of the given AST node by recursively applying mutation operations.

        Note: I'm not sure how useful this function is, since it applies multiple mutation operators
        in one go. It's probably better to use `get_single_point_mutants`.

        Args:
            node (CBMCAst): The AST node for which to create a mutant.

        Returns:
            CBMCAst: The mutant of the given AST node.
        """
        match node:
            # Handle special cases first, e.g., clauses, boolean literals, negations.
            case NegOp(value):
                # The mutant for a negation operation is to remove the negation and
                # do nothing else to the operand.
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
                # CBMC range expressions for quantifiers must be of the form
                # low <= INDEX_VAR < hi, so any mutants could modify the bounds, but not the
                # comparison operators.
                return quantifier_constructor(
                    decl, range_expr, self.get_mutant(expr), quantifier_constructor.kind
                )
            case _:
                return node

    def get_single_point_mutants(self, node: CBMCAst) -> list[CBMCAst]:
        """Return all single-point mutants of the given AST node.

        Each mutant in the result has exactly one operator changed, with all other
        nodes left unchanged.

        Args:
            node (CBMCAst): The AST node for which to create mutants.

        Returns:
            list[CBMCAst]: All single-point mutants of the given AST node.
        """
        mutants = []
        match node:
            case NegOp(operand):
                # Remove the negation.
                mutants.append(operand)
                mutants.extend(NegOp(m) for m in self.get_single_point_mutants(operand))
            case Bool(value):
                mutants.append(Bool(value=not value))
            case RequiresClause(meta, expr):
                mutants.extend(
                    [RequiresClause(meta, m) for m in self.get_single_point_mutants(expr)]
                )
            case EnsuresClause(meta, expr):
                mutants.extend(
                    [EnsuresClause(meta, m) for m in self.get_single_point_mutants(expr)]
                )
            case BinOp(left, right):
                mutation_candidates: list[type[BinOp]] = cast(
                    "list[type[BinOp]]", node.get_mutation_candidates()
                )
                # Mutate just the operator, keeping children unchanged.
                mutants.extend([mutation(left, right) for mutation in mutation_candidates])

                # Mutate just the left-hand side, keeping operator and right child.
                mutants.extend(
                    [
                        type(node)(left_mutant, right)
                        for left_mutant in self.get_single_point_mutants(left)
                    ]
                )

                # Mutate just the right-hand side, keeping operator and left child.
                mutants.extend(
                    [
                        type(node)(left, right_mutant)
                        for right_mutant in self.get_single_point_mutants(right)
                    ]
                )
            case Quantifier(decl, range_expr, expr, _):
                # Exists -> Forall, and vice-versa.
                mutation_candidates = cast("list[type[Quantifier]]", node.get_mutation_candidates())
                assert len(mutation_candidates) == 1, (
                    f"Expected quantifier node '{node}' to have exactly one mutation candidate"
                )
                candidate = mutation_candidates[0]
                mutants.append(candidate(decl, range_expr, expr, candidate.kind))

                # Mutate the body expression only, keeping this quantifier kind.
                mutants.extend(
                    [
                        type(node)(decl, range_expr, quantifier_body_mutant, node.kind)
                        for quantifier_body_mutant in self.get_single_point_mutants(expr)
                    ]
                )
            case _:
                logger.warning(f"No mutant(s) generated for '{node}'")
        return mutants
