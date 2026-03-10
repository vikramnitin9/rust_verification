"""Class to create mutants of AST nodes."""

from __future__ import annotations

from typing import cast

from loguru import logger

from translation.ast.cbmc_ast import (
    BinOp,
    Bool,
    CBMCAst,
    EnsuresClause,
    NotOp,
    Quantifier,
    RequiresClause,
)


class MutantGenerator:
    """Class to create mutants of AST nodes."""

    def get_mutant(self, node: CBMCAst) -> CBMCAst:
        """Return a mutant of the given AST node by recursively applying mutation operations.

        Note: I'm not sure how useful this function is, since it applies multiple mutation operators
        in one go. It's probably better to use `get_first_order_mutants`. Keeping it around for now
        in case it might be useful later.

        Args:
            node (CBMCAst): The AST node for which to create a mutant.

        Returns:
            CBMCAst: The mutant of the given AST node.
        """
        match node:
            # Handle special cases first, e.g., clauses, boolean literals, negations.
            case NotOp(value):
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
                replacement_operators: list[type[BinOp]] = cast(
                    "list[type[BinOp]]", node.get_mutation_candidates()
                )
                assert len(replacement_operators) >= 1, (
                    f"Expected at least one mutation candidate for a binary operation: {node}"
                )
                binop_constructor = replacement_operators[0]
                return binop_constructor(self.get_mutant(left), self.get_mutant(right))
            case Quantifier(decl, range_expr, expr, _):
                quantifier_mutation_candidates: list[type[Quantifier]] = cast(
                    "list[type[Quantifier]]", node.get_mutation_candidates()
                )
                assert len(quantifier_mutation_candidates) == 1, (
                    f"Expected exactly one mutation candidate for a quantifier expression: {node}"
                )
                replacement_qualifier = quantifier_mutation_candidates[0]
                # TODO: Should we also mutate the range expression?
                # CBMC range expressions for quantifiers must be of the form
                # low <= INDEX_VAR < hi, so any mutants could modify the bounds, but not the
                # comparison operators.
                return replacement_qualifier(
                    decl, range_expr, self.get_mutant(expr), replacement_qualifier.kind
                )
            case _:
                return node

    def get_first_order_mutants(self, node: CBMCAst) -> list[CBMCAst]:
        """Return all first-order mutants of the given AST node.

        Each mutant in the result has exactly one operator changed, with all other
        nodes left unchanged.

        Args:
            node (CBMCAst): The AST node for which to create mutants.

        Returns:
            list[CBMCAst]: All first-order mutants of the given AST node.
        """
        mutants = []
        match node:
            case NotOp(operand):
                # Remove the negation.
                mutants.append(operand)
                mutants.extend(
                    [
                        negated_operand_mutant
                        for operand_mutant in self.get_first_order_mutants(operand)
                        if (negated_operand_mutant := NotOp(operand_mutant)) not in mutants
                        # Discard the double-negation generated from negating boolean expressions.
                        and operand_mutant != node
                    ]
                )
            case Bool(value):
                mutants.append(Bool(value=not value))
            case RequiresClause(meta, expr):
                mutants.extend(
                    [RequiresClause(meta, m) for m in self.get_first_order_mutants(expr)]
                )
            case EnsuresClause(meta, expr):
                mutants.extend([EnsuresClause(meta, m) for m in self.get_first_order_mutants(expr)])
            case BinOp(left, right):
                replacement_operators: list[type[BinOp]] = cast(
                    "list[type[BinOp]]", node.get_mutation_candidates()
                )
                # Mutate just the operator, keeping children unchanged.
                mutants.extend([mutation(left, right) for mutation in replacement_operators])

                # Mutate just the left-hand side, keeping operator and right child.
                mutants.extend(
                    [
                        type(node)(left_mutant, right)
                        for left_mutant in self.get_first_order_mutants(left)
                    ]
                )

                # Mutate just the right-hand side, keeping operator and left child.
                mutants.extend(
                    [
                        type(node)(left, right_mutant)
                        for right_mutant in self.get_first_order_mutants(right)
                    ]
                )

                # Additional mutant for boolean expressions: negate the entire expression.
                if node.is_boolean_expression():
                    mutants.append(NotOp(node))
            case Quantifier(decl, range_expr, expr, _):
                # Exists -> Forall, and vice-versa.
                replacement_operators = cast(
                    "list[type[Quantifier]]", node.get_mutation_candidates()
                )
                assert len(replacement_operators) == 1, (
                    f"Expected quantifier node '{node}' to have exactly one mutation candidate"
                )
                candidate = replacement_operators[0]
                mutants.append(candidate(decl, range_expr, expr, candidate.kind))

                # Mutate the body expression only, keeping this quantifier kind.
                mutants.extend(
                    [
                        type(node)(decl, range_expr, quantifier_body_mutant, node.kind)
                        for quantifier_body_mutant in self.get_first_order_mutants(expr)
                    ]
                )
            case _:
                logger.debug(f"No mutant(s) generated for '{node}'")
        return mutants
