"""Transformation where expressions in preconditions are moved to assigns and ensures clauses."""

from translation.ast.cbmc_ast import (
    AndOp,
    Assigns,
    CBMCAst,
    EnsuresClause,
    OrOp,
    RequiresClause,
    ToAst,
)
from translation.parser import Parser
from util import FunctionSpecification

from .specification_transformation import SpecificationTransformation


class MovePreconditionsToAssignsAndEnsures(SpecificationTransformation):
    """Transformation where precondition expressions are moved to assigns and ensures clauses.

    There are cases where a specification might contain preconditions that are *too* strong,
    effectively weakening the entire specification. This transformation moves precondition
    expressions into conditions for assigns clauses and disjunctions for ensures clauses.
    """

    def __init__(self) -> None:
        """Create a new MovePreconditionsToAssignsAndEnsures."""
        self._parser = Parser(
            path_to_grammar_defn="translation/grammar/cbmc.txt",
            start="cbmc_clause",
            transformer=ToAst(),
        )

    def apply(self, specification: FunctionSpecification) -> FunctionSpecification:
        """Return the result of applying this transformation to the given specification.

        Move the expressions in preconditions clauses into:
            * Conditions for any assigns clauses.
            * Disjunctions with any ensures clauses.

        Args:
            specification (FunctionSpecification): The specification to transform.

        Returns:
            FunctionSpecification: The transformed specification.
        """
        preconditions_ast, postconditions_ast = self._parse_specification(specification)

        # If there are no postconditions, return unchanged.
        if not postconditions_ast:
            return specification

        # Extract the inner expressions from each RequiresClause.
        precondition_exprs: list[CBMCAst] = [
            clause.expr for clause in preconditions_ast if isinstance(clause, RequiresClause)
        ]

        # If there are no precondition expressions, return unchanged.
        if not precondition_exprs:
            return specification

        new_postconditions: list[str] = []
        for post_ast in postconditions_ast:
            if isinstance(post_ast, EnsuresClause):
                # Build disjunction: !pre1 || !pre2 || ... || ensures_expr
                result: CBMCAst = precondition_exprs[0].negate()
                for pre_expr in precondition_exprs[1:]:
                    result = OrOp(left=result, right=pre_expr.negate())
                result = OrOp(left=result, right=post_ast.expr)
                new_postconditions.append(
                    EnsuresClause(meta=post_ast.meta, expr=result).to_string()
                )
            elif isinstance(post_ast, Assigns):
                # Add conjunction of all precondition expressions as a condition.
                condition: CBMCAst = precondition_exprs[0]
                for pre_expr in precondition_exprs[1:]:
                    condition = AndOp(left=condition, right=pre_expr)
                # If there's already a condition, AND it with the preconditions.
                if post_ast.condition:
                    condition = AndOp(left=post_ast.condition, right=condition)
                new_assigns = Assigns(condition=condition, targets=post_ast.targets)
                new_postconditions.append(new_assigns.to_string())
            else:
                new_postconditions.append(post_ast.to_string())

        return FunctionSpecification(
            preconditions=[],
            postconditions=new_postconditions,
        )
