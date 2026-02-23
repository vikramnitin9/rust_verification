"""Transformation for inferring non-null preconditions from ensures clauses."""

from lark.tree import Meta

from translation.ast.cbmc_ast import (
    CBMCAst,
    EnsuresClause,
    IndexOp,
    Name,
    NeqOp,
    PtrMemberOp,
    RequiresClause,
)
from util import FunctionSpecification

from .specification_transformation import SpecificationTransformation


class InferNonNullPreconditionsFromEnsures(SpecificationTransformation):
    """Transformation for inferring non-null preconditions from ensures clauses."""

    def apply(self, specification: FunctionSpecification) -> list[FunctionSpecification]:
        """Return the result of applying this transformation to the given specification.

        Infer non-null preconditions from an ensures clause.

        For example, given a spec with the following ensures clause:

                    __CPROVER_ensures(a->b->c != NULL)

        The following preconditions are generated:

                    __CPROVER_requires(a != NULL)
                    __CPROVER_requires(a->b != NULL)

        Args:
            specification (FunctionSpecification): The specification to transform.

        Returns:
            list[FunctionSpecification]: The result of applying this transformation to the given
                specification.
        """
        precondition_asts, postcondition_asts = self._parse_specification(specification)
        non_null_check_exprs: list[NeqOp] = [
            non_null_check_expr
            for ast in postcondition_asts
            if (non_null_check_expr := self._get_non_null_check_expr(ast))
        ]
        precondition_exprs = []
        for neqop in non_null_check_exprs:
            non_null_check_subexprs = self._get_non_null_check_subexpressions(neqop.left)
            precondition_exprs = [
                NeqOp(subexpr, neqop.right) for subexpr in non_null_check_subexprs
            ]
        new_precondition_clauses = [
            # The `Meta` here shouldn't matter, since it isn't used when inserting specs.
            RequiresClause(meta=Meta(), expr=expr)
            for expr in precondition_exprs
        ]
        updated_precondition_clauses = precondition_asts + new_precondition_clauses
        return [
            FunctionSpecification(
                preconditions=[clause.to_string() for clause in updated_precondition_clauses],
                postconditions=specification.postconditions,
            )
        ]

    def _get_non_null_check_expr(self, ast: CBMCAst) -> NeqOp | None:
        """Return a non-null check expression in an ensures clause, if found.

        Args:
            ast (CBMCAst): The AST in which to search for a non-null check expression.

        Returns:
            NeqOp | None: The non-null check expression, if found.
        """
        if not isinstance(ast, EnsuresClause):
            return None
        match ast.expr:
            case NeqOp(left=PtrMemberOp(_, _), right=Name("NULL")):
                return ast.expr
            case NeqOp(left=IndexOp(value=PtrMemberOp(_, _)), right=Name("NULL")):
                return ast.expr
            case _:
                return None

    def _get_non_null_check_subexpressions(self, expr: CBMCAst) -> list[CBMCAst]:
        """Return the subexpressions from the left-hand side of a non-null check.

        Note: This function assumes the non-null check is of the form `LHS != NULL`.

        Args:
            expr (CBMCAst): The left-hand side of a non-null check.

        Returns:
            list[CBMCAst]: The subexpressions from the left-hand side of a non-null check.
        """
        result = []
        match expr:
            case PtrMemberOp(_, _):
                subexprs = expr.get_dereference_subexpressions()
                # Exclude self to avoid duplicating the existing ensures clause.
                result = [s for s in subexprs if s is not expr]
            case IndexOp(value=PtrMemberOp(_, _), index=_):
                subexprs = expr.value.get_dereference_subexpressions()
                result = [s for s in subexprs if s is not expr.value]
        return result
