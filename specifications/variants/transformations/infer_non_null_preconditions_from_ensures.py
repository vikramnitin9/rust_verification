"""Transformation for inferring non-null preconditions from expressions in an ensures clause."""

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
    """TODO: Document me."""

    def apply(self, specification: FunctionSpecification) -> list[FunctionSpecification]:
        """TODO: Document me.

        Args:
            specification (FunctionSpecification): _description_

        Returns:
            list[FunctionSpecification]: _description_
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
