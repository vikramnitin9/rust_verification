"""Transformation for inferring preconditions from expressions in an ensures clause."""

from typing import cast

from translation.ast.cbmc_ast import (
    CBMCAst,
    EnsuresClause,
    Meta,
    Name,
    NeqOp,
    PtrMemberOp,
    RequiresClause,
)
from util import FunctionSpecification

from .specification_transformation import SpecificationTransformation


class InferPreconditionsFromEnsures(SpecificationTransformation):
    """TODO: Document me."""

    def apply(self, specification: FunctionSpecification) -> list[FunctionSpecification]:
        """TODO: Document me.

        Args:
            specification (FunctionSpecification): _description_

        Returns:
            list[FunctionSpecification]: _description_
        """
        _, postcondition_asts = self._parse_specification(specification)
        print(postcondition_asts)
        non_null_check_exprs = [
            non_null_check_expr
            for ast in postcondition_asts
            if (non_null_check_expr := self._get_non_null_check_expr(ast))
        ]
        precondition_exprs = []
        for expr in non_null_check_exprs:
            match expr:
                case NeqOp(lhs, rhs):
                    non_null_check_subexprs = self._get_non_null_check_subexpressions(lhs)
                    precondition_exprs = [
                        NeqOp(subexpr, rhs) for subexpr in non_null_check_subexprs
                    ]
                case _:
                    pass
        # TODO: How to obtain the appropriate meta...
        new_precondition_clauses = [
            RequiresClause(meta=Meta(), expr=expr) for expr in precondition_exprs
        ]
        print(new_precondition_clauses)
        return []  # stub.

    def _get_non_null_check_expr(self, ast: CBMCAst) -> NeqOp | None:
        if not isinstance(ast, EnsuresClause):
            return None
        match ast.expr:
            case NeqOp(left=PtrMemberOp(_, _), right=Name("NULL")):
                return ast.expr
            case _:
                return None

    def _get_non_null_check_subexpressions(self, expr: CBMCAst) -> list[CBMCAst]:
        if ptr_member_op := cast("PtrMemberOp", expr):
            return ptr_member_op.get_dereference_subexpressions()
        return []
