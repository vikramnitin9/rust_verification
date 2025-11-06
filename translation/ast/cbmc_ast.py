# mypy: ignore-errors
# Ideally we'd like to type check this file, but Lark does not yet support type annotations.
# ruff: noqa

#
# This is a manually-written mapping of cbmc.txt to the AST representation used to
# parse CBMC specifications into the representation we work with in this codebase.
#

import sys
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Any

from lark import Transformer, ast_utils, v_args
from lark.tree import Meta


class CBMCAst(ast_utils.Ast):
    pass


@dataclass
class RequiresClause(CBMCAst, ast_utils.WithMeta):
    meta: Meta
    expr: Any


@dataclass
class EnsuresClause(CBMCAst, ast_utils.WithMeta):
    meta: Meta
    expr: Any


@dataclass
class Name(CBMCAst):
    name: str


@dataclass
class Number(CBMCAst):
    value: Any


@dataclass
class Bool(CBMCAst):
    value: bool


@dataclass
class StringLit(CBMCAst):
    value: str


@dataclass
class BinOp(ABC, CBMCAst):
    left: Any
    right: Any

    @abstractmethod
    def operator(self) -> str:
        raise NotImplementedError("Subclasses must implement this method")


@dataclass
class OrOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "||"


@dataclass
class AndOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "&&"


@dataclass
class EqOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "=="


@dataclass
class NeqOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "!="


@dataclass
class LtOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "<"


@dataclass
class LeOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "<="


@dataclass
class GtOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return ">"


@dataclass
class GeOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return ">="


@dataclass
class AddOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "+"


@dataclass
class SubOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "-"


@dataclass
class MulOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "*"


@dataclass
class DivOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "/"


@dataclass
class ModOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "%"


@dataclass
class NotOp(CBMCAst):
    operand: Any


@dataclass
class AddrOp(CBMCAst):
    operand: Any


@dataclass
class DerefOp(CBMCAst):
    operand: Any


@dataclass
class NegOp(CBMCAst):
    operand: Any


@dataclass
class PosOp(CBMCAst):
    operand: Any


@dataclass
class MemberOp(CBMCAst):
    value: CBMCAst
    attr: CBMCAst


@dataclass
class PtrMemberOp(CBMCAst):
    value: Any
    attr: str


@dataclass
class IndexOp(CBMCAst):
    value: Any
    index: Any


@dataclass
class CallOp(CBMCAst):
    func: CBMCAst
    args: CBMCAst


@dataclass
class ArgList(CBMCAst, ast_utils.AsList):
    items: list[Any]


class TypeNode(CBMCAst):
    pass


@dataclass
class BuiltinType(TypeNode):
    # e.g., "int", "unsigned", "signed", "bool", "char", "float", "double"
    BUILT_IN_TYPES = {"int", "unsigned", "signed", "char", "long", "float", "double"}
    name: str


@dataclass
class NamedType(TypeNode):
    # typedef or user-defined type
    name: Name


@dataclass
class QuantifierDecl(CBMCAst):
    typenode: TypeNode
    name: Name


@dataclass
class Quantifier(CBMCAst):
    decl: QuantifierDecl
    range_expr: Any
    expr: Any
    kind: str = ""


@dataclass
class ForallExpr(Quantifier):
    kind: str = "forall"
    pass


@dataclass
class ExistsExpr(Quantifier):
    kind: str = "exists"
    pass


@dataclass
class Old(CBMCAst):
    expr: Any


@dataclass
class ReturnValue(CBMCAst):
    pass


@dataclass
class ExprList(CBMCAst, ast_utils.AsList):
    items: list[CBMCAst]


@dataclass
class AssignsTargetList(CBMCAst):
    items: ExprList


@dataclass
class AssignsExpr(CBMCAst):
    condition: Any | None
    targets: AssignsTargetList


class _ToAst(Transformer):
    def NAME(self, tok: Any) -> Name | Bool:
        txt = str(tok)
        # CBMC sometimes emits boolean literals as the names 'true'/'false'.
        # Prefer producing Bool AST nodes for these tokens instead of Name.
        low = txt.lower()
        if low == "true":
            return Bool(value=True)
        if low == "false":
            return Bool(value=False)
        return Name(name=txt)

    def NUMBER(self, tok: Any) -> Number:
        txt = str(tok)
        float_characters = [".", "e", "E"]
        if any(c in txt for c in float_characters):
            return Number(value=float(txt))
        return Number(value=int(txt))

    def BOOL(self, tok: Any) -> Bool:
        return Bool(value=(str(tok) == "1"))

    def TYPE_KW(self, tok: Any) -> BuiltinType:  # builtin type keyword
        return BuiltinType(name=str(tok))

    # Build TypeNode: keyword already mapped to BuiltinType; NAME -> NamedType
    @v_args(inline=True)
    def typ(self, t):  # type: ignore[no-untyped-def]
        if isinstance(t, Name):
            if t.name in BuiltinType.BUILT_IN_TYPES:
                return BuiltinType(name=t.name)
            return NamedType(name=t)
        # t is a BuiltinType from TYPE_KW
        return t

    @v_args(inline=True)
    def quantifier_decl(self, a, b):  # type: ignore[no-untyped-def]
        # Grammar: quantifier_decl : typ NAME
        if isinstance(a, TypeNode) and isinstance(b, Name):
            return QuantifierDecl(typenode=a, name=b)
        if isinstance(a, Name) and isinstance(b, TypeNode):  # tolerate reversed order
            return QuantifierDecl(typenode=b, name=a)
        raise ValueError(f"Unexpected quantifier_decl children: {type(a)} {type(b)}")

    @v_args(inline=True)
    def assigns_empty(self):  # type: ignore[no-untyped-def]
        return AssignsExpr(condition=None, targets=AssignsTargetList())

    @v_args(inline=True)
    def assigns_unconditional(self, *targets):  # type: ignore[no-untyped-def]
        target_list = list(targets)
        # The targets must be side-effect free.
        for target in target_list:
            self._validate_side_effect_free(target)
        return AssignsExpr(condition=None, targets=AssignsTargetList(*target_list))

    @v_args(inline=True)
    def assigns_conditional(self, condition, *targets):  # type: ignore[no-untyped-def]
        target_list = list(targets)
        # Validate targets are side-effect free
        for target in target_list:
            self._validate_side_effect_free(target)
        return AssignsExpr(condition=condition, targets=AssignsTargetList(*target_list))

    def _validate_side_effect_free(self, expr: Any) -> None:
        """Raise ValueError if an expression contains a function call.

        This is a best-effort attempt to validate that an expression is side-effect free by checking
        for the presence of function calls in an expression. Some functions are obviously
        side-effect free, but this information requires a more complicated analysis to obtain.

        Args:
            expr (Any): The expression to validate.

        Raises:
            ValueError: Raised when a function call appears in the expression.
        """
        if isinstance(expr, CallOp):
            raise ValueError(f"Function calls not allowed in assigns targets: {expr}")
        # Check subexpressions.
        if hasattr(expr, "value"):
            self._validate_side_effect_free(expr.value)
        if hasattr(expr, "index"):
            self._validate_side_effect_free(expr.index)
        if hasattr(expr, "left"):
            self._validate_side_effect_free(expr.left)
        if hasattr(expr, "right"):
            self._validate_side_effect_free(expr.right)

    @v_args(inline=True)
    def assigns_target_list(self, *targets):  # type: ignore[no-untyped-def]
        return list(targets)

    # Keep start inline
    @v_args(inline=True)
    def start(self, x):  # type: ignore[no-untyped-def]
        return x


def ToAst() -> Transformer:
    """Return a Lark Transformer instance which converts parse trees
    into instances of the AST dataclasses defined above.

    Callers use `ToAst()` (no args) so this function returns the configured
    transformer instance.
    """
    return ast_utils.create_transformer(sys.modules[__name__], _ToAst())
