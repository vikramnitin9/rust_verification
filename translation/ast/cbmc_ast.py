# mypy: ignore-errors
# Ideally we'd like to type check this file, but Lark does not yet support type annotations.
# ruff: noqa

#
# This is a manually-written mapping of cbmc.txt to the AST representation used to
# parse CBMC specifications into the representation we work with in this codebase.
#

from __future__ import annotations
import sys
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Any, Protocol

from lark import Transformer, ast_utils, v_args
from lark.tree import Meta


class Mutable(Protocol):
    """Class to represent AST nodes from which mutant nodes can be generated."""

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        """Return the type(s) of CbmcAst nodes that this node may be mutated into.

        Returns:
            list[type[CbmcAst]]: The type(s) of CbmcAst nodes that this node may be mutated into.
        """
        return []


class CbmcAst(ast_utils.Ast, Mutable):
    pass

    def is_boolean_expression(self) -> bool:
        return False


@dataclass(frozen=True)
class RequiresClause(CbmcAst, ast_utils.WithMeta):
    meta: Meta
    expr: Any


@dataclass(frozen=True)
class EnsuresClause(CbmcAst, ast_utils.WithMeta):
    meta: Meta
    expr: Any


@dataclass(frozen=True)
class ExprList(CbmcAst, ast_utils.AsList):
    items: tuple[CbmcAst, ...]


@dataclass(frozen=True)
class AssignsTargetList(CbmcAst):
    items: ExprList


@dataclass(frozen=True)
class Assigns(CbmcAst):
    """Definition for a top-level __CPROVER_assigns clause."""

    condition: Any | None
    targets: AssignsTargetList


@dataclass(frozen=True)
class FreesTargetList(CbmcAst):
    items: ExprList


@dataclass(frozen=True)
class Frees(CbmcAst):
    """Definition for a top-level __CPROVER_frees clause."""

    condition: Any | None
    targets: FreesTargetList


@dataclass(frozen=True)
class ObjectWhole(CbmcAst):
    """Represents a __CPROVER_object_whole(expr) assigns target designator."""

    expr: Any


@dataclass(frozen=True)
class ObjectFrom(CbmcAst):
    """Represents a __CPROVER_object_from(expr) assigns target designator."""

    expr: Any


@dataclass(frozen=True)
class ObjectUpto(CbmcAst):
    """Represents a __CPROVER_object_upto(ptr, size) assigns target designator.

    Designates the range of bytes starting at *ptr up to (but not including)
    byte at offset size.
    """

    ptr: Any
    size: Any


@dataclass(frozen=True)
class TypedTarget(CbmcAst):
    """Represents a __CPROVER_typed_target(lvalue) assigns target designator.

    Designates the same memory location as lvalue but restricts assignability
    to writes of the same type as lvalue.
    """

    expr: Any


@dataclass(frozen=True)
class Freeable(CbmcAst):
    """Represents a __CPROVER_freeable(ptr) frees target designator.

    Specifies that ptr is freeable in the context of the enclosing frees clause.
    """

    expr: Any


@dataclass(frozen=True)
class Name(CbmcAst):
    name: str


@dataclass(frozen=True)
class Number(CbmcAst):
    value: Any


@dataclass(frozen=True)
class Bool(CbmcAst):
    value: bool

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class StringLit(CbmcAst):
    value: str


@dataclass(frozen=True)
class BinOp(ABC, CbmcAst):
    left: Any
    right: Any

    @abstractmethod
    def operator(self) -> str:
        raise NotImplementedError("Subclasses must implement this method")


@dataclass(frozen=True)
class OrOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "||"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [AndOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class AndOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "&&"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [OrOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class EqOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "=="

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [NeqOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class NeqOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "!="

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [EqOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class LtOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "<"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [GeOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class LeOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "<="

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [GtOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class GtOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return ">"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [LeOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class GeOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return ">="

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [LtOp]

    def is_boolean_expression(self) -> bool:
        return True


@dataclass(frozen=True)
class AddOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "+"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [SubOp]


@dataclass(frozen=True)
class SubOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "-"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [AddOp]


@dataclass(frozen=True)
class MulOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "*"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [DivOp]


@dataclass(frozen=True)
class DivOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "/"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [MulOp]


@dataclass(frozen=True)
class ModOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "%"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        # Default to division. Modulo has no inverse.
        return [DivOp]


@dataclass(frozen=True)
class NotOp(CbmcAst):
    operand: Any


@dataclass(frozen=True)
class AddrOp(CbmcAst):
    operand: Any


@dataclass(frozen=True)
class DerefOp(CbmcAst):
    operand: Any


@dataclass(frozen=True)
class NegOp(CbmcAst):
    operand: Any


@dataclass(frozen=True)
class PosOp(CbmcAst):
    operand: Any


@dataclass(frozen=True)
class MemberOp(CbmcAst):
    value: CbmcAst
    attr: CbmcAst


@dataclass(frozen=True)
class PtrMemberOp(CbmcAst):
    value: Any
    attr: str


@dataclass(frozen=True)
class IndexOp(CbmcAst):
    value: Any
    index: Any


@dataclass(frozen=True)
class CallOp(CbmcAst):
    func: CbmcAst
    args: CbmcAst


@dataclass(frozen=True)
class ArgList(CbmcAst, ast_utils.AsList):
    items: tuple[Any, ...]


class TypeNode(CbmcAst):
    pass


@dataclass(frozen=True)
class BuiltinType(TypeNode):
    # e.g., "int", "unsigned", "signed", "bool", "char", "float", "double"
    BUILT_IN_TYPES = {"int", "unsigned", "signed", "char", "long", "float", "double"}
    name: str


@dataclass(frozen=True)
class NamedType(TypeNode):
    # typedef or user-defined type
    name: Name


@dataclass(frozen=True)
class QuantifierDecl(CbmcAst):
    typenode: TypeNode
    name: Name


@dataclass(frozen=True)
class Quantifier(CbmcAst):
    decl: QuantifierDecl
    range_expr: Any
    expr: Any
    kind: str = ""


@dataclass(frozen=True)
class ForallExpr(Quantifier):
    kind: str = "forall"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [ExistsExpr]


@dataclass(frozen=True)
class ExistsExpr(Quantifier):
    kind: str = "exists"

    def get_mutation_candidates(self) -> list[type[CbmcAst]]:
        return [ForallExpr]


@dataclass(frozen=True)
class Old(CbmcAst):
    expr: Any


@dataclass(frozen=True)
class ReturnValue(CbmcAst):
    pass


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

    def STRING(self, tok: Any) -> StringLit:
        return StringLit(value=str(tok))

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
    def assigns_clause(self, content):  # type: ignore[no-untyped-def]
        # The content is already an Assigns from assigns_empty/assigns_unconditional/assigns_conditional
        return content

    @v_args(inline=True)
    def assigns_empty(self):  # type: ignore[no-untyped-def]
        empty_tuple: tuple[CbmcAst, ...] = ()
        return Assigns(condition=None, targets=AssignsTargetList(items=ExprList(empty_tuple)))

    @v_args(inline=True)
    def assigns_unconditional(self, expr_list):  # type: ignore[no-untyped-def]
        # Validate that all targets are side-effect free
        self._validate_side_effect_free(expr_list)
        return Assigns(condition=None, targets=AssignsTargetList(items=expr_list))

    @v_args(inline=True)
    def assigns_conditional(self, condition, expr_list):  # type: ignore[no-untyped-def]
        # Validate that all targets are side-effect free
        self._validate_side_effect_free(expr_list)
        return Assigns(condition=condition, targets=AssignsTargetList(items=expr_list))

    def _validate_side_effect_free(self, expr: Any) -> None:
        """Raise TypeError if an expression contains a function call.

        This is a best-effort attempt to validate that an expression is side-effect free by checking
        for the presence of function calls in an expression. Some functions are obviously
        side-effect free, but this information requires a more complicated analysis to obtain.

        Args:
            expr (Any): The expression to validate.

        Raises:
            TypeError: Raised when a function call appears in the expression.
        """
        if isinstance(expr, CallOp):
            msg = f"Function calls not allowed in assigns targets: {expr}"
            raise TypeError(msg)
        if isinstance(expr, (ObjectWhole, ObjectFrom, TypedTarget)):
            self._validate_side_effect_free(expr.expr)
        if isinstance(expr, ObjectUpto):
            self._validate_side_effect_free(expr.ptr)
            self._validate_side_effect_free(expr.size)
        if isinstance(expr, ExprList):
            for e in expr.items:
                self._validate_side_effect_free(e)
        # Check subexpressions
        if hasattr(expr, "items"):
            for e in expr.items:
                self._validate_side_effect_free(e)
        if hasattr(expr, "value"):
            self._validate_side_effect_free(expr.value)
        if hasattr(expr, "index"):
            self._validate_side_effect_free(expr.index)
        if hasattr(expr, "left"):
            self._validate_side_effect_free(expr.left)
        if hasattr(expr, "right"):
            self._validate_side_effect_free(expr.right)
        if hasattr(expr, "operand"):
            self._validate_side_effect_free(expr.operand)

    def _validate_frees_target(self, expr: Any) -> None:
        """Raise TypeError if a frees target expression contains nested side effects.

        Unlike assigns targets, frees targets may be top-level calls to user-defined void
        functions that are themselves side effect free and deterministic (per the CBMC docs).
        A top-level CallOp is therefore permitted, but its arguments must be side-effect free.
        All other targets (lvalue expressions, __CPROVER_freeable) follow the same rules as
        assigns targets.

        Args:
            expr (Any): A single frees target expression.

        Raises:
            TypeError: Raised when a nested side effect (function call) is found.
        """
        if isinstance(expr, ExprList):
            for e in expr.items:
                self._validate_frees_target(e)
        elif isinstance(expr, CallOp):
            # The top-level call itself is allowed; validate its arguments.
            # This is a best-effort check; it is difficult to know at compile-time whether a
            # function is side-effect free.
            if expr.args is not None:
                self._validate_side_effect_free(expr.args)
        elif isinstance(expr, Freeable):
            self._validate_side_effect_free(expr.expr)
        else:
            self._validate_side_effect_free(expr)

    @v_args(inline=True)
    def object_whole_expr(self, expr):  # type: ignore[no-untyped-def]
        return ObjectWhole(expr=expr)

    @v_args(inline=True)
    def object_from_expr(self, expr):  # type: ignore[no-untyped-def]
        return ObjectFrom(expr=expr)

    @v_args(inline=True)
    def object_upto_expr(self, ptr, size):  # type: ignore[no-untyped-def]
        return ObjectUpto(ptr=ptr, size=size)

    @v_args(inline=True)
    def typed_target_expr(self, expr):  # type: ignore[no-untyped-def]
        return TypedTarget(expr=expr)

    @v_args(inline=True)
    def freeable_expr(self, expr):  # type: ignore[no-untyped-def]
        return Freeable(expr=expr)

    @v_args(inline=True)
    def frees_clause(self, content):  # type: ignore[no-untyped-def]
        # The content is already a Frees from frees_empty/frees_unconditional/frees_conditional
        return content

    @v_args(inline=True)
    def frees_empty(self):  # type: ignore[no-untyped-def]
        empty_tuple: tuple[CbmcAst, ...] = ()
        return Frees(condition=None, targets=FreesTargetList(items=ExprList(empty_tuple)))

    @v_args(inline=True)
    def frees_unconditional(self, expr_list):  # type: ignore[no-untyped-def]
        # Top-level function calls are valid frees targets (user-defined parametric freeable sets),
        # but their arguments must still be side-effect free.
        self._validate_frees_target(expr_list)
        return Frees(condition=None, targets=FreesTargetList(items=expr_list))

    @v_args(inline=True)
    def frees_conditional(self, condition, expr_list):  # type: ignore[no-untyped-def]
        # Top-level function calls are valid frees targets (user-defined parametric freeable sets),
        # but their arguments must still be side-effect free.
        self._validate_frees_target(expr_list)
        return Frees(condition=condition, targets=FreesTargetList(items=expr_list))

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
