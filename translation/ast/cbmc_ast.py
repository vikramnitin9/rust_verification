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
    def to_string(self) -> str:
        """Convert this AST node to its string representation.

        Returns:
            str: The string form of this AST node.
        """
        raise NotImplementedError(f"to_string not implemented for {type(self).__name__}")

    def negate(self) -> "CBMCAst":
        """Return the negation of this AST node.

        Note: This is a general case that avoids crashes at run-time (but may not be sound).

        Returns:
            CBMCAst: The negation of this AST node.
        """
        return NotOp(self)


def _to_str(node: Any) -> str:
    """Convert an AST node or primitive value to a string.

    Args:
        node: A CBMCAst node or a primitive value.

    Returns:
        str: The string representation.
    """
    if node is None:
        return ""
    if isinstance(node, CBMCAst):
        return node.to_string()
    return str(node)


@dataclass
class RequiresClause(CBMCAst, ast_utils.WithMeta):
    meta: Meta
    expr: Any

    def to_string(self) -> str:
        return f"__CPROVER_requires({_to_str(self.expr)})"


@dataclass
class EnsuresClause(CBMCAst, ast_utils.WithMeta):
    meta: Meta
    expr: Any

    def to_string(self) -> str:
        return f"__CPROVER_ensures({_to_str(self.expr)})"


@dataclass
class ExprList(CBMCAst, ast_utils.AsList):
    items: list[CBMCAst]

    def to_string(self) -> str:
        return ", ".join(_to_str(item) for item in self.items)


@dataclass
class AssignsTargetList(CBMCAst):
    items: ExprList

    def to_string(self) -> str:
        return _to_str(self.items)


@dataclass
class Assigns(CBMCAst):
    """Definition for a top-level __CPROVER_assigns clause."""

    condition: Any | None
    targets: AssignsTargetList

    def to_string(self) -> str:
        targets = _to_str(self.targets)
        if self.condition:
            cond = _to_str(self.condition)
            return f"__CPROVER_assigns({cond} : {targets})"
        return f"__CPROVER_assigns({targets})"


@dataclass
class Name(CBMCAst):
    name: str

    def to_string(self) -> str:
        return self.name


@dataclass
class Number(CBMCAst):
    value: Any

    def to_string(self) -> str:
        return str(self.value)


@dataclass
class Bool(CBMCAst):
    value: bool

    def to_string(self) -> str:
        return "1" if self.value else "0"


@dataclass
class StringLit(CBMCAst):
    value: str

    def to_string(self) -> str:
        return self.value


@dataclass
class BinOp(ABC, CBMCAst):
    left: Any
    right: Any

    @abstractmethod
    def operator(self) -> str:
        raise NotImplementedError("Subclasses must implement this method")

    def to_string(self) -> str:
        return f"({_to_str(self.left)} {self.operator()} {_to_str(self.right)})"


@dataclass
class LogicalBinOp(BinOp):
    def __init__(self, left: Any, right: Any):
        self.left = left
        self.right = right

    def get_operand_atoms(self) -> list[CBMCAst]:
        match self:
            case LogicalBinOp(left=LogicalBinOp(_, _), right=LogicalBinOp(_, _)):
                return self.left.get_operand_atoms() + self.right.get_operand_atoms()
            case LogicalBinOp(left=LogicalBinOp(_, _), right=rhs):
                return self.left.get_operand_atoms() + [rhs]
            case LogicalBinOp(left=lhs, right=LogicalBinOp(_, _)):
                return [lhs] + self.right.get_operand_atoms()
            case _:
                return [self.left, self.right]

    def get_operand_prefixes(self) -> list[CBMCAst]:
        """Return the strict prefixes of this logical binary operation.

        E.g., Given `a || b || c || d`, return `a`, `a || b`, `a || b || c`.

        Args:
            logical_binop (LogicalBinOp): The logical binary operation for which to return prefixes.

        Returns:
            list[CBMCAst]: The strict prefixes of the logical binary operation.
        """
        operands = self.get_operand_atoms()
        if len(operands) <= 1:
            return []
        variants: list[CBMCAst] = []
        for i in range(1, len(operands)):
            prefix = operands[:i]
            variants.append(self.apply(prefix))
        return variants

    def apply(self, operands: list[CBMCAst]) -> "LogicalBinOp | CBMCAst":
        if len(operands) == 1:
            return operands[0]
        result = operands[0]
        for operand in operands[1:]:
            result = type(self)(left=result, right=operand)
        return result


@dataclass
class OrOp(LogicalBinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "||"

    def negate(self) -> CBMCAst:
        return AndOp(left=self.left.negate(), right=self.right.negate())


@dataclass
class AndOp(LogicalBinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "&&"

    def negate(self) -> CBMCAst:
        return OrOp(left=self.left.negate(), right=self.right.negate())


@dataclass
class EqOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "=="

    def negate(self) -> CBMCAst:
        return NeqOp(left=self.left, right=self.right)


@dataclass
class NeqOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "!="

    def negate(self) -> CBMCAst:
        return EqOp(left=self.left, right=self.right)


@dataclass
class LtOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "<"

    def negate(self) -> CBMCAst:
        return GeOp(left=self.left, right=self.right)


@dataclass
class LeOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return "<="

    def negate(self) -> CBMCAst:
        return GtOp(left=self.left, right=self.right)


@dataclass
class GtOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return ">"

    def negate(self) -> CBMCAst:
        return LeOp(left=self.left, right=self.right)


@dataclass
class GeOp(BinOp):
    left: Any
    right: Any

    def operator(self) -> str:
        return ">="

    def negate(self) -> CBMCAst:
        return LtOp(left=self.left, right=self.right)


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

    def to_string(self) -> str:
        return f"!{_to_str(self.operand)}"

    def negate(self) -> CBMCAst:
        return self.operand


@dataclass
class AddrOp(CBMCAst):
    operand: Any

    def to_string(self) -> str:
        return f"&{_to_str(self.operand)}"


@dataclass
class DerefOp(CBMCAst):
    operand: Any

    def to_string(self) -> str:
        return f"*{_to_str(self.operand)}"


@dataclass
class NegOp(CBMCAst):
    operand: Any

    def to_string(self) -> str:
        return f"-({_to_str(self.operand)})"


@dataclass
class PosOp(CBMCAst):
    operand: Any

    def to_string(self) -> str:
        return f"+({_to_str(self.operand)})"


@dataclass
class MemberOp(CBMCAst):
    value: CBMCAst
    attr: CBMCAst

    def to_string(self) -> str:
        attr = self.attr.name if isinstance(self.attr, Name) else _to_str(self.attr)
        return f"{_to_str(self.value)}.{attr}"


@dataclass
class PtrMemberOp(CBMCAst):
    value: Any
    attr: str

    def to_string(self) -> str:
        attr = self.attr.name if isinstance(self.attr, Name) else str(self.attr)
        return f"{_to_str(self.value)}->{attr}"

    def get_dereference_subexpressions(self) -> list["PtrMemberOp | CBMCAst"]:
        """Return the chain of subexpressions that are dereferenced in this pointer member access.

        E.g., Given `foo->bar->baz`, return [`foo`, `foo->bar`, `foo->bar->baz`], since each
        is a pointer that must be non-null for the full expression to be valid.

        Returns:
            list[CBMCAst]: The subexpressions that are dereferenced in this chain, including self.
        """
        if isinstance(self.value, PtrMemberOp):
            return self.value.get_dereference_subexpressions() + [self]
        return [self.value, self]


@dataclass
class IndexOp(CBMCAst):
    value: Any
    index: Any

    def to_string(self) -> str:
        return f"{_to_str(self.value)}[{_to_str(self.index)}]"


@dataclass
class CallOp(CBMCAst):
    func: CBMCAst
    args: CBMCAst

    def to_string(self) -> str:
        return f"{_to_str(self.func)}({_to_str(self.args)})"


@dataclass
class ArgList(CBMCAst, ast_utils.AsList):
    items: list[Any]

    def to_string(self) -> str:
        return ", ".join(_to_str(item) for item in self.items)


class TypeNode(CBMCAst):
    pass


@dataclass
class BuiltinType(TypeNode):
    # e.g., "int", "unsigned", "signed", "bool", "char", "float", "double"
    BUILT_IN_TYPES = {"int", "unsigned", "signed", "char", "long", "float", "double"}
    name: str

    def to_string(self) -> str:
        return self.name


@dataclass
class NamedType(TypeNode):
    # typedef or user-defined type
    name: Name

    def to_string(self) -> str:
        return _to_str(self.name)


@dataclass
class QuantifierDecl(CBMCAst):
    typenode: TypeNode
    name: Name

    def to_string(self) -> str:
        return f"{_to_str(self.typenode)} {_to_str(self.name)}"


@dataclass
class Quantifier(CBMCAst):
    decl: QuantifierDecl
    range_expr: Any
    expr: Any
    kind: str = ""


@dataclass
class ForallExpr(Quantifier):
    kind: str = "forall"

    def to_string(self) -> str:
        return (
            f"__CPROVER_forall {{ {_to_str(self.decl)}; "
            f"({_to_str(self.range_expr)}) ==> {_to_str(self.expr)} }}"
        )


@dataclass
class ExistsExpr(Quantifier):
    kind: str = "exists"

    def to_string(self) -> str:
        return (
            f"__CPROVER_exists {{ {_to_str(self.decl)}; "
            f"({_to_str(self.range_expr)}) && {_to_str(self.expr)} }}"
        )


@dataclass
class Old(CBMCAst):
    expr: Any

    def to_string(self) -> str:
        return f"__CPROVER_old({_to_str(self.expr)})"


@dataclass
class ReturnValue(CBMCAst):
    def to_string(self) -> str:
        return "__CPROVER_return_value"


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
        return Assigns(condition=None, targets=AssignsTargetList(items=ExprList([])))

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
        if isinstance(expr, ExprList):
            for e in expr.items:
                self._validate_side_effect_free(e)
        # Check subexpressions
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
