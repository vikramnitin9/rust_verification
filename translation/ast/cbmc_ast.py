# mypy: ignore-errors
# Ideally we'd like to type check this file, but Lark does not yet support type annotations.

from typing import List, Any
from dataclasses import dataclass
from abc import ABC, abstractmethod

import sys
from lark import ast_utils, Transformer, v_args
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
    value: Any
    attr: str


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
    func: Any
    args: List[Any]


@dataclass
class ArgList(CBMCAst, ast_utils.AsList):
    items: List[Any]


@dataclass
class Quantifier(CBMCAst):
    kind: str
    decls: List[Any]
    expr: Any


@dataclass
class Old(CBMCAst):
    expr: Any


@dataclass
class ReturnValue(CBMCAst):
    pass


class _ToAst(Transformer):
    def NAME(self, tok: Any) -> Name:
        return Name(name=str(tok))

    def NUMBER(self, tok: Any) -> Number:
        txt = str(tok)
        float_characters = [".", "e", "E"]
        if any(c in txt for c in float_characters):
            return Number(value=float(txt))
        return Number(value=int(txt))

    def BOOL(self, tok: Any) -> Bool:
        return Bool(value=(str(tok) == "1"))

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
