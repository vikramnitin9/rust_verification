import pytest

from translation.ast.cbmc_ast import (
    CBMCAst,
    DerefOp,
    EnsuresClause,
    GtOp,
    Name,
    NeqOp,
    Number,
    OrOp,
    RequiresClause,
    ToAst,
)
from translation.parser import Parser

parser: Parser[CBMCAst] = Parser(
    path_to_grammar_defn="translation/grammar/cbmc.txt",
    start="cbmc_clause",
    transformer=ToAst(),
)


def test_single_line_cbmc_precond() -> None:
    parsed_precond = parser.parse("__CPROVER_requires(1)")
    assert isinstance(parsed_precond, RequiresClause), (
        f"Parsed specification is of type {type(parsed_precond)}, expected RequiresClause"
    )


def test_single_line_cbmc_postcond() -> None:
    parsed_postcond = parser.parse("__CPROVER_ensures(1)")
    assert isinstance(parsed_postcond, EnsuresClause), (
        f"Parsed specification is of type {type(parsed_postcond)}, expected EnsuresClause"
    )


def test_parse_condition_expr() -> None:
    parsed_spec = parser.parse("__CPROVER_ensures(*x > 10)")
    match parsed_spec:
        case EnsuresClause(_, GtOp(DerefOp(Name("x")), Number(10))):
            pass
        case _:
            pytest.fail(f"Parsed spec is of type {type(parsed_spec)}, expected EnsuresClause")


def test_parse_nested_condition_expr() -> None:
    parsed_spec = parser.parse("__CPROVER_requires(*x > 10 || *y != 2)")
    match parsed_spec:
        case RequiresClause(
            _,
            OrOp(
                GtOp(DerefOp(Name("x")), Number(10)),
                NeqOp(DerefOp(Name("y")), Number(2)),
            ),
        ):
            pass
        case _:
            pytest.fail(f"Parsed spec is of type {type(parsed_spec)}, expected EnsuresClause")


def test_parse_multi_line_spec() -> None:
    multi_line_spec = """
    __CPROVER_requires(
        *x > 10 ||
        *y != 2
    )
    """
    parsed_spec = parser.parse(multi_line_spec)
    match parsed_spec:
        case RequiresClause(
            _,
            OrOp(
                GtOp(DerefOp(Name("x")), Number(10)),
                NeqOp(DerefOp(Name("y")), Number(2)),
            ),
        ):
            pass
        case _:
            pytest.fail(f"Parsed spec is of type {type(parsed_spec)}, expected RequiresClause")
