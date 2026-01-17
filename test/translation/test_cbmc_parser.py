import pytest

from translation.ast.cbmc_ast import (
    AddOp,
    AndOp,
    Assigns,
    AssignsTargetList,
    BuiltinType,
    CBMCAst,
    DerefOp,
    EnsuresClause,
    EqOp,
    ExistsExpr,
    ExprList,
    ForallExpr,
    GtOp,
    IndexOp,
    LeOp,
    LtOp,
    Name,
    NeqOp,
    Number,
    OrOp,
    QuantifierDecl,
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
            pytest.fail(f"Parsed spec is of type {type(parsed_spec)}, expected RequiresClause")


def test_parse_basic_forall_expr() -> None:
    parsed_spec = parser.parse(
        "__CPROVER_ensures(__CPROVER_forall { int i; (0 <= i && i < 10) ==> arr[i] == 0 })"
    )
    if not isinstance(parsed_spec, EnsuresClause):
        pytest.fail(f"Top level AST is of type {type(parsed_spec)}, expected EnsuresClause")
    parsed_spec_expr = parsed_spec.expr
    if not isinstance(parsed_spec_expr, ForallExpr):
        pytest.fail(
            f"Expression inside EnsuresClause is of type {type(parsed_spec_expr)}, expected ForallExpr"
        )

    # Check the declaration.
    match parsed_spec_expr.decl:
        case QuantifierDecl(typenode=BuiltinType("int"), name=Name("i")):
            pass
        case _:
            pytest.fail(f"Declaration should be `int i`, but was {parsed_spec_expr.decl}")

    # Check the range expression
    match parsed_spec_expr.range_expr:
        case AndOp(
            left=LeOp(left=Number(0), right=Name("i")), right=LtOp(left=Name("i"), right=Number(10))
        ):
            pass
        case _:
            pytest.fail(
                f"Range should be `0 <= i && i < 10`, but was {parsed_spec_expr.range_expr}"
            )

    # Check the qualifier body.
    match parsed_spec_expr.expr:
        case EqOp(left=IndexOp(value=Name("arr"), index=Name("i")), right=Number(0)):
            pass
        case _:
            pytest.fail(f"Body should be `arr[i] == 0`, but was {parsed_spec_expr.expr}")


def test_parse_basic_exists_expr() -> None:
    parsed_spec = parser.parse(
        "__CPROVER_requires(__CPROVER_exists { long j; (0 <= j && j < len + 1) && arr[j] == 10 })"
    )
    if not isinstance(parsed_spec, RequiresClause):
        pytest.fail(f"Top level AST is of type {type(parsed_spec)}, expected RequiresClause")
    parsed_spec_expr = parsed_spec.expr
    if not isinstance(parsed_spec_expr, ExistsExpr):
        pytest.fail(
            f"Expression inside RequiresClause is of type {type(parsed_spec_expr)}, expected ExistsExpr"
        )

    # Check the declaration.
    match parsed_spec_expr.decl:
        case QuantifierDecl(typenode=BuiltinType("long"), name=Name("j")):
            pass
        case _:
            pytest.fail(f"Declaration should be `long j`, but was {parsed_spec_expr.decl}")

    # Check the range expression.
    match parsed_spec_expr.range_expr:
        case AndOp(
            left=LeOp(right=Name("j"), left=Number(0)),
            right=LtOp(left=Name("j"), right=AddOp(left=Name("len"), right=Number(1))),
        ):
            pass
        case _:
            pytest.fail(
                f"Range should be `0 <= j && j < len + 1`, but was {parsed_spec_expr.range_expr}"
            )

    # Check the qualifier body.
    match parsed_spec_expr.expr:
        case EqOp(left=IndexOp(value=Name("arr"), index=Name("j")), right=Number(10)):
            pass
        case _:
            pytest.fail(f"Body should be `arr[j] == 10`, but was {parsed_spec_expr.expr}")


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


def test_assigns_empty_args() -> None:
    assigns_cbmc_spec = "__CPROVER_assigns()"
    parsed_spec = parser.parse(assigns_cbmc_spec)
    match parsed_spec:
        case Assigns(condition=None, targets=AssignsTargetList(items=ExprList(items=[]))):
            pass
        case _:
            pytest.fail(
                f"Expected the parsed spec expression: '__CPROVER_assigns(), but got: {parsed_spec}'"
            )


def test_assigns_single_arg() -> None:
    assigns_cbmc_spec = "__CPROVER_assigns(*out)"
    parsed_spec = parser.parse(assigns_cbmc_spec)

    match parsed_spec:
        case Assigns(
            condition=None,
            targets=AssignsTargetList(items=ExprList(items=[DerefOp(operand=Name("out"))])),
        ):
            pass
        case _:
            pytest.fail(
                f"Expected the parsed spec expression: '__CPROVER_assigns(*out), but got: {parsed_spec}'"
            )


def test_assigns_multiple_args() -> None:
    assigns_cbmc_spec = "__CPROVER_assigns(*out1, *out2)"
    parsed_spec = parser.parse(assigns_cbmc_spec)

    match parsed_spec:
        case Assigns(
            condition=None,
            targets=AssignsTargetList(
                items=ExprList(items=[DerefOp(operand=Name("out1")), DerefOp(operand=Name("out2"))])
            ),
        ):
            pass
        case _:
            pytest.fail(
                f"Expected the parsed spec expression: '__CPROVER_assigns(*out1, *out2), but got: {parsed_spec.expr}'"
            )
