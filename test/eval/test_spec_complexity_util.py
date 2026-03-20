import pytest
from translation.ast.cbmc_ast import (
    AddOp,
    BuiltinType,
    EqOp,
    ForallExpr,
    LeOp,
    LtOp,
    Name,
    OrOp,
    Number,
    AndOp,
    QuantifierDecl,
)

from eval import (
    get_complexity,
    ClauseComplexity,
    ClauseComplexityError,
    get_atoms_in_expression,
)


def test_get_complexity_simple() -> None:
    clause = "__CPROVER_requires(a < b || c && 1 + 2 == d)"
    complexity = get_complexity(clause)
    match complexity:
        case ClauseComplexity(clause=_, num_atoms=3, num_unique_atoms=3, is_tautology=False):
            pass
        case _:
            pytest.fail(
                f"'{clause}' should be reported to have 3 atoms and not be a tautology, but got {complexity}"
            )


def test_get_complexity_tautology() -> None:
    clause = "__CPROVER_requires((a < b || c && 1 + 2 == d) || !(a < b || c && 1 + 2 == d))"
    complexity = get_complexity(clause)
    match complexity:
        case ClauseComplexity(clause=_, num_atoms=6, is_tautology=True):
            pass
        case _:
            pytest.fail(
                f"'{clause}' should be reported to have 6 atoms and be a tautology, but got {complexity}"
            )

def test_get_complexity_syntactically_invalid_spec() -> None:
    invalid_clause = "__CPROVER_assigns(out[i], out[i+1], out[i+2], ...)"
    complexity = get_complexity(invalid_clause)
    match complexity:
        case ClauseComplexityError():
            pass
        case ClauseComplexity():
            pytest.fail(f"{invalid_clause} is invalid, and should not have a complexity reported")

def test_get_complexity_assigns_empty_condition() -> None:
    invalid_clause = "__CPROVER_assigns(*out)"
    complexity = get_complexity(invalid_clause)
    match complexity:
        case ClauseComplexity():
            pass
        case ClauseComplexityError():
            pytest.fail(f"{invalid_clause} is invalid, and should not have a complexity reported")

def test_count_atoms_in_expr_singleton() -> None:
    expr = LtOp(Name("a"), Name("b"))
    assert len(get_atoms_in_expression(expr)) == 1, f"The expression '{expr}' comprises one atom."


def test_count_atoms_in_clause_recursion() -> None:
    # expr = "__CPROVER_ensures(a < b || b < 1 + 2)"
    expr = OrOp(LtOp(Name("a"), Name("b")), LtOp(Name("b"), AddOp(Number(1), Number(2))))
    assert len(get_atoms_in_expression(expr)) == 2, (
        "The expression 'a < b || b < 1 + 2' comprises two atoms."
    )


def test_count_atoms_in_clause_eq() -> None:
    expr = EqOp(LtOp(Name("a"), Name("b")), AddOp(Number(1), Number(2)))
    assert len(get_atoms_in_expression(expr)) == 1, (
        "The expression 'a < b == 1 + 2' comprises one atom."
    )


def test_count_atoms_combined() -> None:
    expr = OrOp(
        LtOp(Name("a"), Name("b")), AndOp(Name("c"), EqOp(AddOp(Number(1), Number(2)), Name("d")))
    )
    assert len(get_atoms_in_expression(expr)) == 3


def test_count_atoms_quantifier_body() -> None:
    range_expr = AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10)))
    body_expr = OrOp(
        LtOp(Name("i"), Number(10)), AndOp(Name("z"), LtOp(Name("a"), AddOp(Number(1), Number(2))))
    )
    forall_expr = ForallExpr(
        decl=QuantifierDecl(typenode=BuiltinType(name="int"), name=Name(name="i")),
        range_expr=range_expr,
        expr=body_expr,
        kind="forall",
    )
    assert len(get_atoms_in_expression(forall_expr)) == 3, (
        "The expression 'i < 10 || z && a > b + 1' comprises 3 atoms."
    )

