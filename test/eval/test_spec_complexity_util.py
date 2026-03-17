from translation.ast.cbmc_ast import OrOp, Bool, NotOp, GeOp, Number, AndOp

from eval import is_tautology, count_atoms_in_clause


def test_count_atoms_in_clause_singleton() -> None:
    clause = "__CPROVER_requires(a < b)"
    assert count_atoms_in_clause(clause) == 1, "The expression 'a < b' comprises one atom."


def test_count_atoms_in_clause_recursion() -> None:
    clause = "__CPROVER_ensures(a < b || b < 1 + 2)"
    assert count_atoms_in_clause(clause) == 2, (
        "The expression 'a < b || b < 1 + 2' comprises two atoms."
    )


def test_count_atoms_in_clause_eq() -> None:
    clause = "__CPROVER_ensures(a < b == b < 1 + 2)"
    assert count_atoms_in_clause(clause) == 2, (
        "The expression 'a < b || b < 1 + 2' comprises two atoms."
    )


def test_count_atoms_quantifier_body() -> None:
    clause = (
        "__CPROVER_ensures(__CPROVER_forall { int i; (0 < i <= 10) ==> i < 10 || a > b + 1 && c})"
    )
    assert count_atoms_in_clause(clause) == 3, (
        "The expression 'i < 10 || a > b + 1 && c' comprises 3 atoms."
    )


def test_is_tautology_simple() -> None:
    simple_tautology = OrOp(Bool(True), NotOp(Bool(True)))
    assert is_tautology(simple_tautology), f"Expected {simple_tautology} to be a tautology"

    tautology = OrOp(NotOp(GeOp(Number(1), Number(-1))), GeOp(Number(1), Number(-1)))
    assert is_tautology(tautology), f"Expected {tautology} to be a tautology"


def test_is_tautology_distributive_law() -> None:
    node = NotOp(AndOp(NotOp(Bool(True)), Bool(True)))
    assert is_tautology(node), f"Expected {node} to be a tautology"
