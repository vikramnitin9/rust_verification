from translation.ast.cbmc_ast import OrOp, Bool, NotOp, GeOp, Number, AndOp

from eval import is_tautology

def test_is_tautology_simple() -> None:
    simple_tautology = OrOp(Bool(True), NotOp(Bool(True)))
    assert is_tautology(simple_tautology), f"Expected {simple_tautology} to be a tautology"

    tautology = OrOp(NotOp(GeOp(Number(1), Number(-1))), GeOp(Number(1), Number(-1)))
    assert is_tautology(tautology), f"Expected {tautology} to be a tautology"

def test_is_tautology_distributive_law() -> None:
    node = NotOp(AndOp(NotOp(Bool(True)), Bool(True)))
    assert is_tautology(node), f"Expected {node} to be a tautology"
