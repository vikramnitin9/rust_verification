from translation import MutantGenerator
from translation.ast.cbmc_ast import (
    AndOp,
    Bool,
    BuiltinType,
    DivOp,
    EnsuresClause,
    EqOp,
    ExistsExpr,
    ForallExpr,
    LeOp,
    LtOp,
    MulOp,
    NegOp,
    NeqOp,
    Number,
    OrOp,
    QuantifierDecl,
    RequiresClause,
    Name,
)

mutant_generator = MutantGenerator()


def test_boolean_mutants() -> None:
    # Sanity check.
    bools = [True, False]
    for b in bools:
        assert mutant_generator.get_mutant(Bool(value=b)) == Bool(value=not b)


def test_neg_mutant() -> None:
    neg_op = NegOp(Bool(True))

    assert mutant_generator.get_mutant(neg_op) == Bool(True)


def test_top_level_clause_mutants() -> None:
    requires_clause = RequiresClause(meta=None, expr=Bool(value=False))
    assert mutant_generator.get_mutant(requires_clause) == RequiresClause(
        meta=None, expr=Bool(value=True)
    )

    ensures_clause = EnsuresClause(meta=None, expr=Bool(value=True))
    assert mutant_generator.get_mutant(ensures_clause) == EnsuresClause(
        meta=None, expr=Bool(value=False)
    )


def test_unnested_binop_mutant() -> None:
    simple_binop = OrOp(Bool(True), Bool(False))
    expected_mutant = AndOp(Bool(False), Bool(True))

    assert mutant_generator.get_mutant(simple_binop) == expected_mutant


def test_nested_binop_mutant() -> None:
    simple_binop = OrOp(AndOp(Bool(True), Bool(True)), DivOp(Number(10), Number(2)))
    expected_mutant = AndOp(OrOp(Bool(False), Bool(False)), MulOp(Number(10), Number(2)))

    assert mutant_generator.get_mutant(simple_binop) == expected_mutant


def test_mutate_forall() -> None:
    forall_expr = ForallExpr(
        QuantifierDecl(
            typenode=BuiltinType("int"),
            name=Name("i")),
            range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
            expr=EqOp(Name("i"), Number(0)),
        )
    expected_mutant = ExistsExpr(
        QuantifierDecl(
            typenode=BuiltinType("int"),
            name=Name("i")),
            range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
            expr=NeqOp(Name("i"), Number(0)),
    )
    assert mutant_generator.get_mutant(forall_expr) == expected_mutant

def test_mutate_exists() -> None:
    forall_expr = ExistsExpr(
        QuantifierDecl(
            typenode=BuiltinType("int"),
            name=Name("i")),
            range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
            expr=EqOp(Name("i"), Number(0)),
        )
    expected_mutant = ForallExpr(
        QuantifierDecl(
            typenode=BuiltinType("int"),
            name=Name("i")),
            range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
            expr=NeqOp(Name("i"), Number(0)),
    )
    assert mutant_generator.get_mutant(forall_expr) == expected_mutant

def test_get_single_point_mutants_boolean() -> None:
    bools = [True, False]
    for b in bools:
        mutants = mutant_generator.get_single_point_mutants(Bool(value=b))
        assert len(mutants) == 1, f"Boolean nodes should only have a single mutant"
        assert mutants[0] == Bool(value=not b)

def test_get_single_point_mutants_negate() -> None:
    # !(True && True) -> True && True, !(True && False), !(False && True), !(True || True)
    negop = NegOp(AndOp(Bool(True), Bool(True)))
    mutants = mutant_generator.get_single_point_mutants(negop)
    expected_mutants = [
        AndOp(Bool(True), Bool(True)),
        NegOp(OrOp(Bool(True), Bool(True))),
        NegOp(AndOp(Bool(False), Bool(True))),
        NegOp(AndOp(Bool(True), Bool(False))),
    ]
    assert len(mutants) == len(expected_mutants)
    for expected_mutant in expected_mutants:
        assert expected_mutant in mutants
