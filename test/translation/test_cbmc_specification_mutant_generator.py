from translation import CbmcSpecificationMutantGenerator
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
    NeqOp,
    NotOp,
    Number,
    OrOp,
    QuantifierDecl,
    RequiresClause,
    Name,
)

mutant_generator = CbmcSpecificationMutantGenerator()


def test_boolean_mutants() -> None:
    # Sanity check.
    bools = [True, False]
    for b in bools:
        assert mutant_generator.get_higher_order_mutant(Bool(value=b)) == Bool(value=not b)


def test_negation_mutant() -> None:
    not_op = NotOp(Bool(True))

    assert mutant_generator.get_higher_order_mutant(not_op) == Bool(True)


def test_top_level_clause_mutants() -> None:
    requires_clause = RequiresClause(meta=None, expr=Bool(value=False))
    assert mutant_generator.get_higher_order_mutant(requires_clause) == RequiresClause(
        meta=None, expr=Bool(value=True)
    )

    ensures_clause = EnsuresClause(meta=None, expr=Bool(value=True))
    assert mutant_generator.get_higher_order_mutant(ensures_clause) == EnsuresClause(
        meta=None, expr=Bool(value=False)
    )


def test_unnested_binop_mutant() -> None:
    simple_binop = OrOp(Bool(True), Bool(False))
    expected_mutant = AndOp(Bool(False), Bool(True))

    assert mutant_generator.get_higher_order_mutant(simple_binop) == expected_mutant


def test_nested_binop_mutant() -> None:
    simple_binop = OrOp(AndOp(Bool(True), Bool(True)), DivOp(Number(10), Number(2)))
    expected_mutant = AndOp(OrOp(Bool(False), Bool(False)), MulOp(Number(10), Number(2)))

    assert mutant_generator.get_higher_order_mutant(simple_binop) == expected_mutant


def test_mutate_forall() -> None:
    forall_expr = ForallExpr(
        QuantifierDecl(typenode=BuiltinType("int"), name=Name("i")),
        range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
        expr=EqOp(Name("i"), Number(0)),
    )
    expected_mutant = ExistsExpr(
        QuantifierDecl(typenode=BuiltinType("int"), name=Name("i")),
        range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
        expr=NeqOp(Name("i"), Number(0)),
    )
    assert mutant_generator.get_higher_order_mutant(forall_expr) == expected_mutant


def test_mutate_exists() -> None:
    exists_expr = ExistsExpr(
        QuantifierDecl(typenode=BuiltinType("int"), name=Name("i")),
        range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
        expr=EqOp(Name("i"), Number(0)),
    )
    expected_mutant = ForallExpr(
        QuantifierDecl(typenode=BuiltinType("int"), name=Name("i")),
        range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
        expr=NeqOp(Name("i"), Number(0)),
    )
    assert mutant_generator.get_higher_order_mutant(exists_expr) == expected_mutant


def test_get_mutants_boolean() -> None:
    bools = [True, False]
    for b in bools:
        mutants = mutant_generator.get_mutants(Bool(value=b))
        assert len(mutants) == 1, "Boolean nodes should only have a single mutant"
        assert next(iter(mutants)) == Bool(value=not b)


def test_get_mutants_negate() -> None:
    # !(True && True) -> True && True, !(True && False), !(False && True), !(True || True)
    not_op = NotOp(AndOp(Bool(True), Bool(True)))
    mutants = mutant_generator.get_mutants(not_op)
    expected_mutants = {
        AndOp(Bool(True), Bool(True)),
        NotOp(OrOp(Bool(True), Bool(True))),
        NotOp(AndOp(Bool(False), Bool(True))),
        NotOp(AndOp(Bool(True), Bool(False))),
        NotOp(Bool(True)),
    }
    assert mutants == expected_mutants


def test_get_mutants_requires() -> None:
    requires_clause = RequiresClause(meta=None, expr=AndOp(Bool(True), Bool(True)))
    mutants = mutant_generator.get_mutants(requires_clause)
    expected_mutants = {
        RequiresClause(meta=None, expr=OrOp(Bool(True), Bool(True))),
        RequiresClause(meta=None, expr=AndOp(Bool(False), Bool(True))),
        RequiresClause(meta=None, expr=AndOp(Bool(True), Bool(False))),
        RequiresClause(meta=None, expr=NotOp(AndOp(Bool(True), Bool(True)))),
        RequiresClause(meta=None, expr=Bool(True))
    }
    assert mutants == expected_mutants

def test_get_mutants_forall() -> None:
    range_expr=AndOp(LeOp(Number(0), Name("i")), LtOp(Name("i"), Number(10))),
    forall_expr = ForallExpr(
        QuantifierDecl(typenode=BuiltinType("int"), name=Name("i")),
        range_expr=range_expr,
        expr=EqOp(Name("i"), Number(0)),
    )
    expected_mutants ={
        ExistsExpr(decl=QuantifierDecl(typenode=BuiltinType(name='int'), name=Name(name='i')), range_expr=range_expr, expr=EqOp(left=Name(name='i'), right=Number(value=0)), kind='exists'),
        ForallExpr(decl=QuantifierDecl(typenode=BuiltinType(name='int'), name=Name(name='i')), range_expr=range_expr, expr=NeqOp(left=Name(name='i'), right=Number(value=0)), kind='forall'),
        ForallExpr(decl=QuantifierDecl(typenode=BuiltinType(name='int'), name=Name(name='i')), range_expr=range_expr, expr=NotOp(operand=EqOp(left=Name(name='i'), right=Number(value=0))), kind='forall'),
    } 
    print(mutant_generator.get_mutants(forall_expr))
    assert mutant_generator.get_mutants(forall_expr) == expected_mutants

