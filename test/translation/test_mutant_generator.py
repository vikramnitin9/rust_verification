from translation import MutantGenerator
from translation.ast.cbmc_ast import Bool, EnsuresClause, OrOp, RequiresClause

mutant_generator = MutantGenerator()


def test_boolean_mutants() -> None:
    # Sanity check.
    bools = [True, False]
    for b in bools:
        assert mutant_generator.get_mutant(Bool(value=b)) == Bool(value=not b)


def test_top_level_clause_mutants() -> None:
    requires_clause = RequiresClause(meta=None, expr=Bool(value=False))
    assert mutant_generator.get_mutant(requires_clause) == RequiresClause(
        meta=None, expr=Bool(value=True)
    )

    ensures_clause = EnsuresClause(meta=None, expr=Bool(value=True))
    assert mutant_generator.get_mutant(ensures_clause) == EnsuresClause(
        meta=None, expr=Bool(value=False)
    )


def test_binop_mutants() -> None:
    print(mutant_generator.get_mutant(OrOp(Bool(True), Bool(False))))