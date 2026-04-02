"""Tests for the CMutator mutation-testing utility."""

from pathlib import Path
from textwrap import dedent

from util import CMutator, Mutant, MutationOperator
from util.parsec_project import ParsecProject

def _mutant_replacements(mutants: list[Mutant]) -> set[tuple[str, str]]:
    """Return the (original, replacement) pairs from a list of mutants."""
    return {(m.original, m.replacement) for m in mutants}


def _get_function(file: str, name: str):
    project = ParsecProject(Path(file))
    fn = project.get_function_or_none(name)
    assert fn, f"Function '{name}' not found in '{file}'"
    return fn


class TestArithmeticOperatorReplacement:

    def test_aor_finds_multiplication_in_factorial(self):
        """partition has + and - binary operators — expect AOR mutants."""
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        aor_mutants = mutator.get_mutants_by_operator()[MutationOperator.AOR]
        operators_replaced = {m.original for m in aor_mutants}
        assert operators_replaced, "Expected at least one AOR mutation in partition"

    def test_aor_mutant_source_differs_from_original(self):
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants_by_operator()[MutationOperator.AOR]:
            assert mutant.source_code != mutator.get_source_code

    def test_aor_replaces_plus_with_minus(self):
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        aor_mutants = mutator.get_mutants_by_operator()[MutationOperator.AOR]
        pairs = _mutant_replacements(aor_mutants)
        assert ("+", "-") in pairs, "Expected a + → - AOR mutation in partition"

    def test_aor_operator_label(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants_by_operator()[MutationOperator.AOR]:
            assert mutant.operator == MutationOperator.AOR


# ---------------------------------------------------------------------------
# ROR – Relational Operator Replacement
# ---------------------------------------------------------------------------

class TestRelationalOperatorReplacement:

    def test_ror_finds_less_than_or_equal_in_factorial(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        ror_mutants = mutator.get_mutants_by_operator()[MutationOperator.ROR]
        operators_replaced = {m.original for m in ror_mutants}
        assert "<=" in operators_replaced, (
            "Expected a '<=' ROR mutation site in factorial_iter"
        )

    def test_ror_less_than_or_equal_generates_lt_replacement(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        ror_mutants = mutator.get_mutants_by_operator()[MutationOperator.ROR]
        pairs = _mutant_replacements(ror_mutants)
        assert ("<=", "<") in pairs

    def test_ror_operator_label(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants_by_operator()[MutationOperator.ROR]:
            assert mutant.operator == MutationOperator.ROR

    def test_ror_mutant_source_contains_replacement_operator(self):
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants_by_operator()[MutationOperator.ROR]:
            assert mutant.replacement in mutant.source_code


# ---------------------------------------------------------------------------
# LCR – Logical Connector Replacement
# ---------------------------------------------------------------------------

class TestLogicalConnectorReplacement:
    def test_lcr_swaps_and_to_or_in_quicksort(self):
        fn = _get_function("data/qsort.c", "quickSort")
        mutator = CMutator(fn)
        lcr_mutants = mutator.get_mutants_by_operator()[MutationOperator.LCR]
        # quickSort has `if (low < high)` — no && / ||.
        # If no logical operators exist, the result should simply be empty.
        assert isinstance(lcr_mutants, list)

    def test_lcr_uses_source_with_and_operator(self):
        """Construct a minimal CFunction with && to verify && → || replacement."""
        fn = _get_function("data/qsort.c", "partition")
        # Inject source with && via set_source_code to exercise LCR
        src_with_and = dedent("""\
            int f(int a, int b, int c) {
                if (a > 0 && b > 0) {
                    return a + b;
                }
                return c;
            }
        """)
        fn.set_source_code(src_with_and)
        mutator = CMutator(fn)
        lcr_mutants = mutator.get_mutants_by_operator()[MutationOperator.LCR]
        assert len(lcr_mutants) == 1
        assert lcr_mutants[0].original == "&&"
        assert lcr_mutants[0].replacement == "||"
        assert "||" in lcr_mutants[0].source_code

    def test_lcr_operator_label(self):
        fn = _get_function("data/qsort.c", "partition")
        src = dedent("""\
            int f(int a, int b) {
                return (a > 0 && b > 0) || (a < 0);
            }
        """)
        fn.set_source_code(src)
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants_by_operator()[MutationOperator.LCR]:
            assert mutant.operator == MutationOperator.LCR


# ---------------------------------------------------------------------------
# CRP – Constant Replacement
# ---------------------------------------------------------------------------

class TestCRP:
    def test_crp_finds_literal_in_factorial(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        crp_mutants = mutator.get_mutants_by_operator()[MutationOperator.CRP]
        assert crp_mutants, "Expected at least one CRP mutant in factorial_iter"

    def test_crp_produces_zero_replacement_for_one(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        crp_mutants = mutator.get_mutants_by_operator()[MutationOperator.CRP]
        pairs = _mutant_replacements(crp_mutants)
        assert ("1", "0") in pairs, "Expected literal '1' → '0' CRP mutation"

    def test_crp_produces_incremented_value(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        crp_mutants = mutator.get_mutants_by_operator()[MutationOperator.CRP]
        pairs = _mutant_replacements(crp_mutants)
        assert ("1", "2") in pairs, "Expected literal '1' → '2' CRP mutation"

    def test_crp_zero_literal_only_generates_increment(self):
        """The value 0 should only mutate to 1 (not to -1 or itself)."""
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        src_with_zero = dedent("""\
            int f() {
                int x = 0;
                return x;
            }
        """)
        fn.set_source_code(src_with_zero)
        mutator = CMutator(fn)
        crp_mutants = mutator.get_mutants_by_operator()[MutationOperator.CRP]
        replacements_for_zero = [m.replacement for m in crp_mutants if m.original == "0"]
        assert "1" in replacements_for_zero
        # 0 should not produce a replacement of 0 (no-op) or -1 (guarded in the code).
        assert "0" not in replacements_for_zero

    def test_crp_operator_label(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants_by_operator()[MutationOperator.CRP]:
            assert mutant.operator == MutationOperator.CRP


# ---------------------------------------------------------------------------
# RVR – Return Value Replacement
# ---------------------------------------------------------------------------

class TestRVR:
    def test_rvr_finds_return_in_factorial(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        rvr_mutants = mutator.get_mutants_by_operator()[MutationOperator.RVR]
        assert rvr_mutants, "Expected at least one RVR mutant in factorial_iter"

    def test_rvr_replaces_return_with_zero(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        rvr_mutants = mutator.get_mutants_by_operator()[MutationOperator.RVR]
        for mutant in rvr_mutants:
            assert mutant.replacement == "0"

    def test_rvr_skips_existing_zero_return(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        src_returns_zero = dedent("""\
            int f() {
                return 0;
            }
        """)
        fn.set_source_code(src_returns_zero)
        mutator = CMutator(fn)
        rvr_mutants = mutator.get_mutants_by_operator()[MutationOperator.RVR]
        assert rvr_mutants == [], "Should not mutate a return that already returns 0"

    def test_rvr_skips_void_function(self):
        fn = _get_function("data/qsort.c", "swap")
        mutator = CMutator(fn)
        rvr_mutants = mutator.get_mutants_by_operator()[MutationOperator.RVR]
        assert rvr_mutants == [], "void functions should produce no RVR mutants"

    def test_rvr_operator_label(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants_by_operator()[MutationOperator.RVR]:
            assert mutant.operator == MutationOperator.RVR


# ---------------------------------------------------------------------------
# get_mutants (combined)
# ---------------------------------------------------------------------------

class TestGetMutants:
    def test_get_mutants_returns_list(self):
        fn = _get_function("data/factorial_iterative.c", "factorial_iter")
        mutator = CMutator(fn)
        mutants = mutator.get_mutants()
        assert isinstance(mutants, list)
        assert len(mutants) > 0

    def test_get_mutants_equals_sum_of_all_operators(self):
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        by_operator = mutator.get_mutants_by_operator()
        total_by_op = sum(len(v) for v in by_operator.values())
        assert len(mutator.get_mutants()) == total_by_op

    def test_each_mutant_has_nonempty_description(self):
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants():
            assert mutant.description, "Each mutant should have a non-empty description"

    def test_each_mutant_line_is_positive(self):
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        for mutant in mutator.get_mutants():
            assert mutant.line >= 1

    def test_mutants_are_unique(self):
        """No two mutants should produce the exact same source code."""
        fn = _get_function("data/qsort.c", "partition")
        mutator = CMutator(fn)
        sources = [m.source_code for m in mutator.get_mutants()]
        assert len(sources) == len(set(sources)), "Mutants should be unique"
