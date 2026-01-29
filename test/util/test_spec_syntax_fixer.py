from util.spec_syntax_fixer import fix_syntax
from util.function_specification import FunctionSpecification

# These are some examples of the illegal (for C/CBMC) array range expressions we've seen so far.
ILLEGAL_ARRAY_RANGE_EXPRESSIONS = [
    "arr[lo:hi]",
    "arr[lo.. hi]",
    "arr[lo...hi]",
    "arr[lo+1:hi]",
    "arr[lo : hi]",
]

CLAUSES_WITH_ILLEGAL_ARRAY_RANGES_TO_FIXED_CLAUSES = {
    "__CPROVER_assigns(arr[lo...hi], a, arr2[i])": "__CPROVER_assigns(*arr, a, arr2[i])",
    "__CPROVER_assigns(a, arr[1..2], arr2[i])": "__CPROVER_assigns(a, *arr, arr2[i])",
    "__CPROVER_assigns(a, arr2[i], arr[lo+2:3])": "__CPROVER_assigns(a, arr2[i], *arr)"
}

# These are some examples of specifications that contain ellipses (...), which are illegal.
ILLEGAL_CLAUSES_WITH_ELLIPSES = [
    "__CPROVER_assigns(..., a, b, c)",
    "__CPROVER_assigns(a, ..., b, c)",
    "__CPROVER_assigns(a, b, ..., c)",
    "__CPROVER_assigns(a, b, c, ...)",
]


def test_fix_illegal_array_ranges() -> None:
    # Construct `__CPROVER_assigns` clauses with the illegal array syntax.
    clauses_with_illegal_array_range_syntax = [
        f"__CPROVER_assigns({illegal_array_range})"
        for illegal_array_range in ILLEGAL_ARRAY_RANGE_EXPRESSIONS
    ]
    # Construct specs that contain the illegal clauses created above.
    specs_with_illegal_array_range_syntax = [
        FunctionSpecification(preconditions=[], postconditions=[illegal_clause])
        for illegal_clause in clauses_with_illegal_array_range_syntax
    ]
    for spec_with_syntax_error in specs_with_illegal_array_range_syntax:
        fixed_spec = fix_syntax(spec_with_syntax_error)
        # We only care about the postconditions.
        assert fixed_spec.postconditions == ["__CPROVER_assigns(*arr)"]


def test_fix_illegal_ellipses() -> None:
    specs_with_illegal_ellipses = [
        FunctionSpecification(preconditions=[], postconditions=[clause_with_ellipses])
        for clause_with_ellipses in ILLEGAL_CLAUSES_WITH_ELLIPSES
    ]
    for spec_with_illegal_ellipses in specs_with_illegal_ellipses:
        fixed_spec = fix_syntax(spec_with_illegal_ellipses)
        # We only care about the postconditions.
        assert fixed_spec.postconditions == ["__CPROVER_assigns(a, b, c)"]

def test_fix_illegal_array_ranges_with_unrelated_assigns_targets() -> None:
    for illegal_clause, fixed_clause in CLAUSES_WITH_ILLEGAL_ARRAY_RANGES_TO_FIXED_CLAUSES.items():
        spec_with_illegal_clause = FunctionSpecification(preconditions=[], postconditions=[illegal_clause])
        fixed_spec = fix_syntax(spec_with_illegal_clause)
        assert fixed_spec.postconditions == [fixed_clause]


def test_fix_multiple_illegal_ellipses() -> None:
    spec_with_multiple_illegal_ellipses = FunctionSpecification(preconditions=[], postconditions=["__CPROVER_assigns(a, b, ..., c, ..., d)"])
    fixed_spec = fix_syntax(spec_with_multiple_illegal_ellipses)
    assert fixed_spec.postconditions == ["__CPROVER_assigns(a, b, c, d)"]


