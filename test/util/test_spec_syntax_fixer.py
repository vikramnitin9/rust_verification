from util.spec_syntax_fixer import fix_syntax
from util.function_specification import FunctionSpecification


def test_fix_illegal_array_ranges() -> None:
    illegal_array_range_syntax = ["arr[lo:hi]", "arr[lo.. hi]", "arr[lo...hi]", "arr[lo+1:hi]", "arr[lo : hi]"]
    replacement_clause = "__CPROVER_assigns(*arr)"
    func_spec = FunctionSpecification(
        preconditions=[],
        postconditions=[
            f"__CPROVER_assigns({illegal_array})" for illegal_array in illegal_array_range_syntax
        ],
    )
    fixed_spec = fix_syntax(func_spec)
    assert set(fixed_spec.postconditions) == set([replacement_clause])

def test_fix_illegal_ellipses() -> None:
    func_spec = FunctionSpecification(
        preconditions=[],
        postconditions=[
            "__CPROVER_assigns(..., a, b, c)",
            "__CPROVER_assigns(a, ..., b, c)",
            "__CPROVER_assigns(a, b, ..., c)",
            "__CPROVER_assigns(a, b, c, ...)",
        ]
    )
    replacement_clause = "__CPROVER_assigns(a, b, c)"
    fixed_spec = fix_syntax(func_spec)
    assert set(fixed_spec.postconditions) == set([replacement_clause])