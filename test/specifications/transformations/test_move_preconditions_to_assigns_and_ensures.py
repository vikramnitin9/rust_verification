from specifications.variants.transformations import MovePreconditionsToAssignsAndEnsures
from util import FunctionSpecification

transformation = MovePreconditionsToAssignsAndEnsures()


def test_move_preconditions_to_ensures_returns_unchanged_specs_if_no_ensures_clause():
    spec_without_ensures = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(pp->p != NULL)",
            "__CPROVER_requires(pp->p->buf != NULL)",
        ],
        postconditions=[],
    )
    actual_transformed_spec = transformation.apply(spec_without_ensures)[0]
    assert actual_transformed_spec == spec_without_ensures


def test_move_preconditions_to_ensures_disjunctions():
    spec_with_preconditions = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(pp != NULL)",
            "__CPROVER_requires(pp->p != NULL)",
            "__CPROVER_requires(pp->p->buf != NULL)",
            "__CPROVER_requires(some_call(foo))",
        ],
        postconditions=["__CPROVER_ensures(pp->p->buf[0] == 0)"],
    )
    actual_transformed_spec = transformation.apply(spec_with_preconditions)[0]
    expected_transformed_spec = FunctionSpecification(
        preconditions=[],
        postconditions=[
            "__CPROVER_ensures((((((pp == NULL) || (pp->p == NULL)) || (pp->p->buf == NULL)) || !some_call(foo)) || (pp->p->buf[0] == 0)))"
        ],
    )
    assert actual_transformed_spec == expected_transformed_spec


def test_move_preconditions_to_ensures_disjunctions_and_assigns_conditions():
    spec_with_preconditions = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(pp != NULL)",
            "__CPROVER_requires(pp->p != NULL)",
            "__CPROVER_requires(pp->p->buf != NULL)",
        ],
        postconditions=["__CPROVER_ensures(pp->p->buf[0] == 0)", "__CPROVER_assigns(pp->p->buf)"],
    )
    actual_transformed_spec = transformation.apply(spec_with_preconditions)[0]
    expected_transformed_spec = FunctionSpecification(
        preconditions=[],
        postconditions=[
            "__CPROVER_ensures(((((pp == NULL) || (pp->p == NULL)) || (pp->p->buf == NULL)) || (pp->p->buf[0] == 0)))",
            "__CPROVER_assigns((((pp != NULL) && (pp->p != NULL)) && (pp->p->buf != NULL)) : pp->p->buf)",
        ],
    )
    assert actual_transformed_spec == expected_transformed_spec
