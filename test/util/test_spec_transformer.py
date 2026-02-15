from util.spec_transformer import SpecTransformer
from util import FunctionSpecification

transformer = SpecTransformer()

def test_move_preconditions_to_ensures_returns_unchanged_specs_if_no_ensures_clause():
    spec_without_ensures = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(pp->p != NULL)",
            "__CPROVER_requires(pp->p->buf != NULL)",
        ],
        postconditions=[]
    )
    actual_transformed_spec = transformer.move_preconditions_to_ensures(spec_without_ensures)
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
    actual_transformed_spec = transformer.move_preconditions_to_ensures(spec_with_preconditions)
    print(actual_transformed_spec)
    expected_transformed_spec = FunctionSpecification(
        preconditions=[],
        postconditions=[
            "__CPROVER_ensures((((((pp == NULL) || (pp->p == NULL)) || (pp->p->buf == NULL)) || !some_call(foo)) || (pp->p->buf[0] == 0)))"
        ]
    )
    assert actual_transformed_spec == expected_transformed_spec

def test_move_preconditions_returns_unchanged_spec_if_no_assigns():
    spec_with_no_assigns = FunctionSpecification(
        preconditions=["__CPROVER_requires(pp != NULL)"],
        postconditions=["__CPROVER_ensures(__CPROVER_return_value == 0)"]
    )
    actual_transformed_spec = transformer.move_preconditions_to_assigns(spec_with_no_assigns)
    assert actual_transformed_spec == spec_with_no_assigns

def test_move_preconditions_to_assigns_conditional():
    spec_with_preconditions = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(pp != NULL)",
            "__CPROVER_requires(pp->p != NULL)",
            "__CPROVER_requires(pp->p->buf != NULL)",
        ],
        postconditions=["__CPROVER_assigns(pp->p->buf[0])"],
    )
    expected_transformed_spec = FunctionSpecification(
        preconditions=[],
        postconditions=[
            "__CPROVER_assigns((((pp != NULL) && (pp->p != NULL)) && (pp->p->buf != NULL)) : pp->p->buf[0])"
        ],
    )
    actual_transformed_spec = transformer.move_preconditions_to_assigns(spec_with_preconditions)
    assert expected_transformed_spec == actual_transformed_spec
