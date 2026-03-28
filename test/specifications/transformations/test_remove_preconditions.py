from specifications.variants.transformations import RemovePreconditions
from util import FunctionSpecification

transformation = RemovePreconditions()


def test_remove_preconditions_returns_unchanged_if_no_preconditions():
    spec_without_preconditions = FunctionSpecification(
        preconditions=[
        ],
        postconditions=["__CPROVER_ensures(__CPROVER_return_value > 0)"],
    )
    actual_transformed_specs = transformation.apply(spec_without_preconditions)
    assert actual_transformed_specs == [spec_without_preconditions]

def test_remove_preconditions_single_precondition():
    spec_single_precondition = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(a > 0)"
        ],
        postconditions=["__CPROVER_ensures(__CPROVER_return_value > 0)"],
    )
    actual_transformed_specs = transformation.apply(spec_single_precondition)
    assert actual_transformed_specs == [FunctionSpecification(preconditions=[], postconditions=["__CPROVER_ensures(__CPROVER_return_value > 0)"])]

def test_remove_preconditions_more_than_one_precondition():
    spec_multiple_preconditions = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(a > 0)",
            "__CPROVER_requires(len < INT_MAX)"
        ],
        postconditions=["__CPROVER_ensures(__CPROVER_return_value > 0)"],
    )
    actual_transformed_specs = transformation.apply(spec_multiple_preconditions)
    assert actual_transformed_specs == [
        FunctionSpecification(preconditions=["__CPROVER_requires((a > 0))"], postconditions=["__CPROVER_ensures(__CPROVER_return_value > 0)"]),
        FunctionSpecification(preconditions=["__CPROVER_requires((len < INT_MAX))"], postconditions=["__CPROVER_ensures(__CPROVER_return_value > 0)"]),
        FunctionSpecification(preconditions=[], postconditions=["__CPROVER_ensures(__CPROVER_return_value > 0)"])
    ]