from specifications.variants.transformations import InferNonNullPreconditionsFromEnsures
from util import FunctionSpecification

transformation = InferNonNullPreconditionsFromEnsures()


def test_ensures_value_non_null():
    spec_with_non_null_ensures = FunctionSpecification(
        preconditions=[], postconditions=["__CPROVER_ensures(foo->bar->baz->james != NULL)"]
    )
    spec_with_updated_preconditions = transformation.apply(spec_with_non_null_ensures)[0]
    assert spec_with_updated_preconditions.preconditions == [
        "__CPROVER_requires((foo != NULL))",
        "__CPROVER_requires((foo->bar != NULL))",
        "__CPROVER_requires((foo->bar->baz != NULL))",
    ]
    assert (
        spec_with_updated_preconditions.postconditions == spec_with_non_null_ensures.postconditions
    )


def test_infers_precondition_with_existing_preconditions():
    spec_with_non_null_ensures = FunctionSpecification(
        preconditions=["__CPROVER_requires(z < INT_MAX)"],
        postconditions=["__CPROVER_ensures(a->b->c->arr[0] != NULL)"],
    )
    spec_with_updated_preconditions = transformation.apply(spec_with_non_null_ensures)[0]
    assert spec_with_updated_preconditions.preconditions == [
        "__CPROVER_requires((z < INT_MAX))",
        "__CPROVER_requires((a != NULL))",
        "__CPROVER_requires((a->b != NULL))",
        "__CPROVER_requires((a->b->c != NULL))",
    ]
    assert (
        spec_with_updated_preconditions.postconditions == spec_with_non_null_ensures.postconditions
    )
