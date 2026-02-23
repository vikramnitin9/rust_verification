from specifications.variants.transformations import MinimizeConditionalAssigns
from util import FunctionSpecification

transformation = MinimizeConditionalAssigns()

def test_minimize_single_condition_in_assigns() -> None:
    spec_with_single_condition_in_assigns = FunctionSpecification(preconditions=[], postconditions=[
        "__CPROVER_assigns(out->target != NULL : out->target)"
    ])
    transformed_specs = transformation.apply(spec_with_single_condition_in_assigns)
    print(transformed_specs)
    assert transformed_specs == [
        FunctionSpecification(preconditions=[], postconditions=[
            "__CPROVER_assigns(out->target)"
        ])
    ]
