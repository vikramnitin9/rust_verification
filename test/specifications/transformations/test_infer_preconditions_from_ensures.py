from specifications.variants.transformations import InferPreconditionsFromEnsures
from util import FunctionSpecification

transformation = InferPreconditionsFromEnsures()

def test_ensures_value_non_null():
    spec_with_non_null_ensures = FunctionSpecification(preconditions=[], postconditions=[
        "__CPROVER_ensures(foo->bar->baz->james != NULL)"
    ])
    # TODO: implement me.
    
