from pathlib import Path

from util import FunctionSpecification, ParsecFile, CFunction
from verification import VerificationContext, VerificationInput


def get_function_or_none(file_path: str, function_name: str) -> CFunction:
    """Utility method for tests."""
    parsec_file = ParsecFile(file_path=Path(file_path))
    return parsec_file.get_function(function_name=function_name)


def test_verification_input_eq() -> None:
    test_file = "test/data/callgraph/ordering.c"
    func_a = get_function_or_none(test_file, function_name="a")
    input_for_a = VerificationInput(
        function=func_a,
        spec=FunctionSpecification(preconditions=["__CPROVER_ensures(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        path_to_input_file=Path(test_file),
    )
    assert input_for_a == input_for_a, f"{input_for_a} should be equal to itself"


def test_verification_input_ne() -> None:
    test_file = "test/data/callgraph/ordering.c"
    func_a = get_function_or_none(test_file, function_name="a")
    func_b = get_function_or_none(test_file, function_name="b")
    input_for_a = VerificationInput(
        function=func_a,
        spec=FunctionSpecification(preconditions=["__CPROVER_ensures(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        path_to_input_file=Path(test_file),
    )
    input_for_b = VerificationInput(
        function=func_b,
        spec=FunctionSpecification(preconditions=["__CPROVER_ensures(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        path_to_input_file=Path(test_file),
    )
    assert input_for_a != input_for_b, f"{input_for_a} should not be equal to {input_for_b}"


def test_verification_input_eq_different_file_names() -> None:
    test_file = "test/data/callgraph/ordering.c"
    test_file_copy = "test/data/callgraph/ordering_copy.c"
    func_a = get_function_or_none(test_file, function_name="a")
    func_a_copy = get_function_or_none(test_file_copy, function_name="a")
    input_for_a = VerificationInput(
        function=func_a,
        spec=FunctionSpecification(preconditions=["__CPROVER_ensures(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        path_to_input_file=Path(test_file),
    )
    input_for_a_copy = VerificationInput(
        function=func_a_copy,
        spec=FunctionSpecification(preconditions=["__CPROVER_ensures(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        path_to_input_file=Path(test_file_copy),
    )
    assert input_for_a == input_for_a_copy, f"{input_for_a} be equal to {input_for_a_copy}"


def test_hashing_same_function() -> None:
    test_file = "test/data/callgraph/ordering.c"
    test_file_copy = "test/data/callgraph/ordering_copy.c"
    func_a = get_function_or_none(test_file, function_name="a")
    func_a_copy = get_function_or_none(test_file_copy, function_name="a")
    input_for_a = VerificationInput(
        function=func_a,
        spec=FunctionSpecification(preconditions=["__CPROVER_ensures(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        path_to_input_file=Path(test_file),
    )
    input_for_a_copy = VerificationInput(
        function=func_a_copy,
        spec=FunctionSpecification(preconditions=["__CPROVER_ensures(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        path_to_input_file=Path(test_file_copy),
    )
    func_cache = {}
    func_cache[input_for_a] = "Some value"
    assert input_for_a_copy in func_cache, f"{input_for_a_copy} should be present in {func_cache}"
