from pathlib import Path

from util import FunctionSpecification, CFunctionGraph, CFunction
from verification import VerificationContext, VerificationInput


def get_function_or_none(file_path: str, function_name: str) -> CFunction | None:
    """Utility method for tests."""
    function_graph = CFunctionGraph(input_path=Path(file_path))
    return function_graph.get_function_or_none(function_name=function_name)


def test_verification_input_eq() -> None:
    test_file = "test/data/callgraph/ordering.c"
    func_a = get_function_or_none(test_file, function_name="a")
    input_for_a = VerificationInput(
        function=func_a,
        spec=FunctionSpecification(preconditions=["__CPROVER_requires(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        contents_of_file_to_verify=Path(test_file).read_text(),
    )
    assert input_for_a == input_for_a, f"{input_for_a} should be equal to itself"


def test_verification_input_ne() -> None:
    test_file = "test/data/callgraph/ordering.c"
    func_a = get_function_or_none(test_file, function_name="a")
    func_b = get_function_or_none(test_file, function_name="b")
    input_for_a = VerificationInput(
        function=func_a,
        spec=FunctionSpecification(preconditions=["__CPROVER_requires(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        contents_of_file_to_verify=Path(test_file).read_text(),
    )
    input_for_b = VerificationInput(
        function=func_b,
        spec=FunctionSpecification(preconditions=["__CPROVER_requires(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        contents_of_file_to_verify=Path(test_file).read_text(),
    )
    assert input_for_a != input_for_b, f"{input_for_a} should not be equal to {input_for_b}"


def test_get_headers() -> None:
    test_file = "test/data/avocado_stub/test_header_detection.c"
    is_separator = get_function_or_none(test_file, function_name="is_separator")
    input_for_is_separator = VerificationInput(
        function=is_separator,
        spec=FunctionSpecification(preconditions=["__CPROVER_requires(1)"], postconditions=[]),
        context=VerificationContext(callee_specs={}, global_variable_specs={}),
        contents_of_file_to_verify=Path(test_file).read_text()
    )
    headers_parsed_from_file = input_for_is_separator.get_headers()
    assert headers_parsed_from_file == [
        "stdlib.h",
        "ctype.h",
        "string.h",
        "stdio.h",
    ]