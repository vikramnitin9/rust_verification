from util.rust import TsRustParser, RustFunction, RustParser, RustTypeWrapper

import pytest

ts_rust_parser: RustParser = TsRustParser()

def test_parse_rust_qsort() -> None:
    parsed_fns = ts_rust_parser.get_functions_defined_in_file(file_name="data/rust_qsort/src/main.rs")
    expected_fns = [
        RustFunction(name="main", param_to_type={}),
        RustFunction(name="swap", param_to_type={ "a": RustTypeWrapper("i32", True), "b": RustTypeWrapper("i32", True)}),
        RustFunction(name="partition", param_to_type={ "arr": RustTypeWrapper("[i32]", True), "low": RustTypeWrapper("usize"), "high": RustTypeWrapper("usize")}),
        RustFunction(name="quickSort", param_to_type={ "arr": RustTypeWrapper("[i32]", True), "low": RustTypeWrapper("usize"), "high": RustTypeWrapper("usize")})
    ]
    for expected_fn in expected_fns:
        if parsed_fn := parsed_fns.get(expected_fn.name):
            assert expected_fn.param_to_type == parsed_fn.param_to_type
        else:
            pytest.fail(f"Expected {expected_fn.name} to be parsed")
    

