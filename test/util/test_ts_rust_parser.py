from util.rust.ts_rust_parser import TsRustParser
from util.rust.rust_parser import RustFunction

ts_rust_parser = TsRustParser()

def test_parse_rust_qsort() -> None:
    parsed_fns = ts_rust_parser.get_functions_defined_in_file(file_name="data/rust_qsort/src/main.rs")
    expected_fns = [
        RustFunction(name="main", param_to_type={}),
        RustFunction(name="swap", param_to_type={ "a": "&mut i32", "b": "&mut i32"}),
        RustFunction(name="partition", param_to_type={ "arr": "&mut [i32]", "low": "usize", "high": "usize"}),
        RustFunction(name="quickSort", param_to_type={ "arr": "&mut [i32]", "low": "usize", "high": "usize"})
    ]
    for expected_fn in expected_fns:
        assert expected_fn in parsed_fns, f"Expected function: {expected_fn} was missing from parsed functions"
    

