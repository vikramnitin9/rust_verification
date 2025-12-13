import pytest

from util.rust import RustFunction, RustParser, RustTypeWrapper, TsRustParser


@pytest.fixture
def ts_rust_parser() -> RustParser:
    return TsRustParser()


def test_parse_rust_qsort(ts_rust_parser: RustParser) -> None:
    parsed_fns = ts_rust_parser.get_functions_defined_in_file(
        file_name="data/rust_qsort/src/main.rs"
    )
    expected_fns = [
        RustFunction(name="main", param_to_type={}),
        RustFunction(
            name="swap",
            param_to_type={
                "a": RustTypeWrapper("i32", is_mutable=True, is_reference=True),
                "b": RustTypeWrapper("i32", is_mutable=True, is_reference=True),
            },
        ),
        RustFunction(
            name="partition",
            param_to_type={
                "arr": RustTypeWrapper("[i32]", is_mutable=True, is_reference=True),
                "low": RustTypeWrapper("usize", is_reference=False),
                "high": RustTypeWrapper("usize", is_reference=False),
            },
        ),
        RustFunction(
            name="quickSort",
            param_to_type={
                "arr": RustTypeWrapper("[i32]", is_mutable=True, is_reference=True),
                "low": RustTypeWrapper("usize", is_reference=False),
                "high": RustTypeWrapper("usize", is_reference=False),
            },
        ),
    ]
    for expected_fn in expected_fns:
        if parsed_fn := parsed_fns.get(expected_fn.name):
            assert expected_fn.param_to_type == parsed_fn.param_to_type
        else:
            pytest.fail(f"Expected {expected_fn.name} to be parsed")


def test_parse_rust_parameter_type_binding_decls(ts_rust_parser: RustParser) -> None:
    parsed_fns = ts_rust_parser.get_functions_defined_in_file(
        file_name="test/data/rust/test_rust_function_parsing.rs"
    )
    fn_name_to_expected_decls = {
        "f1": "let x: String = kani::any();",
        "f2": "let x: String = kani::any();",
        "f3": "let mut x: String = kani::any();",
        "f4": "let x: String = kani::any();",
        "f5": "let mut x: String = kani::any();",
    }
    for fn_name, expected_decl in fn_name_to_expected_decls.items():
        if parsed_fn := parsed_fns.get(fn_name):
            assert expected_decl == parsed_fn.param_to_type["a"].declaration(
                variable_name="x", val="kani::any()"
            )
        else:
            pytest.fail(f"Expected {fn_name} to be parsed")


def test_parse_rust_parameter_type_binding_args(ts_rust_parser: RustParser) -> None:
    parsed_fns = ts_rust_parser.get_functions_defined_in_file(
        file_name="test/data/rust/test_rust_function_parsing.rs"
    )
    fn_name_to_expected_decls = {
        "f1": "a",
        "f2": "&a",
        "f3": "&mut a",
    }
    for fn_name, expected_decl in fn_name_to_expected_decls.items():
        if parsed_fn := parsed_fns.get(fn_name):
            assert expected_decl == parsed_fn.param_to_type["a"].to_argument(name="a")
        else:
            pytest.fail(f"Expected {fn_name} to be parsed")
