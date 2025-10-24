import pathlib

from util import function_util


def _get_function_lines(path_to_file: str) -> list[str]:
    return pathlib.Path(path_to_file).read_text(encoding="utf-8").splitlines(True)


def test_extract_specs_no_specs() -> None:
    func_lines = _get_function_lines("test/data/function_util/no_specs.c")

    specs = function_util.extract_specifications(func_lines)
    assert specs.preconditions == [], (
        f"Expected an empty set of preconditions, got {specs.preconditions}"
    )
    assert specs.postconditions == [], (
        f"Expected an empty set of postconditions, got {specs.postconditions}"
    )


def test_extract_single_multi_line_spec() -> None:
    func_lines = _get_function_lines("test/data/function_util/single_multi_line_spec.c")
    specs = function_util.extract_specifications(func_lines)
    assert specs.preconditions == ["__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))"], (
        f"Unexpected preconditions: {specs.preconditions}"
    )
    assert specs.postconditions == [], (
        f"Expected an empty set of postconditions, got {specs.postconditions}"
    )


def test_extract_specs_multiple_single_line_specs() -> None:
    func_lines = _get_function_lines("test/data/function_util/multiple_single_line_specs.c")
    specs = function_util.extract_specifications(func_lines)
    assert specs.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ], f"Unexpected preconditions: {specs.preconditions}"
    assert specs.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b == __CPROVER_old(*a))",
    ], f"Unexpected postconditions: {specs.postconditions}"


def test_extract_specs_multiple_multi_line_specs() -> None:
    func_lines = _get_function_lines("test/data/function_util/multiple_multi_line_spec.c")
    specs = function_util.extract_specifications(func_lines)
    assert specs.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ], f"Unexpected preconditions: {specs.preconditions}"
    assert specs.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b ==__CPROVER_old(*a))",
    ], f"Unexpected postconditions: {specs.postconditions}"
