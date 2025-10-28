import pathlib

from util import function_util


# TODO: This seems to get a whole file, not just one function.
def _get_function_lines(path_to_file: str) -> list[str]:
    return pathlib.Path(path_to_file).read_text(encoding="utf-8").splitlines(True)


def test_extract_spec_no_spec() -> None:
    func_lines = _get_function_lines("test/data/function_util/no_specs.c")

    spec = function_util.extract_specification(func_lines)
    assert spec.preconditions == [], (
        f"Expected an empty set of preconditions, got {spec.preconditions}"
    )
    assert spec.postconditions == [], (
        f"Expected an empty set of postconditions, got {spec.postconditions}"
    )


def test_extract_single_multi_line_spec() -> None:
    func_lines = _get_function_lines("test/data/function_util/single_multi_line_spec.c")
    spec = function_util.extract_specification(func_lines)
    assert spec.preconditions == ["__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))"], (
        f"Unexpected preconditions: {spec.preconditions}"
    )
    assert spec.postconditions == [], (
        f"Expected an empty set of postconditions, got {spec.postconditions}"
    )


def test_extract_spec_multiple_single_line_specs() -> None:
    func_lines = _get_function_lines("test/data/function_util/multiple_single_line_specs.c")
    spec = function_util.extract_specification(func_lines)
    assert spec.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ], f"Unexpected preconditions: {spec.preconditions}"
    assert spec.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b == __CPROVER_old(*a))",
    ], f"Unexpected postconditions: {spec.postconditions}"


def test_extract_spec_multiple_multi_line_specs() -> None:
    func_lines = _get_function_lines("test/data/function_util/multiple_multi_line_spec.c")
    spec = function_util.extract_specification(func_lines)
    assert spec.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ], f"Unexpected preconditions: {spec.preconditions}"
    assert spec.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b ==__CPROVER_old(*a))",
    ], f"Unexpected postconditions: {spec.postconditions}"
