import pathlib

from util import function_util


def _get_file_lines(path_to_file: str) -> list[str]:
    return pathlib.Path(path_to_file).read_text(encoding="utf-8").splitlines(True)


def test_extract_spec_no_spec() -> None:
    lines = _get_file_lines("test/data/function_util/no_specs.c")

    spec = function_util.extract_specification(lines)
    assert spec.preconditions == [], (
        f"Expected an empty set of preconditions, got {spec.preconditions}"
    )
    assert spec.postconditions == [], (
        f"Expected an empty set of postconditions, got {spec.postconditions}"
    )


def test_extract_single_multi_line_spec() -> None:
    lines = _get_file_lines("test/data/function_util/single_multi_line_spec.c")
    spec = function_util.extract_specification(lines)
    assert spec.preconditions == ["__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))"], (
        f"Unexpected preconditions: {spec.preconditions}"
    )
    assert spec.postconditions == [], (
        f"Expected an empty set of postconditions, got {spec.postconditions}"
    )


def test_extract_spec_multiple_single_line_specs() -> None:
    lines = _get_file_lines("test/data/function_util/multiple_single_line_specs.c")
    spec = function_util.extract_specification(lines)
    assert spec.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ], f"Unexpected preconditions: {spec.preconditions}"
    assert spec.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b == __CPROVER_old(*a))",
    ], f"Unexpected postconditions: {spec.postconditions}"


def test_extract_spec_multiple_multi_line_specs() -> None:
    lines = _get_file_lines("test/data/function_util/multiple_multi_line_spec.c")
    spec = function_util.extract_specification(lines)
    assert spec.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ], f"Unexpected preconditions: {spec.preconditions}"
    assert spec.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b ==__CPROVER_old(*a))",
    ], f"Unexpected postconditions: {spec.postconditions}"
