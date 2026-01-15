import os
import shutil

import filecmp

from pathlib import Path
from util import FunctionSpecification, ParsecResult, function_util

import pytest


def _get_file_lines(path_to_file: str) -> list[str]:
    return Path(path_to_file).read_text(encoding="utf-8").splitlines(True)


@pytest.fixture
def setup_for_update_function():
    """Factory fixture that creates and cleans up a temporary test file."""
    created_file = None

    def _setup(file: str) -> Path:
        nonlocal created_file
        file_path, ext = os.path.splitext(file)
        dest = Path(f"{file_path}-copy{ext}")
        shutil.copyfile(Path(file), dest)
        created_file = dest
        return dest

    yield _setup

    if created_file and created_file.exists():
        created_file.unlink()


@pytest.fixture
def remove_file():
    def _remove_file(file: str) -> None:
        Path(file).unlink()

    return _remove_file


@pytest.fixture
def copy_file():
    def _copy_file(file: str) -> Path:
        file_path, ext = os.path.splitext(file)
        dest = Path(f"{file_path}-copy{ext}")
        shutil.copyfile(Path(file), dest)
        return dest

    return _copy_file


def test_extract_spec_no_spec() -> None:
    lines = _get_file_lines("test/data/function_util/no_specs.c")

    spec = function_util.extract_specification(lines)
    assert spec is None, (
        "No specification(s) should be parsed from a function with no CBMC annotations"
    )


def test_extract_single_multi_line_spec() -> None:
    lines = _get_file_lines("test/data/function_util/single_multi_line_spec.c")
    spec = function_util.extract_specification(lines)
    assert spec, f"Missing specifications from {lines}"
    assert spec.preconditions == ["__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))"], (
        f"Unexpected preconditions: {spec.preconditions}"
    )
    assert spec.postconditions == [], (
        f"Expected an empty set of postconditions, got {spec.postconditions}"
    )


def test_extract_spec_multiple_single_line_specs() -> None:
    lines = _get_file_lines("test/data/function_util/multiple_single_line_specs.c")
    spec = function_util.extract_specification(lines)
    assert spec, f"Missing specifications from {lines}"
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
    assert spec, f"Missing specifications from {lines}"
    assert spec.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ], f"Unexpected preconditions: {spec.preconditions}"
    assert spec.postconditions == [
        "__CPROVER_assigns(a)",
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b ==__CPROVER_old(*a))",
    ], f"Unexpected postconditions: {spec.postconditions}"


def test_extract_multi_line_quantifiers() -> None:
    lines = _get_file_lines("test/data/function_util/quantifiers.c")
    spec = function_util.extract_specification(lines)
    assert spec, f"Missing specifications from {lines}"
    assert spec.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(arr, (high + 1) * sizeof(int)))",
        "__CPROVER_requires(low >= 0 && high >= low)",
    ], f"Unexpected preconditions: {spec.preconditions}"
    print(spec.preconditions)
    assert spec.postconditions == [
        "__CPROVER_ensures(__CPROVER_forall {int k;(low <= k && k < __CPROVER_return_value) ==> (arr[k] <= arr[__CPROVER_return_value])})",
        "__CPROVER_ensures(__CPROVER_forall {int m;(__CPROVER_return_value < m && m <= high) ==> (arr[m] > arr[__CPROVER_return_value])})",
        "__CPROVER_ensures(__CPROVER_return_value >= low && __CPROVER_return_value <= high)",
    ], f"Unexpected postconditions: {spec.postconditions}"


def test_update_function_declaration_at_top(setup_for_update_function) -> None:
    file_containing_function = setup_for_update_function(
        "test/data/function_util/update_function_declaration/swap_top.c"
    )
    path_to_expected_updated_file = (
        "test/data/function_util/update_function_declaration/swap_top_with_specs.c"
    )
    updated_function = """void swap(int* a, int* b)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
__CPROVER_ensures(*a == __CPROVER_old(*b))
__CPROVER_ensures(*b == __CPROVER_old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}"""

    parsec_file = ParsecResult(file_containing_function)
    function_util.update_function_declaration(
        "swap", updated_function, parsec_file, file_containing_function
    )

    assert filecmp.cmp(
        f1=path_to_expected_updated_file, f2=file_containing_function
    ), (f"Expected files '{path_to_expected_updated_file}' and '{file_containing_function}' to be "
        "identical")

def test_get_signature_simple() -> None:
    src = """int main(int* a, int* b)\n{\n    printf("test")\n    return 0;\n}"""
    (signature, body) = function_util.get_signature_and_body(src, lang="c")

    assert signature == "int main(int* a, int* b)"
    assert body == """{\n    printf("test")\n    return 0;\n}"""


def test_get_function_signature() -> None:
    src = """static void
    swap(
        int* a, int* b)
{
    int t = *a;
    *a = *b;
    *b = t;
}"""

    (signature, body) = function_util.get_signature_and_body(src, lang="c")
    assert signature == "static void\n    swap(\n        int* a, int* b)"
    assert body == "{\n    int t = *a;\n    *a = *b;\n    *b = t;\n}"


def test_get_source_code_with_inserted_specs() -> None:
    path_to_swap_no_specs = Path("test/data/function_util/no_specs.c")
    swap_specs = FunctionSpecification(
        preconditions=[
            "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
            "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
        ],
        postconditions=[
            "__CPROVER_ensures(*a == __CPROVER_old(*b))",
            "__CPROVER_ensures(*b == __CPROVER_old(*a))",
        ],
    )
    swap_with_specs = function_util.get_source_code_with_inserted_spec(
        "swap", swap_specs, ParsecResult(file_path=Path(path_to_swap_no_specs))
    )
    assert (
        swap_with_specs
        == """void swap(int* a, int* b)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
__CPROVER_ensures(*a == __CPROVER_old(*b))
__CPROVER_ensures(*b == __CPROVER_old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}"""
    )


def test_update_function_declaration_at_middle(copy_file, remove_file) -> None:
    file_containing_function = copy_file(
        "test/data/function_util/update_function_declaration/swap_middle.c"
    )
    path_to_expected_updated_file = (
        "test/data/function_util/update_function_declaration/swap_middle_with_specs.c"
    )
    updated_function = """void swap(int* a, int* b)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
__CPROVER_ensures(*a == __CPROVER_old(*b))
__CPROVER_ensures(*b == __CPROVER_old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}"""

    parsec_file = ParsecResult(file_containing_function)
    function_util.update_function_declaration(
        "swap", updated_function, parsec_file, file_containing_function
    )

    assert filecmp.cmp(
        f1=path_to_expected_updated_file, f2=file_containing_function
    ), (f"Expected files '{path_to_expected_updated_file}' and '{file_containing_function}' to be "
        "identical")
    remove_file(file_containing_function)


def test_update_function_declaration_at_bottom(copy_file, remove_file) -> None:
    file_containing_function = copy_file(
        "test/data/function_util/update_function_declaration/swap_bottom.c"
    )
    path_to_expected_updated_file = (
        "test/data/function_util/update_function_declaration/swap_bottom_with_specs.c"
    )
    updated_function = """void swap(int* a, int* b)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
__CPROVER_ensures(*a == __CPROVER_old(*b))
__CPROVER_ensures(*b == __CPROVER_old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}"""

    parsec_file = ParsecResult(file_containing_function)
    function_util.update_function_declaration(
        "swap", updated_function, parsec_file, file_containing_function
    )

    assert filecmp.cmp(
        f1=path_to_expected_updated_file, f2=file_containing_function
    ), (f"Expected files '{path_to_expected_updated_file}' and '{file_containing_function}' to be "
        "identical")
    remove_file(file_containing_function)
