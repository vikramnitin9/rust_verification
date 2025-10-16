from util.llvm_analysis import Function
from pathlib import Path

import pytest


def test_extract_func() -> None:
    filepath = Path("data/qsort.c")
    qsort = Function(
        name="swap",
        num_args=2,
        return_type="void",
        signature="void swap(int* a, int* b)",
        file_name="data/qsort.c",
        start_line=5,
        end_line=10,
        start_col=1,
        end_col=25,
    )
    extracted_func = qsort.get_source_code(filepath)
    expected_extracted_func = (
        "void swap(int* a, int* b)\n{\n    int t = *a;\n    *a = *b;\n    *b = t;\n}\n"
    )
    assert extracted_func == expected_extracted_func


def test_extract_func_invalid_line_range() -> None:
    filepath = Path("data/qsort.c")
    nonexistent_function = Function(
        name="swap",
        num_args=2,
        return_type="void",
        signature="void swap(int* a, int* b)",
        file_name="data/qsort.c",
        start_line=999,
        end_line=9999,
        start_col=1,
        end_col=25,
    )
    with pytest.raises(ValueError):
        nonexistent_function.get_source_code(filepath)


def test_extract_func_on_one_line() -> None:
    filepath = Path("test/data/extract_func/test.c")
    one_line_function = Function(
        name="single_line_main",
        num_args=0,
        return_type="void",
        signature="void single_line_main()",
        file_name="test/data/extract_func/test.c",
        start_line=3,
        end_line=3,
        start_col=1,
        end_col=52,
    )
    extracted_func = one_line_function.get_source_code(filepath)
    expected_extracted_func = 'void single_line_main() { printf("Hello, world!"); }'
    assert extracted_func == expected_extracted_func


def test_extract_func_at_end_of_file() -> None:
    filepath = Path("test/data/extract_func/test.c")
    end_of_file_function = Function(
        name="fn_at_end",
        num_args=0,
        return_type="void",
        signature="void fn_at_end()",
        file_name="test/data/extract_func/test.c",
        start_line=5,
        end_line=9,
        start_col=1,
        end_col=37,
    )
    extracted_func = end_of_file_function.get_source_code(filepath)
    expected_extracted_func = 'void fn_at_end()\n{\n    printf("This");\n    printf("Function is at the end");\n}'
    assert extracted_func == expected_extracted_func
