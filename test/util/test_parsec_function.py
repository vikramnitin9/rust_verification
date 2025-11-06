import pytest

from util.parsec_function import ParsecFunction


def test_get_source_code() -> None:
    qsort = ParsecFunction(
        {
            "name": "swap",
            "num_args": 2,
            "returnType": "void",
            "signature": "void swap(int* a, int* b)",
            "filename": "data/qsort.c",
            "startLine": 5,
            "endLine": 10,
            "startCol": 1,
            "endCol": 25,
            "callees": []
        }
    )
    extracted_func = qsort.get_source_code()
    expected_extracted_func = (
        "void swap(int* a, int* b)\n{\n    int t = *a;\n    *a = *b;\n    *b = t;\n}\n"
    )
    assert extracted_func == expected_extracted_func


def test_get_source_code_invalid_line_range() -> None:
    nonexistent_function = ParsecFunction(
        {
            "name": "swap",
            "num_args": 2,
            "returnType": "void",
            "signature": "void swap(int* a, int* b)",
            "filename": "data/qsort.c",
            "startLine": 999,
            "endLine": 9999,
            "startCol": 1,
            "endCol": 25,
            "callees": []
        }
    )
    with pytest.raises(ValueError):
        nonexistent_function.get_source_code()


def test_get_source_code_on_one_line() -> None:
    one_line_function = ParsecFunction(
        {
            "name": "single_line_main",
            "num_args": 0,
            "returnType": "void",
            "signature": "void single_line_main()",
            "filename": "test/data/get_source_code/test.c",
            "startLine": 3,
            "endLine": 3,
            "startCol": 1,
            "endCol": 52,
            "callees": []
        }
    )
    extracted_func = one_line_function.get_source_code()
    expected_extracted_func = 'void single_line_main() { printf("Hello, world!"); }'
    assert extracted_func == expected_extracted_func


def test_get_source_code_at_end_of_file() -> None:
    end_of_file_function = ParsecFunction(
        {
            "name": "fn_at_end",
            "num_args": 0,
            "returnType": "void",
            "signature": "void fn_at_end()",
            "filename": "test/data/get_source_code/test.c",
            "startLine": 5,
            "endLine": 9,
            "startCol": 1,
            "endCol": 37,
            "callees": []
        }
    )
    extracted_func = end_of_file_function.get_source_code()
    expected_extracted_func = (
        'void fn_at_end()\n{\n    printf("This");\n    printf("Function is at the end");\n}'
    )
    assert extracted_func == expected_extracted_func
