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
            "callees": [],
        }
    )
    extracted_func = qsort.get_source_code()
    expected_extracted_func = (
        "void swap(int* a, int* b)\n{\n    int t = *a;\n    *a = *b;\n    *b = t;\n}\n"
    )
    assert extracted_func == expected_extracted_func

def test_get_source_code_with_docs_double_slash() -> None:
    fn = ParsecFunction(
        {
            "name": "f1",
            "num_args": 0,
            "returnType": "void",
            "signature": "void f1()",
            "filename": "test/data/get_source_code/test_with_doc_comments.c",
            "startLine": 5,
            "endLine": 5,
            "startCol": 1,
            "endCol": 13,
            "callees": [],
        }
    )
    extracted_func = fn.get_source_code(include_documentation_comments=True)
    expected_extracted_func = (
        "// This is a documentation\n// Comment\nvoid f1() { }"
    )
    assert extracted_func == expected_extracted_func

def test_get_source_code_with_docs_multi_line() -> None:
    fn = ParsecFunction(
        {
            "name": "f1",
            "num_args": 0,
            "returnType": "void",
            "signature": "void f2()",
            "filename": "test/data/get_source_code/test_with_doc_comments.c",
            "startLine": 11,
            "endLine": 13,
            "startCol": 1,
            "endCol": 9,
            "callees": [],
        }
    )
    extracted_func = fn.get_source_code(include_documentation_comments=True)
    expected_extracted_func = (
        "/** this comment\nspans three\nlines\n */\nvoid f2()\n{\n}"
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
            "callees": [],
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
            "callees": [],
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
            "callees": [],
        }
    )
    extracted_func = end_of_file_function.get_source_code()
    expected_extracted_func = (
        'void fn_at_end()\n{\n    printf("This");\n    printf("Function is at the end");\n}'
    )
    assert extracted_func == expected_extracted_func

def test_get_comment_no_comments() -> None:
    function = ParsecFunction({
            "name": "f2",
            "num_args": 0,
            "returnType": "void",
            "signature": "void f2()",
            "filename": "test/data/get_comments/test.c",
            "startLine": 7,
            "endLine": 11,
            "startCol": 1,
            "endCol": 37,
            "callees": [],
    })
    assert function.get_documentation_comments() == ""


def test_get_comment_double_slash() -> None:
    function = ParsecFunction({
            "name": "f1",
            "num_args": 0,
            "returnType": "void",
            "signature": "void f1()",
            "filename": "test/data/get_comments/test.c",
            "startLine": 5,
            "endLine": 5,
            "startCol": 1,
            "endCol": 38,
            "callees": [],
    })
    expected_comments = "// Double-slash comment\n// Again"
    assert function.get_documentation_comments() == expected_comments

def test_get_comment_multi_line() -> None:
    function = ParsecFunction({
            "name": "f3",
            "num_args": 0,
            "returnType": "void",
            "signature": "void f3(int a)",
            "filename": "test/data/get_comments/test.c",
            "startLine": 21,
            "endLine": 24,
            "startCol": 1,
            "endCol": 14,
            "callees": [],
    })
    expected_comment = "/**\n* Brief description.\n*\n* @param a first parameter\n* @return if any return value\n*\n* Detailed description\n**/"
    assert function.get_documentation_comments() == expected_comment

def test_get_comment_multi_line_pathological() -> None:
    function = ParsecFunction({
            "name": "f4",
            "num_args": 0,
            "returnType": "void",
            "signature": "void f4()",
            "filename": "test/data/get_comments/test.c",
            "startLine": 31,
            "endLine": 34,
            "startCol": 1,
            "endCol": 9,
            "callees": [],
    })
    expected_comment = "/*\nTest\n\n\nDetailed description */"
    assert function.get_documentation_comments() == expected_comment