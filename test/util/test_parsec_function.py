import pytest

from textwrap import dedent

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
    source_code = qsort.get_source_code()
    expected_source_code = dedent("""\
        void swap(int* a, int* b)
        {
            int t = *a;
            *a = *b;
            *b = t;
        }
        """)
    assert source_code == expected_source_code


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
    source_code = fn.get_source_code(include_documentation_comments=True)
    expected_source_code = dedent("""\
        // This is a documentation
        // Comment
        void f1() { }
        """).rstrip()
    assert source_code == expected_source_code


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
    source_code = fn.get_source_code(include_documentation_comments=True)
    expected_source_code = dedent("""\
        /** this comment
        spans three
        lines
         */
        void f2()
        {
        }
        """)
    assert source_code == expected_source_code


def test_get_source_code_with_docs_multi_line_with_line_numbers() -> None:
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
    source_code = fn.get_source_code(include_documentation_comments=True, include_line_numbers=True)
    expected_source_code = dedent("""\
        7 : /** this comment
        8 : spans three
        9 : lines
        10:  */
        11: void f2()
        12: {
        13: }
        """).rstrip()
    assert source_code == expected_source_code


def test_get_source_code_with_docs_inline_comment_above() -> None:
    fn = ParsecFunction(
        {
            "name": "f3",
            "num_args": 0,
            "returnType": "void",
            "signature": "void f3()",
            "filename": "test/data/get_source_code/test_with_doc_comments.c",
            "startLine": 16,
            "endLine": 16,
            "startCol": 1,
            "endCol": 12,
            "callees": [],
        }
    )
    source_code = fn.get_source_code(include_documentation_comments=True)
    expected_source_code = "void f3() {}"
    assert source_code == expected_source_code


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
    source_code = one_line_function.get_source_code()
    expected_source_code = 'void single_line_main() { printf("Hello, world!"); }'
    assert source_code == expected_source_code


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
    source_code = end_of_file_function.get_source_code()
    expected_source_code = dedent("""\
        void fn_at_end()
        {
            printf("This");
            printf("Function is at the end");
        }
        """).rstrip()
    assert source_code == expected_source_code


def test_get_comment_no_comments() -> None:
    function = ParsecFunction(
        {
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
        }
    )
    assert function.get_preceding_comments() is None


def test_get_comment_double_slash() -> None:
    function = ParsecFunction(
        {
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
        }
    )
    expected_comments = dedent("""\
        // Double-slash comment
        // Again
        """).rstrip()
    assert function.get_preceding_comments() == expected_comments


def test_get_comment_multi_line() -> None:
    function = ParsecFunction(
        {
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
        }
    )
    expected_comment = dedent("""\
        /**
        * Brief description.
        *
        * @param a first parameter
        * @return if any return value
        *
        * Detailed description
        **/
        """).rstrip()
    assert function.get_preceding_comments() == expected_comment


def test_get_comment_multi_line_pathological() -> None:
    function = ParsecFunction(
        {
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
        }
    )
    expected_comment = dedent("""\
        /*
        Test
        
        
        Detailed description */
        """).rstrip()
    assert function.get_preceding_comments() == expected_comment


def test_is_direct_recursive_is_true() -> None:
    function = ParsecFunction(
        {
            "name": "recursive_function",
            "num_args": 0,
            "returnType": "void",
            "signature": "void recursive_function()",
            "filename": "test/data/callgraph/direct_recursion.c",
            "startLine": 14,
            "endLine": 17,
            "startCol": 1,
            "endCol": 25,
            "callees": [{"name": "recursive_function"}],
        }
    )
    assert function.is_direct_recursive()


def test_is_direct_recursive_is_false() -> None:
    function = ParsecFunction(
        {
            "name": "a",
            "num_args": 1,
            "returnType": "int",
            "signature": "int a(int x)",
            "filename": "test/data/callgraph/simple.c",
            "startLine": 8,
            "endLine": 13,
            "startCol": 1,
            "endCol": 28,
            "callees": [],
        }
    )
    assert not function.is_direct_recursive()
