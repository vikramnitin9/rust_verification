from pathlib import Path
from textwrap import dedent

from util.parsec_file import ParsecFile


def test_get_source_code() -> None:
    parsec_file = ParsecFile(Path("data/qsort.c"))
    expected_source_code = dedent("""\
        void swap(int* a, int* b)
        {
            int t = *a;
            *a = *b;
            *b = t;
        }""")
    expected_function = parsec_file.get_function_or_none("swap")
    assert expected_function, "Function 'swap' should be declared in data/qsort.c"
    assert expected_function.get_source_code() == expected_source_code


def test_get_source_code_with_docs_double_slash() -> None:
    parsec_file = ParsecFile(Path("test/data/get_source_code/test_with_doc_comments.c"))
    expected_function = parsec_file.get_function_or_none("f1")
    assert expected_function, "Function 'f1' should be declared in test/data/get_source_code/test_with_doc_comments.c"
    expected_source_code = dedent("""\
        // This is a documentation
        // Comment
        void f1() { }""").rstrip()
    assert expected_function.get_source_code(include_documentation_comments=True) == expected_source_code


def test_get_source_code_with_docs_multi_line() -> None:
    parsec_file = ParsecFile(Path("test/data/get_source_code/test_with_doc_comments.c"))
    expected_function = parsec_file.get_function_or_none("f2")
    assert expected_function, "Function 'f2' should be declared in test/data/get_source_code/test_with_doc_comments.c"
    expected_source_code = dedent("""\
        /** this comment
        spans three
        lines
         */
        void f2()
        {
        }""")
    assert expected_function.get_source_code(include_documentation_comments=True) == expected_source_code


def test_get_source_code_with_docs_multi_line_with_line_numbers() -> None:
    parsec_file = ParsecFile(Path("test/data/get_source_code/test_with_doc_comments.c"))
    expected_function = parsec_file.get_function_or_none("f2")
    assert expected_function, "Function 'f2' should be declared in test/data/get_source_code/test_with_doc_comments.c"
    expected_source_code = dedent("""\
        7 : /** this comment
        8 : spans three
        9 : lines
        10:  */
        11: void f2()
        12: {
        13: }""").rstrip()
    assert expected_function.get_source_code(include_documentation_comments=True, include_line_numbers=True) == expected_source_code


def test_get_source_code_with_docs_inline_comment_above() -> None:
    parsec_file = ParsecFile(Path("test/data/get_source_code/test_with_doc_comments.c"))
    expected_function = parsec_file.get_function_or_none("f3")
    assert expected_function, "Function 'f3' should be declared in test/data/get_source_code/test_with_doc_comments.c"
    expected_source_code = "void f3() {}"
    assert expected_function.get_source_code(include_documentation_comments=True) == expected_source_code


def test_get_source_code_on_one_line() -> None:
    parsec_file = ParsecFile(Path("test/data/get_source_code/test.c"))
    expected_function = parsec_file.get_function_or_none("single_line_main")
    assert expected_function, "Function 'single_line_main' should be declared in test/data/get_source_code/test.c"
    expected_source_code = 'void single_line_main() { printf("Hello, world!"); }'
    assert expected_function.get_source_code() == expected_source_code


def test_get_source_code_at_end_of_file() -> None:
    parsec_file = ParsecFile(Path("test/data/get_source_code/test.c"))
    expected_function = parsec_file.get_function_or_none("fn_at_end")
    assert expected_function, "Function 'fn_at_end' should be declared in test/data/get_source_code/test.c"
    expected_source_code = dedent("""\
        void fn_at_end()
        {
            printf("This");
            printf("Function is at the end");
        }
        """).rstrip()
    assert expected_function.get_source_code() == expected_source_code


def test_get_comment_no_comments() -> None:
    parsec_file = ParsecFile(Path("test/data/get_comments/test.c"))
    expected_function = parsec_file.get_function_or_none("f2")
    assert expected_function, "Function 'f2' should be declared in test/data/get_comments/test.c"
    assert expected_function.get_preceding_lines_starting_with_comment_delimiters() is None


def test_get_comment_double_slash() -> None:
    parsec_file = ParsecFile(Path("test/data/get_comments/test.c"))
    expected_function = parsec_file.get_function_or_none("f1")
    assert expected_function, "Function 'f1' should be declared in test/data/get_comments/test.c"
    expected_comments = dedent("""\
        // Double-slash comment
        // Again
        """).rstrip()
    assert expected_function.get_preceding_lines_starting_with_comment_delimiters() == expected_comments


def test_get_comment_multi_line() -> None:
    parsec_file = ParsecFile(Path("test/data/get_comments/test.c"))
    expected_function = parsec_file.get_function_or_none("f3")
    assert expected_function, "Function 'f3' should be declared in test/data/get_comments/test.c"
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
    assert expected_function.get_preceding_lines_starting_with_comment_delimiters() == expected_comment


def test_get_comment_multi_line_pathological() -> None:
    parsec_file = ParsecFile(Path("test/data/get_comments/test.c"))
    expected_function = parsec_file.get_function_or_none("f4")
    assert expected_function, "Function 'f4' should be declared in test/data/get_comments/test.c"
    expected_comment = dedent("""\
        /*
        Test
        
        
        Detailed description */
        """).rstrip()
    assert expected_function.get_preceding_lines_starting_with_comment_delimiters() == expected_comment


def test_is_self_recursive_is_true() -> None:
    parsec_file = ParsecFile(Path("test/data/callgraph/self_recursion.c"))
    expected_function = parsec_file.get_function_or_none("recursive_function")
    assert expected_function, "Function 'recursive_function' should be declared in test/data/callgraph/direct_recursion.c"
    assert expected_function.is_self_recursive()


def test_is_self_recursive_is_false() -> None:
    parsec_file = ParsecFile(Path("test/data/callgraph/simple.c"))
    expected_function = parsec_file.get_function_or_none("a")
    assert expected_function, "Function 'a' should be declared in test/data/callgraph/simple.c"
    assert not expected_function.is_self_recursive()
