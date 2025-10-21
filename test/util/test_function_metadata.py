from util import Function, FunctionMetadata


def test_specs_single_line() -> None:
    qsort = Function(
        {
            "name": "swapA",
            "num_args": 2,
            "returnType": "void",
            "signature": "void swapA(int* a, int* b)",
            "filename": "test/data/qsort_with_specs.c",
            "startLine": 5,
            "endLine": 14,
            "startCol": 1,
            "endCol": 54,
        }
    )
    qsort_metadata = FunctionMetadata.from_function_analysis(qsort)
    assert qsort_metadata.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ]
    assert qsort_metadata.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b == __CPROVER_old(*a))",
    ]


def test_specs_multi_line_single_pre_and_post_cond() -> None:
    qsort = Function(
        {
            "name": "swapB",
            "num_args": 2,
            "returnType": "void",
            "signature": "void swapB(int* a, int* b)",
            "filename": "test/data/qsort_with_specs.c",
            "startLine": 16,
            "endLine": 26,
            "startCol": 1,
            "endCol": 39,
        }
    )
    qsort_metadata = FunctionMetadata.from_function_analysis(qsort)
    assert qsort_metadata.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
    ]
    assert qsort_metadata.postconditions == [
        "__CPROVER_ensures(*b == __CPROVER_old(*a))"
    ]


def test_function_with_no_specs() -> None:
    qsort = Function(
        {
            "name": "swap",
            "num_args": 2,
            "returnType": "void",
            "signature": "void swapC(int* a, int* b)",
            "filename": "test/data/qsort_with_specs.c",
            "startLine": 28,
            "endLine": 33,
            "startCol": 1,
            "endCol": 25,
        }
    )
    qsort_metadata = FunctionMetadata.from_function_analysis(qsort)
    assert qsort_metadata.preconditions == []
    assert qsort_metadata.postconditions == []


def test_specs_multi_line_multiple_pre_and_post_conds() -> None:
    qsort = Function(
        {
            "name": "swapC",
            "num_args": 2,
            "returnType": "void",
            "signature": "void swapA(int* a, int* b)",
            "filename": "test/data/qsort_with_specs.c",
            "startLine": 35,
            "endLine": 53,
            "startCol": 1,
            "endCol": 54,
        }
    )
    qsort_metadata = FunctionMetadata.from_function_analysis(qsort)
    assert qsort_metadata.preconditions == [
        "__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))",
        "__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))",
    ]
    assert qsort_metadata.postconditions == [
        "__CPROVER_ensures(*a == __CPROVER_old(*b))",
        "__CPROVER_ensures(*b ==__CPROVER_old(*a))",
    ]
