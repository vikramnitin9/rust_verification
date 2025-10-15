from util.llvm_util import extract_func
from pathlib import Path

import pytest


def test_extract_func() -> None:
    filepath = Path("data/qsort.c")
    partial_func_analysis = {
        "startLine": 5,
        "endLine": 10,
        "startCol": 1,
        "endCol": 25,
    }
    extracted_func = extract_func(filepath, partial_func_analysis)
    expected_extracted_func = (
        "void swap(int* a, int* b)\n{\n    int t = *a;\n    *a = *b;\n    *b = t;\n}\n"
    )
    assert extracted_func == expected_extracted_func


def test_extract_func_invalid_line_range() -> None:
    filepath = Path("data/qsort.c")
    partial_func_analysis = {
        "startLine": 999,
        "endLine": 9999,
        "startCol": 1,
        "endCol": 25,
    }
    with pytest.raises(ValueError):
        extract_func(filepath, partial_func_analysis)
