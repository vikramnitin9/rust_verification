from util import file_util

from pathlib import Path


def test_get_directory_name() -> None:
    directory = file_util.get_directory_name_for_generated_code(Path("data/qsort.c"), "partition")
    assert str(directory) == "qsort/partition"

def test_get_directory_name_nested() -> None:
    directory = file_util.get_directory_name_for_generated_code(Path("data/subdir/foo.c"), "bar")
    assert str(directory) == "foo/bar"
