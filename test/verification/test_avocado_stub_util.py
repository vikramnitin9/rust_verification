from verification import avocado_stub_util

from pathlib import Path


def _read_file_content(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")


def test_stub_mapping() -> None:
    name_to_rename_data = avocado_stub_util.get_stub_mappings()
    assert len(name_to_rename_data) != 0, (
        "Expected a non-zero number of stub function renamings"
    )
    for name, rename_metadata in name_to_rename_data.items():
        expected_rename = f"_avocado_{name}"

        assert rename_metadata.avocado_name == expected_rename, (
            f"Expected {name} in {rename_metadata.file_path.name} to be renamed to: {expected_rename}"
        )


def test_apply_stub_renaming() -> None:
    content_pre_renaming = _read_file_content(
        "test/data/avocado_stub/test_renaming_no_existing_avocado_names.c"
    )
    expected_content_post_renaming = """#include <stdlib.h>
#include <ctype.h>

int is_separator(int c)
{
    return c == '\\0' ||
        _avocado_isspace(c) ||
        _avocado_strchr(",.()+-/*=~%[];",c) != NULL;
}"""
    assert (
        avocado_stub_util.apply_stub_renaming(content_pre_renaming)
        == expected_content_post_renaming
    )


def test_apply_stub_renaming_existing_avocado_name() -> None:
    content_pre_renaming = _read_file_content(
        "test/data/avocado_stub/test_renaming_existing_avocado_names.c"
    )
    assert avocado_stub_util.apply_stub_renaming(content_pre_renaming) == content_pre_renaming
