from verification import avocado_stub_util

from pathlib import Path


def _read_file_content(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")


def test_stub_mapping() -> None:
    original_name_to_rename_metadata = avocado_stub_util.get_stub_mappings()
    assert len(original_name_to_rename_metadata) != 0, (
        "Expected a non-zero number of stub function renamings"
    )

    for original_name, rename_metadata in original_name_to_rename_metadata.items():
        expected_rename = f"avocado_{original_name}"

        assert rename_metadata.avocado_name == expected_rename, (
            f"Expected {original_name} in {rename_metadata.original_file_path.name} to be renamed to: {expected_rename}"
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
        avocado_isspace(c) ||
        avocado_strchr(",.()+-/*=~%[];",c) != NULL;
}"""
    assert (
        avocado_stub_util.apply_stub_renaming(content_pre_renaming)
        == expected_content_post_renaming
    )


def test_apply_stub_renaming_existing_avocado_names() -> None:
    content_pre_renaming = _read_file_content(
        "test/data/avocado_stub/test_renaming_existing_avocado_names.c"
    )
    assert avocado_stub_util.apply_stub_renaming(content_pre_renaming) == content_pre_renaming
