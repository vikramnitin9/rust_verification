from verification import avocado_stub_util

from pathlib import Path

def _read_file_content(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")

avocado_renamer = avocado_stub_util.AvocadoIdentifierRenamer()


def test_stub_mapping() -> None:
    identifier_to_rename_data = avocado_stub_util.get_stub_mappings()
    assert len(identifier_to_rename_data) != 0, (
        "Expected a non-zero number of stub function renamings"
    )
    for identifier, rename_metadata in identifier_to_rename_data.items():
        expected_rename = avocado_stub_util.AVOCADO_FUNCTION_PREFIX + identifier
        actual_rename = avocado_stub_util.get_renamed_identifier(identifier, rename_metadata)

        assert actual_rename == expected_rename, (
            f"Expected {identifier} to be renamed to: {expected_rename}"
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
        avocado_renamer.rename_ansi_identifiers_to_avocado_identifiers(
            content_pre_renaming
        ).src_after_renaming
        == expected_content_post_renaming
    )


def test_apply_stub_renaming_existing_avocado_name() -> None:
    content_pre_renaming = _read_file_content(
        "test/data/avocado_stub/test_renaming_existing_avocado_names.c"
    )
    assert (
        avocado_renamer.rename_ansi_identifiers_to_avocado_identifiers(
            content_pre_renaming
        ).src_after_renaming
        == content_pre_renaming
    )
