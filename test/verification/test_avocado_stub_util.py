from verification import avocado_stub_util

from pathlib import Path


def _read_file_content(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")


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
        avocado_stub_util.apply_stub_renaming(content_pre_renaming)
        == expected_content_post_renaming
    )


def test_apply_stub_renaming_existing_avocado_name() -> None:
    content_pre_renaming = _read_file_content(
        "test/data/avocado_stub/test_renaming_existing_avocado_names.c"
    )
    assert avocado_stub_util.apply_stub_renaming(content_pre_renaming) == content_pre_renaming


def test_get_stub_with_nonexistent_file() -> None:
    assert not avocado_stub_util.get_stub_implementation("strchr", "nonsense.h"), (
        f"'nonsense.h' should not exist"
    )


def test_get_stub_with_nonexistent_function() -> None:
    assert not avocado_stub_util.get_stub_implementation("nonsense_function", "string.h"), (
        f"'nonsense_function' should not exist in 'string.h'"
    )

def test_get_stub() -> None:
    stub_implementation = """char *strchr(const char *src, int c)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(src),
                         "strchr zero-termination of string argument");
  __CPROVER_bool found;
  __CPROVER_size_t i;
  return found?src+i:0;
  #else
  for(__CPROVER_size_t i=0; ; i++)
  {
    if(src[i]==(char)c)
      return ((char *)src)+i; // cast away const-ness
    if(src[i]==0) break;
  }
  return 0;
  #endif
}"""
    assert avocado_stub_util.get_stub_implementation("strchr", "string.h") == stub_implementation

