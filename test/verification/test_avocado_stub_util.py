import pytest

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
#include "string.h"
#include <time.h> // `time` is renamed function name, but this header should not be renamed.

int is_separator(int c)
{
    return c == '\\0' ||
        _avocado_isspace(c) ||
        _avocado_strchr(",.()+-/*=~%[];",c) != NULL;
}"""
    rename_result = avocado_renamer.rename_ansi_identifiers_to_avocado_identifiers(
        content_pre_renaming)
    assert rename_result.src_after_renaming == expected_content_post_renaming
    assert rename_result.get_headers_for_renamed_functions() == {"ctype.h", "string.h"}


def test_apply_stub_renaming_existing_avocado_name() -> None:
    content_pre_renaming = _read_file_content(
        "test/data/avocado_stub/test_renaming_existing_avocado_names.c"
    )
    rename_result = avocado_renamer.rename_ansi_identifiers_to_avocado_identifiers(content_pre_renaming)
    assert rename_result.src_after_renaming == content_pre_renaming

def test_apply_stub_renaming_existing_cbmc_specs() -> None:
    content_pre_renaming = _read_file_content(
        "test/data/avocado_stub/test_renaming_with_cbmc_specs.c"
    )
    expected_content_post_renaming = """#include <stdlib.h>
#include <ctype.h>
#include "string.h"
#include <time.h> // `time` is renamed function name, but this header should not be renamed.

int is_separator(int c)
__CPROVER_ensures(__CPROVER_return_value == (c == '\\0' || _avocado_isspace(c) || _avocado_strchr(",.()+-/*=~%[];",c) != NULL))
__CPROVER_ensures((__CPROVER_return_value == 0) ==> (c == '\\0' || _avocado_isspace(c) || _avocado_strchr(",.()+-/*=~%[];",c) == NULL))
{
    return c == '\\0' ||
        _avocado_isspace(c) ||
        _avocado_strchr(",.()+-/*=~%[];",c) != NULL;
}"""
    rename_result = avocado_renamer.rename_ansi_identifiers_to_avocado_identifiers(content_pre_renaming)
    assert rename_result.src_after_renaming == expected_content_post_renaming

def test_get_stub() -> None:
    header_basename = "string.h"
    parsed_header = avocado_stub_util.load_stub_file(header_basename)
    assert parsed_header, f"{header_basename} should have parsed correctly"
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
    assert avocado_stub_util.get_stub_implementation_from_parsed_source("strchr", parsed_header) == stub_implementation
