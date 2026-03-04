"""Module for utility functions for working with Avocado stubs."""

import pickle as pkl
import re
from dataclasses import dataclass
from pathlib import Path
from typing import cast

AVOCADO_STUB_DIR = "verification/cbmc_stubs"
DEFAULT_STUB_MAPPINGS = f"{AVOCADO_STUB_DIR}/c_stub_rename_map.pkl"


@dataclass(frozen=True)
class RenameMetadata:
    """Capture metadata for renaming ANSI-C functions to Avocado stubs.

    Attributes:
        avocado_name (str): The ANSI-C function's name as an Avocado stub.
        original_file_path (Path): The path to the original file in which the function is defined.
    """

    avocado_name: str
    original_file_path: Path


def apply_stub_renaming(file_content: str) -> str:
    """Return the file content after stub function replacements have been applied.

    Args:
        file_content (str): The content of the file to which to apply renaming.

    Returns:
        str: The file content after stub function replacements have been applied.
    """
    file_content_with_renaming = file_content
    for original_name, rename_metadata in get_stub_mappings().items():
        # Don't replace names twice (i.e., replace only exact matches)
        name_to_replace_pattern = r"\b" + original_name + r"\b"
        file_content_with_renaming = re.sub(
            name_to_replace_pattern, rename_metadata.avocado_name, file_content_with_renaming
        )
    return file_content_with_renaming


def get_stub_mappings(
    path_to_stub_mappings: str = DEFAULT_STUB_MAPPINGS,
) -> dict[str, RenameMetadata]:
    """Return the stub mappings for Avocado's ANSI-C libraries.

    Args:
        path_to_stub_mappings (str, optional): Path to stub mappings. Defaults to
            DEFAULT_STUB_MAPPINGS.

    Returns:
        dict[str, RenameMetadata]: A mapping from the original C function name to rename metadata.
    """
    with Path(path_to_stub_mappings).open(mode="rb") as f:
        data = pkl.load(f)
        return cast("dict[str, RenameMetadata]", data)
