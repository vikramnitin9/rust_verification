"""Module for utility functions for working with Avocado stubs."""

import pickle as pkl
from dataclasses import dataclass
from pathlib import Path
from typing import cast


@dataclass(frozen=True)
class RenameMetadata:
    """Capture metadata for renaming ANSI-C functions to Avocado stubs.

    Attributes:
        avocado_name (str): The ANSI-C function's name as an Avocado stub.
        original_file_path (Path): The path to the original file in which the function is defined.
    """

    avocado_name: str
    original_file_path: Path


DEFAULT_STUB_MAPPINGS = "verification/cbmc_stubs/c_stub_rename_map.pkl"


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
