"""Module for utility functions for working with Avocado stubs."""

import pickle as pkl
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


def apply_stub_renaming(src_file_path: Path, stub_mappings: dict[str, RenameMetadata]) -> None:
    """TODO: Document me.

    Args:
        src_file_path (Path): _description_
        stub_mappings (dict[str, RenameMetadata]): _description_
    """
