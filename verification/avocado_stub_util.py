"""Module for utility functions for working with Avocado stubs."""

from __future__ import annotations

import pickle as pkl
from dataclasses import dataclass
from pathlib import Path
from typing import cast


@dataclass(frozen=True)
class RenameData:
    """Metadata for renaming functions in libraries defined in the ANSI-C standard to Avocado stubs.

    The CBMC verifier includes its own copy of stub functions in libraries defined in the ANSI-C
    standard that it uses for verifying client code that makes use them. This can sometimes lead to
    unexpected issues related to internal C functions that are used by its copy of stub functions:

        https://github.com/diffblue/cbmc/issues/8844

    Avocado stubs aim to mitigate this issue by ensuring only the functions directly in the copy of
    the standard library are used. However, standard library functions cannot be defined twice,
    and so each function (i.e., stub) is prepended with `avocado_` to avoid naming collisions.


    See `generate_avocado_stubs.py` for how Avocado stubs are generated.

    Attributes:
        avocado_name (str): The function's name as an Avocado stub.
        file_path (Path): The path to the original file in which the function is defined.
    """

    avocado_name: str
    file_path: Path


DEFAULT_STUB_MAPPINGS = "verification/cbmc_stubs/c_stub_rename_map.pkl"


def get_stub_mappings(
    path_to_stub_mappings: str = DEFAULT_STUB_MAPPINGS,
) -> dict[str, RenameData]:
    """Return the stub mappings for Avocado stubs for functions declared in the ANSI-C standard.

    Args:
        path_to_stub_mappings (str, optional): Path to stub mappings. Defaults to
            DEFAULT_STUB_MAPPINGS.

    Returns:
        dict[str, RenameData]: A mapping from the original C function name to rename data.
    """
    with Path(path_to_stub_mappings).open(mode="rb") as f:
        data = pkl.load(f)
        return cast("dict[str, RenameData]", data)
