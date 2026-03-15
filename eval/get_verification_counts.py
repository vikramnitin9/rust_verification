#!/opt/miniconda3/bin/python
# ruff: noqa: E402

"""Script to calculate metrics around functions verified by Avocado in a given C file."""

import argparse
import sys
from pathlib import Path

from diskcache import Cache  # ty: ignore

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from util import CFunction, ParsecProject
from verification import VerificationResult


def main() -> None:
    """TODO: Document me."""
    parser = argparse.ArgumentParser(
        description=("Calculate metrics around functions verified by Avocado in a given C file.")
    )
    parser.add_argument(
        "--file", type=str, required=True, help="Path to the .c file for which to report metrics."
    )
    parser.add_argument(
        "--path-to-cache-dir",
        type=str,
        required=True,
        help="Path to the directory holding the cache file used by Avocado's verifier.",
    )
    args = parser.parse_args()

    verifier_cache = Cache(args.path_to_cache_dir)
    parsec_project_for_file = ParsecProject(Path(args.file))
    for f in parsec_project_for_file.get_functions_in_topological_order():
        # TODO: Do something with the vresult(s) for each function.
        _get_vresults(verifier_cache, f)


def _get_vresults(cache: Cache, function: CFunction) -> list[VerificationResult]:
    return [
        vresult
        for vinput in cache.iterkeys()
        if (vresult := cache[vinput]) and vresult.get_function() == function
    ]


if __name__ == "__main__":
    main()
