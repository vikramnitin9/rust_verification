#!/opt/miniconda3/bin/python
# ruff: noqa: E402, PERF203

"""Script to calculate metrics around functions verified by Avocado in a given C file."""

import argparse
import json
import sys
from pathlib import Path

from diskcache import Cache  # ty: ignore

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from dataclasses import asdict, dataclass

from util import CFunction, FunctionSpecification, ParsecProject
from verification import VerificationResult


class CacheLookupError(Exception):
    """Represent a lookup error in the cache.

    This might happen when a lookup fetches a function that has a dangling pointer to a file that
    no longer exists.
    """


@dataclass(frozen=True)
class CacheLookupResult:
    """Represent the results of a cache lookup.

    Attributes:
        results (list[VerificationResult | CacheLookupError]): The successfully-fetched
            verification results, or lookup errors.
    """

    results: list[VerificationResult | CacheLookupError]


@dataclass(frozen=True)
class VerificationSummary:
    """Summary of verification results for a function.

    Attributes:
        function_name (str): The name of the function.
        verifying_specs (list[FunctionSpecification]): The list of verifying specs.
        failing_specs (list[FunctionSpecification]): The list of failing specs.
        lookup_errors (list[CacheLookupError]): The list of any cache lookup errors.
    """

    function_name: str
    verifying_specs: list[FunctionSpecification]
    failing_specs: list[FunctionSpecification]
    lookup_errors: list[CacheLookupError]


def main() -> None:
    """Script to calculate metrics for functions run through the Avocado verifier.

    Avocado caches the result of verification runs (i.e., the result of invoking CBMC the specs
    it generates) in a cache file. This script aids in the automation of the analysis of verifier
    runs. It reports the following numbers for each function in the provided C file:

        - The number of specs that have successfully verified.
        - The number of spec that have failed to be successfully verified.
        - The number of *unique* specs that have successfully verified.
        - The number of *unique* specs that have failed to be successfully verified.

    """
    parser = argparse.ArgumentParser(
        description=("Calculate for functions run through the Avocado verifier in a given C file.")
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
    function_to_lookup_results: dict[CFunction, CacheLookupResult] = {}
    for f in parsec_project_for_file.get_functions_in_topological_order():
        function_to_lookup_results[f] = _get_lookup_result(verifier_cache, f)

    verification_summary_for_file = {}
    verification_summary_for_file["file_name"] = args.file
    verification_summary_for_file["functions"] = []
    for function, lookup_result in function_to_lookup_results.items():
        vsummary = _get_verification_summary(function, lookup_result)
        verification_summary_for_file["functions"].append(asdict(vsummary))

    with _get_result_json_name(args.file).open(mode="w") as f:
        json.dump(verification_summary_for_file, f, indent=4)


def _get_lookup_result(cache: Cache, function: CFunction) -> CacheLookupResult:
    """Return the verification cache lookup result for the given function.

    Args:
        cache (Cache): The cache from which to look up verification results.
        function (CFunction): The function for which to look up verification results.

    Returns:
        CacheLookupResult: The verification cache lookup result for the given function.
    """
    results = []
    for vinput in cache.iterkeys():
        try:
            if (vresult := cache[vinput]) and vresult.get_function() == function:
                results.append(vresult)
        except Exception as e:
            results.append(CacheLookupError(e))
            continue

    return CacheLookupResult(results)


def _get_verification_summary(
    function: CFunction, lookup_result: CacheLookupResult
) -> VerificationSummary:
    """Compute statistics and summarize a function's verifier cache lookup result.

    Args:
        function (CFunction): The function for which to summarize a verifier cache lookup result.
        lookup_result (CacheLookupResult): The verifier cache lookup result.

    Returns:
        VerificationSummary: The verification summary.
    """
    # All vresults.
    vresults = [
        result for result in lookup_result.results if isinstance(result, VerificationResult)
    ]

    # Verifying specs
    verifying_specs = [vresult.get_spec() for vresult in vresults if vresult.succeeded]

    # Failing specs
    failing_specs = [
        failing_spec
        for vresult in vresults
        if (failing_spec := vresult.get_spec()) and failing_spec not in set(verifying_specs)
    ]

    # Lookup errors
    lookup_errors = [
        result for result in lookup_result.results if isinstance(result, CacheLookupError)
    ]

    return VerificationSummary(function.name, verifying_specs, failing_specs, lookup_errors)


def _get_result_json_name(input_file: str) -> Path:
    """Return the path to the output JSON given an input file.

    For a file, e.g., 'foo/bar/baz.c', return the path to its JSON result file, i.e.,
    'foo/bar/baz-verification-summary.json'

    Args:
        input_file (str): The input file for which to generate a JSON file.

    Returns:
        Path: The path to the JSON file to be generated.
    """
    path_to_input = Path(input_file)
    return path_to_input.parent / f"{path_to_input.stem}-verification-summary.json"


if __name__ == "__main__":
    main()
