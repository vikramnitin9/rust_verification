#!/opt/miniconda3/bin/python
# ruff: noqa: E402, PERF203

"""Script to generate verification summaries for functions verified by Avocado in a given C file."""

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from diskcache import Cache  # ty: ignore

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from dataclasses import asdict, dataclass

from eval import ClauseComplexity, get_complexity
from util import CFunction, FunctionSpecification, ParsecProject
from verification import VerificationResult


class CacheLookupError(Exception):
    """Represent a lookup error in the cache.

    This might happen when a lookup fetches a CFunction whose `file_name` field refers to a file
    that no longer exists.
    """


@dataclass(frozen=True)
class CacheLookupResult:
    """Represent the results of a cache lookup.

    A CFunction is the key for a cache lookup result.

    Attributes:
        function (CFunction): The key for this cache lookup result.
        results (list[VerificationResult | CacheLookupError]): The successfully-fetched
            verification results, or lookup errors.
    """

    function: CFunction
    results: list[VerificationResult | CacheLookupError]


@dataclass(frozen=True)
class SpecWithComplexity:
    """A specification paired with its clause complexity.

    Attributes:
        spec (FunctionSpecification): The specification.
        precondition_complexity (list[ClauseComplexity]): Clause complexity for preconditions.
        postcondition_complexity (list[ClauseComplexity]): Clause complexity for postconditions.
    """

    spec: FunctionSpecification
    precondition_complexity: list[ClauseComplexity]
    postcondition_complexity: list[ClauseComplexity]


@dataclass(frozen=True)
class VerificationSummary:
    """Summary of verification results for a function.

    Unlike a VerificationResult (see verification/verification_result.py), a VerificationSummary
    contains less information about each individual verifier run (e.g., it does not have a full
    CFunction field, nor does it have the source code that was verified). It encapsulates
    information about the entire set of specifications that were generated for a function in the
    form of SpecWithComplexity objects.

    Attributes:
        function_name (str): The name of the function.
        verifying_specs (list[SpecWithComplexity]): The list of verifying specs with complexity.
        failing_specs (list[SpecWithComplexity]): The list of failing specs with complexity.
        lookup_errors (list[CacheLookupError]): The list of cache lookup errors.
    """

    function_name: str
    verifying_specs: list[SpecWithComplexity]
    failing_specs: list[SpecWithComplexity]
    lookup_errors: list[CacheLookupError]

    def to_dict(self) -> dict[str, Any]:
        """Return the dictionary representation of this verification summary.

        Returns:
            dict[str, Any]: The dictionary representation of this verification summary.
        """
        vsummary_dict = asdict(self)
        vsummary_dict["lookup_errors"] = [str(lookup_err) for lookup_err in self.lookup_errors]
        return vsummary_dict


def main() -> None:
    """Generate verification summaries for functions in a C file run through the Avocado verifier.

    Run: ./eval/get_verification_summary.py -h for usage information.

    This script generates verification summaries for each function in the file as entries in a JSON

    See eval/README.md for a detailed description of result of this script.

    Implementation detail: Avocado caches the result of verification runs (i.e., the result of
    invoking CBMC on the specs it generates) in global cache file, the path to which must be
    provided in invoking this script.
    """
    parser = argparse.ArgumentParser(
        description=(
            "Generate verification summaries for functions run through the Avocado verifier in a C"
            " file."
        )
    )
    parser.add_argument(
        "--file",
        type=str,
        required=True,
        help="Path to the C file containing the functions for"
        " which to generate verification summaries.",
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
        verification_summary_for_file["functions"].append(vsummary.to_dict())

    with _get_result_json_name(args.file).open(mode="w") as f:
        json.dump(verification_summary_for_file, f, indent=4)


def _get_lookup_result(cache: Cache, function: CFunction) -> CacheLookupResult:
    """Return the verification cache lookup result for the given function.

    The function is the key for the lookup result.

    Args:
        cache (Cache): The cache from which to look up verification results.
        function (CFunction): The function for which to look up verification results.

    Returns:
        CacheLookupResult: The verification cache lookup result for the given function.
    """
    results = []
    for vinput in cache.iterkeys():
        # DiskCache does not offer a function to iterate over cache entries (e.g., .values() or
        # .items()) because it aims to support concurrent reads/writes, so this explicit item lookup
        # via keys is necessary.
        try:
            if (vresult := cache[vinput]) and vresult.get_function() == function:
                results.append(vresult)
        except Exception as err:
            # A lookup error might occur if a comparison is made for functions in a vresult where
            # the original file is no longer on disk.
            results.append(CacheLookupError(err))
            continue

    return CacheLookupResult(function, results)


def _get_verification_summary(
    function: CFunction, lookup_result: CacheLookupResult
) -> VerificationSummary:
    """Compute statistics and summarize a function's verifier cache lookup result.

    Args:
        function (CFunction): The function for which to summarize a verifier cache lookup result.
        lookup_result (CacheLookupResult): The verifier cache lookup result.

    Returns:
        VerificationSummary: The verification summary for the function.
    """
    verifying_specs = []
    failing_specs = []
    lookup_errors = []
    for result in lookup_result.results:
        if isinstance(result, VerificationResult):
            spec_with_complexity = SpecWithComplexity(
                result.get_spec(), *_get_complexity_for_clauses(result.get_spec())
            )
            if result.succeeded:
                verifying_specs.append(spec_with_complexity)
            else:
                failing_specs.append(spec_with_complexity)
        else:
            lookup_errors.append(result)
    return VerificationSummary(function.name, verifying_specs, failing_specs, lookup_errors)


def _get_result_json_name(c_file: str) -> Path:
    """Return the path to the output JSON given a C file.

    For a file, e.g., 'foo/bar/baz.c', return the path to its JSON result file, i.e.,
    'foo/bar/baz-verification-summary.json'

    See eval/README.md for a detailed description of the schema of the JSON file.

    Args:
        c_file (str): The C file for which to generate a JSON file.

    Returns:
        Path: The path to the JSON file to be generated.
    """
    path_to_input = Path(c_file)
    return path_to_input.parent / f"{path_to_input.stem}-verification-summary.json"


def _get_complexity_for_clauses(
    spec: FunctionSpecification,
) -> tuple[list[ClauseComplexity], list[ClauseComplexity]]:
    """Return the clause complexity for each clause in the given specification.

    Args:
        spec (FunctionSpecification): The specification for which to generate clause complexity.

    Returns:
        tuple[list[ClauseComplexity], list[ClauseComplexity]]: The clause complexity for each clause
            in the given specification.
    """
    return (
        [get_complexity(clause) for clause in spec.preconditions],
        [get_complexity(clause) for clause in spec.postconditions],
    )


if __name__ == "__main__":
    main()
