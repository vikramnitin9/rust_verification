#!/usr/bin/env python3
# ruff: noqa: E402

"""Script to generate verification summaries for functions verified by Avocado in a given C file."""

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from diskcache import Cache
from loguru import logger

REPO_ROOT = Path(__file__).resolve().parents[1]
# This statement causes Ruff to report "module-import-not-at-top-of-file" for the following imports.
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from collections import defaultdict
from dataclasses import asdict, dataclass

from eval import ClauseComplexity, get_complexity
from util import CFunction, CFunctionGraph, FunctionSpecification, get_destination_path
from verification import VerificationResult, VerificationStatus


class StaleCacheEntryError(Exception):
    """A stale cache entry in the cache.

    The verifier cache is a map from VerifierInput(s) to VerificationResult(s). This class
    represents two possible error cases:

        1. A cache entry is expired (i.e., an input no longer maps to a result).
        2. An entry comprises a VerificationResult that has a CFunction whose file_name field refers
           to a file that is no longer on disk.
    """

    def __init__(self, cause: Exception) -> None:
        """Construct a new StaleCacheEntryError."""
        super().__init__(f"Stale cache entry: {cause}")


@dataclass(frozen=True)
class CacheLookupResult:
    """The results of a cache lookup.

    Attributes:
        function (CFunction): The key for this cache lookup result.
        results (list[VerificationResult | StaleCacheEntryError]): The successfully-fetched
            verification results and/or stale cache entry errors.
    """

    function: CFunction
    results: list[VerificationResult | StaleCacheEntryError]


@dataclass(frozen=True)
class SpecWithComplexity:
    """A specification paired with its clause complexity.

    Attributes:
        spec (FunctionSpecification): The specification.
        precondition_complexity (list[ClauseComplexity]): Clause complexities for preconditions.
        postcondition_complexity (list[ClauseComplexity]): Clause complexities for postconditions.
    """

    spec: FunctionSpecification
    precondition_complexity: list[ClauseComplexity]
    postcondition_complexity: list[ClauseComplexity]


@dataclass(frozen=True)
class VerificationSummary:
    """Immutable summary of verification results for a function.

    This class is used as a lightweight representation of verification results (without much of the
    data that is present in a VerificationResult) that can be used to generate tables and figures.

    Unlike a VerificationResult (see verification/verification_result.py), a VerificationSummary
    contains less information about each individual verifier run (e.g., it does not have a full
    CFunction field, nor does it have the source code that was verified). It encapsulates
    information about the entire set of specifications that were generated for a function in the
    form of SpecWithComplexity objects.

    Attributes:
        function_name (str): The name of the function.
        verifying_specs (list[SpecWithComplexity]): The list of verifying specs with complexity.
        assumed_specs (list[SpecWithComplexity]): The list of assumed specs with complexity.
        failing_specs (list[SpecWithComplexity]): The list of failing specs with complexity.
        stale_cache_entries (list[StaleCacheEntryError]): The list of stale cache entry errors.
    """

    function_name: str
    verifying_specs: list[SpecWithComplexity]
    assumed_specs: list[SpecWithComplexity]
    failing_specs: list[SpecWithComplexity]
    stale_cache_entries: list[StaleCacheEntryError]

    @classmethod
    def empty(cls, function_name: str) -> "VerificationSummary":
        """Construct an empty immutable verification summary.

        Args:
            function_name (str): The name of the function for which to construct an empty
                verification summary.

        Returns:
            VerificationSummary: An empty verification summary.
        """
        return cls(
            function_name,
            verifying_specs=[],
            assumed_specs=[],
            failing_specs=[],
            stale_cache_entries=[],
        )

    def to_dict(self) -> dict[str, Any]:
        """Return the dictionary representation of this verification summary.

        Returns:
            dict[str, Any]: The dictionary representation of this verification summary.
        """
        vsummary_dict = asdict(self)
        # Convert the `stale_cache_entries` field, which is not JSON-serializable, into strings.
        del vsummary_dict["stale_cache_entries"]
        vsummary_dict["lookup_errors"] = [
            str(stale_entry) for stale_entry in self.stale_cache_entries
        ]
        return vsummary_dict


def main() -> None:
    """Generate verification summaries for functions in a C file run through the Avocado verifier.

    For usage information, run: ./eval/get_verification_summary.py -h

    This script generates verification summaries for each function in the file as entries in a JSON
    object.

    See eval/README.md for a detailed description of result of this script.

    Implementation detail: Avocado caches the result of verification runs (i.e., the result of
    invoking CBMC on the specs it generates) in a global cache file (see `main.py#VERIFIER_CACHE),
    the path to which must be provided when invoking this script.
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
    path_to_cache_dir = args.path_to_cache_dir

    if not Path(path_to_cache_dir).exists():
        msg = f"'{path_to_cache_dir}' does not exist"
        raise ValueError(msg)

    verifier_cache = Cache(path_to_cache_dir)
    path_to_file_with_specs = get_destination_path(Path(args.file), "/app/specs")
    function_to_lookup_results: dict[CFunction, CacheLookupResult] = (
        _get_cached_results_for_functions_in_file(verifier_cache, path_to_file_with_specs)
    )

    verification_summary_for_file = {}
    verification_summary_for_file["file_name"] = args.file
    verification_summary_for_file["functions"] = []
    for function, lookup_result in function_to_lookup_results.items():
        vsummary = _get_verification_summary(function, lookup_result)
        verification_summary_for_file["functions"].append(vsummary.to_dict())

    # Populate the result with empty verification summaries for functions that have yet to be run
    # through Avocado.
    verification_summary_for_file["functions"] = [
        *verification_summary_for_file["functions"],
        *[
            VerificationSummary.empty(name).to_dict()
            for name in _get_names_of_unprocessed_functions(args.file, function_to_lookup_results)
        ],
    ]

    # Collapse summaries for functions with the same name (e.g., from cache entries with distinct
    # CFunction keys that share a name). This is fine, given we're running on files individually.
    merged_summaries: dict[str, Any] = {}
    for vsummary in verification_summary_for_file["functions"]:
        function_name = vsummary["function_name"]
        if function_name not in merged_summaries:
            merged_summaries[function_name] = vsummary
        else:
            merged_summaries[function_name]["verifying_specs"].extend(vsummary["verifying_specs"])
            merged_summaries[function_name]["failing_specs"].extend(vsummary["failing_specs"])
            merged_summaries[function_name]["assumed_specs"].extend(vsummary["assumed_specs"])
            merged_summaries[function_name]["lookup_errors"].extend(vsummary["lookup_errors"])
    verification_summary_for_file["functions"] = list(merged_summaries.values())

    num_verified_functions = _get_num_verified_functions(verification_summary_for_file)
    num_assumed_functions = _get_num_functions_with_assumed_specs(verification_summary_for_file)

    logger.info(
        "{} function(s) in {}\n\t{} verified\n\t{} assumed",
        len(verification_summary_for_file["functions"]),
        args.file,
        num_verified_functions,
        num_assumed_functions,
    )

    with _get_result_json_name(args.file).open(mode="w") as f:
        json.dump(verification_summary_for_file, f, indent=4)


def _get_cached_results_for_functions_in_file(
    cache: Cache, path_to_file: Path
) -> dict[CFunction, CacheLookupResult]:
    """Return cache lookup results for functions associated with a specific file.

    This helper groups cache entries by function and keeps only entries whose
    VerificationResult points to path_to_file. It also records stale/expired cache
    entries as StaleCacheEntryError objects so callers can surface lookup errors
    in summaries.

    Args:
        cache (Cache): Verifier cache that maps verification inputs to results.
        path_to_file (Path): File path used to filter verification results.

    Returns:
        dict[CFunction, CacheLookupResult]: Mapping from function to its lookup
            results (verification results and/or stale cache entry errors).
    """
    function_to_vresults_or_lookup_errors = defaultdict(list)
    for vinput in cache.iterkeys():
        # DiskCache does not offer a function to iterate over cache entries (e.g., .values() or
        # .items()) because it aims to support concurrent reads/writes, so this explicit item lookup
        # via keys is necessary.
        vresult = cache[vinput]
        if not vresult:
            msg = f"Expired cache entry for '{vinput.function.name}'"
            function_to_vresults_or_lookup_errors[vinput.function].append(
                StaleCacheEntryError(Exception(msg))
            )
        elif not Path(vresult.get_function().file_name).exists():
            msg = (
                f"Stale cache entry for '{vresult.get_function().name}' in deleted file "
                f"'{vresult.get_function().file_name}'"
            )
            function_to_vresults_or_lookup_errors[vinput.function].append(
                StaleCacheEntryError(Exception(msg))
            )
        elif Path(vresult.get_function().file_name) == path_to_file:
            function_to_vresults_or_lookup_errors[vinput.function].append(vresult)
    return {
        function: CacheLookupResult(function, results)
        for function, results in function_to_vresults_or_lookup_errors.items()
    }


def _get_names_of_unprocessed_functions(
    c_file: str, function_to_lookup_results: dict[CFunction, CacheLookupResult]
) -> set[str]:
    """Return the names of functions for which the cache did not contain a verifier result.

    A function does not have a verifier result (which either says a function has been successfully
    verified, or failed to verify) if it has not yet been processed via Avocado.

    Args:
        c_file (str): The C file from which to get function names.
        function_to_lookup_results (dict[CFunction, CacheLookupResult]): The cache lookup results.

    Returns:
        set[str]: The names of unprocessed functions.
    """
    all_functions_in_file = {
        f.name for f in CFunctionGraph.get_functions_defined_in_file(Path(c_file))
    }
    functions_with_lookup_results = {f.name for f in function_to_lookup_results}
    return all_functions_in_file.difference(functions_with_lookup_results)


def _get_verification_summary(
    function: CFunction, lookup_result: CacheLookupResult
) -> VerificationSummary:
    """Compute statistics and summarize a function's verifier cache lookup result.

    Args:
        function (CFunction): The function for which to summarize a verifier cache lookup result.
        lookup_result (CacheLookupResult): The verifier cache lookup result for `function`.

    Returns:
        VerificationSummary: The verification summary for the function.
    """
    verifying_specs = []
    assumed_specs = []
    failing_specs = []
    lookup_errors = []
    for result in lookup_result.results:
        if isinstance(result, VerificationResult):
            spec_with_complexity = SpecWithComplexity(
                result.get_spec(), *_get_complexity_for_clauses(result.get_spec())
            )
            match result.status:
                case VerificationStatus.SUCCEEDED:
                    verifying_specs.append(spec_with_complexity)
                case VerificationStatus.ASSUMED:
                    assumed_specs.append(spec_with_complexity)
                case VerificationStatus.FAILED:
                    failing_specs.append(spec_with_complexity)
        else:
            lookup_errors.append(result)
    return VerificationSummary(
        function.name, verifying_specs, assumed_specs, failing_specs, lookup_errors
    )


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


def _get_num_verified_functions(file_summary: dict[str, Any]) -> int:
    """Return the number of functions with at least one verifying specification.

    Args:
        file_summary (dict[str, Any]): A verification summary for a file.

    Returns:
        int: The count of functions that have at least one verifying specification.
    """
    verified_functions = [
        function_summary
        for function_summary in file_summary["functions"]
        if len(function_summary["verifying_specs"]) > 0
    ]
    return len(verified_functions)


def _get_num_functions_with_assumed_specs(file_summary: dict[str, Any]) -> int:
    """Return the number of functions that only have assumed (or failing) specifications.

    Args:
        file_summary (dict[str, Any]): A verification summary for a file.

    Returns:
        int: The count of functions that only have assumed (or failing) specifications.
    """
    functions_with_assumed_specs_with_no_successfully_verifying_specs = [
        function_summary
        for function_summary in file_summary["functions"]
        if len(function_summary["assumed_specs"]) > 0
        and len(function_summary["verifying_specs"]) == 0
    ]
    return len(functions_with_assumed_specs_with_no_successfully_verifying_specs)


if __name__ == "__main__":
    main()
