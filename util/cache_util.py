"""Utility functions for working with the verification result cache."""

from __future__ import annotations

from collections import defaultdict
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from diskcache import Cache

    from verification import VerificationResult

    from .c_function import CFunction


def get_vresult_index(
    vresult_cache: Cache | None,
) -> defaultdict[CFunction, list[VerificationResult]]:
    """Return a dictionary of CFunction to VerificationResult(s) constructed from the given cache.

    Args:
        vresult_cache (Cache | None): The cache from which to construct the dictionary of CFunction
            to VerificationResult(s).

    Returns:
        defaultdict[CFunction, list[VerificationResult]]: The dictionary of CFunction to
            VerificationResult(s). Default value for keys is an empty list
    """
    function_to_vresults: dict[CFunction, list[VerificationResult]] = defaultdict(list)
    if vresult_cache is None:
        return function_to_vresults
    for vinput in vresult_cache.iterkeys():
        if vresult := vresult_cache[vinput]:
            function_to_vresults[vresult.get_function()].append(vresult)
    return function_to_vresults
