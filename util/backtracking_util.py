"""Utilities for backtracking information."""

from dataclasses import dataclass

from .c_function import CFunction
from .json_util import parse_object
from .parsec_file import ParsecFile


@dataclass(frozen=True)
class BacktrackingInformation:
    """Represents backtracking information for specification generation.

    Attributes:
        function (CFunction): The function to backtrack to (i.e., regenerate specs for).
        reasoning (str): The reasoning provided by an LLM for backtracking.

    """

    function: CFunction
    reasoning: str


def parse_backtracking_info(llm_response: str, parsec_file: ParsecFile) -> BacktrackingInformation:
    """Return backtracking information parsed from an LLM response.

    Args:
        llm_response (str): The raw LLM response comprising backtracking information.
        parsec_file (ParsecFile): The ParsecFile from which to obtain the CFunction corresponding to
            the function to backtrack to.

    Raises:
        ValueError: Raised when the CFunction callee definition is missing from the ParsecFile.
        RuntimeError: Raised when the LLM response does not contain the 'callee' and 'reasoning'
            keys.

    Returns:
        BacktrackingInformation: Backtracking information parsed from an LLM response.
    """
    llm_response_dict = parse_object(llm_response)
    callee_name = llm_response_dict.get("callee")
    reasoning = llm_response_dict.get("reasoning")
    if callee_name and reasoning:
        if callee := parsec_file.get_function_or_none(function_name=str(callee_name)):
            return BacktrackingInformation(function=callee, reasoning=str(reasoning))
        msg = f"Callee '{callee_name}' was missing from the ParsecFile"
        raise ValueError(msg)
    msg = (
        "Backtracking strategy was missing information: "
        f"callee = {callee_name}, reasoning = {reasoning}"
    )
    raise RuntimeError(msg)
