"""Utilities for backtracking information."""

from dataclasses import dataclass

from .json_util import parse_object


@dataclass(frozen=True)
class BacktrackingInformation:
    """Represents backtracking information for specification generation.

    Attributes:
        callee_name (str): The name of the callee to backtrack to (i.e., regenerate specs for).
        postcondition_strengthening_description (str): The description of the
            postcondition-strengthening change that should be made to the callee specification.

    """

    callee_name: str
    postcondition_strengthening_description: str


def parse_backtracking_info(llm_response: str) -> BacktrackingInformation:
    """Return backtracking information parsed from an LLM response.

    Args:
        llm_response (str): The raw LLM response comprising backtracking information.

    Raises:
        RuntimeError: Raised when the LLM response does not contain the 'callee' and
            'postcondition_strengthening_description' keys.

    Returns:
        BacktrackingInformation: Backtracking information parsed from an LLM response.
    """
    llm_response_dict = parse_object(llm_response)
    callee_name = llm_response_dict.get("callee")
    postcondition_change_for_callee = llm_response_dict.get("postcondition_change_for_callee")
    if callee_name and postcondition_change_for_callee:
        return BacktrackingInformation(
            callee_name=callee_name,
            postcondition_strengthening_description=str(postcondition_change_for_callee),
        )
    msg = (
        "Backtracking strategy was missing information: "
        f"callee = {callee_name}, "
        f"postcondition_change_for_callee = {postcondition_change_for_callee}"
    )
    raise RuntimeError(msg)
