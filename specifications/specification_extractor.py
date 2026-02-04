"""Utility module for specification extraction from LLM responses."""

from util import FunctionSpecification, SpecGenGranularity, code_extraction_util


def extract_spec_from_response(
    llm_response: str, granularity: SpecGenGranularity
) -> FunctionSpecification | None:
    """Return a FunctionSpecification parsed from the LLM response.

    Args:
        llm_response (str): The raw LLM response.
        granularity (SpecGenGranularity): The specification generation granularity, i.e., generate
            specifications in the form of entire clauses, or in the form of expressions that are
            input to clauses.

    Returns:
        FunctionSpecification | None: The specification parsed from the LLM response.
    """
    match granularity:
        case SpecGenGranularity.CLAUSE:
            return code_extraction_util.parse_clauses_for_spec(llm_response)
        case SpecGenGranularity.EXPRESSION:
            return code_extraction_util.parse_expressions_for_spec(llm_response)
        case _:
            msg = f"Unexpected specification generation granularity: {granularity}"
            raise ValueError(msg)
