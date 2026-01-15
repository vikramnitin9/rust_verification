"""Utility functions for extracting source code from text."""

from .json_util import parse_object


def extract_function_source_code(text: str) -> str:
    """Extract the source code part of an LLM response.

    An LLM is prompted to return a string in the following JSON format:

        { "function_with_specs": "<SOURCE CODE>" }

    This function extracts the <SOURCE CODE> part.

    An alternate implementation would be to have the LLM generate *just* the specifications
    (i.e., avoid having it generate the original function, as well). The initial implementation
    asked the LLM to re-generate the entire function, so we kept it as such.

    An issue to possibly implement the future approach is open at:

        https://github.com/vikramnitin9/rust_verification/issues/66

    Args:
        text (str): The full response from an LLM.

    Returns:
        str: The source code part of an LLM.
    """
    llm_response = parse_object(text)
    if function := llm_response.get("function_with_specs"):
        return function
    msg = f"The LLM returned valid JSON, but was missing the 'function_with_specs' key: {text}"
    raise RuntimeError(msg)
