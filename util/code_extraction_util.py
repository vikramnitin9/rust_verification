"""Utility functions for extracting source code from text."""

from .json_util import parse_object

# MDE: Did we discuss having the LLM return only the specs, without repeating the function's source
# code?


def extract_function_source_code(text: str) -> str:
    """Extract the source code part of an LLM response.

    An LLM is prompted to return a string in the following JSON format:

    # TODO: just ask for the specification.  Then the LLM is less likely to hallucinate a
    # change in the function's source code.
    # Also make this more structured, such as separating the pre- and post-conditions.
    # See https://github.com/vikramnitin9/rust_verification/issues/66

        { "function_with_specs": "<SOURCE CODE>" }

    This function extracts the <SOURCE CODE> part.

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
