"""Utility functions for extracting source code from text."""

from .text_util import get_value_of_field_with_key


def extract_function(text: str) -> str:
    """Extract the source code part of an LLM response.

    An LLM is prompted to return a string in the following JSON format:

        { "function_with_specs": "<SOURCE CODE>" }

    This function extracts the <SOURCE CODE> part.

    Args:
        text (str): The full response from an LLM.

    Returns:
        str: The source code part of an LLM.
    """
    return get_value_of_field_with_key(text, key="function_with_specs")
