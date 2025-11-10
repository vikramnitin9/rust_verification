"""Utility functions for extracting source code from text."""

import json
from json import JSONDecodeError


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
    text = text.strip()
    if text.startswith("```json") or text.endswith("```"):
        # The LLM likely did not follow instructions to return just the plain object.
        text = text.strip().removeprefix("```json").removesuffix("```")
    try:
        return str(json.loads(text)["function_with_specs"])
    except JSONDecodeError as je:
        msg = f"The LLM failed to return a valid JSON object: {text}, error = {je}"
        raise RuntimeError(msg) from je
    except KeyError as ke:
        msg = f"The LLM returned valid JSON, but was missing the 'function_with_specs' key: {text}"
        raise RuntimeError(msg) from ke
