"""Utility functions for working with string representations of JSON objects."""

import json
from json import JSONDecodeError
from typing import Any


def parse_object(text: str) -> dict[str, Any]:
    """Return a Python dictionary parsed from a string representation of a JSON object.

    Note: This function should not be used to parse a JSON array from its string representation.

    Args:
        text (str): A string representation of a JSON object.

    Raises:
        RuntimeError: Raised when a JSON object fails to be parsed from the given text.

    Returns:
        dict[str, Any]: A Python dictionary parsed from a string representation of a JSON object.
    """
    text = text.strip()
    if text.startswith("```json") or text.endswith("```"):
        text = text.strip().removeprefix("```json").removesuffix("```")
    try:
        return json.loads(text)
    except JSONDecodeError as je:
        msg = f"Failed to parse a JSON object from: '{text}', error = {je}"
        raise RuntimeError(msg) from je
