"""Utility functions for working with string representations of JSON objects."""

import json
import re
from json import JSONDecodeError
from typing import Any


def parse_object(text: str) -> dict[str, Any]:
    r"""Return a Python dictionary parsed from a string representation of a JSON object.

    Note: This function should not be used to parse a JSON array from its string representation.

    Before parsing, the following pre-processing steps are applied:

    1. Markdown code fences (` ```json ... ``` `) are stripped, since LLMs sometimes wrap JSON
       output in fences.
    2. Lone backslashes (i.e., not part of an existing `\\` pair) that are not followed by a
       valid JSON escape character are doubled (e.g., bare `\0` → `\\0`). LLMs generating
       CBMC specs may include C escape sequences such as `'\0'` verbatim inside JSON strings.
       These are invalid in JSON — only `\\"`, `\\\\`, `\\/`, `\\b`, `\\f`, `\\n`, `\\r`,
       `\\t`, and `\\uXXXX` are recognised — so they must be normalised to their literal
       two-character form before parsing. Already-valid sequences such as `\\\\0` (a correctly
       escaped backslash followed by `0`) are left untouched.

    Args:
        text (str): A string representation of a JSON object.

    Returns:
        dict[str, Any]: A Python dictionary parsed from a string representation of a JSON object.

    Raises:
        RuntimeError: Raised when a JSON object fails to be parsed from the given text.

    """
    text = text.strip()
    if text.startswith("```json") or text.endswith("```"):
        text = text.strip().removeprefix("```json").removesuffix("```")
    text = re.sub(r'(?<!\\)\\(?!["\\/bfnrtu])', r"\\\\", text)
    try:
        return json.loads(text)
    except JSONDecodeError as je:
        msg = f"Failed to parse a JSON object from: '{text}', error = {je}"
        raise RuntimeError(msg) from je
