"""Utilities for manipulating text."""

import json
from json import JSONDecodeError


def prepend_line_numbers(lines: list[str], start: int, end: int) -> list[tuple[str, str]]:
    """Return a list of tuples of line numbers with lines.

    Args:
        lines (list[str]): The lines to prepend line numbers to.
        start (int): The start of the line number range (inclusive).
        end (int): The end of the line number range (exclusive).

    Raises:
        RuntimeError: Raised when the number of lines is not equal to the number of
            elements in the range, or when the end of the line number range is less
            than the start.

    Returns:
        list[tuple[str, str]]: A list of tuples of line numbers with lines.
    """
    if end < start:
        msg = f"Invalid line number range (start = {start}, end = {end})"
        raise RuntimeError(msg)
    if len(lines) != end - start:
        msg = (
            f"Mismatch between length of lines ({len(lines)}) and "
            f"range of lines (start = {start}, end = {end})"
        )
    line_number_padding = len(str(end))
    return [(f"{str(n).ljust(line_number_padding)}", lines[n - start]) for n in range(start, end)]


def get_lines_with_suffix(text: str, suffix: str) -> list[str]:
    """Return the lines in text that end with the given suffix, ignoring whitespace.

    Args:
        text (str): The text to get lines that end with the given suffix.
        suffix (str): The suffix.

    Returns:
        int: The lines in text that end with the given suffix, ignoring whitespace.
    """
    lines = [line.strip() for line in text.splitlines()]
    return [line for line in lines if line.endswith(suffix)]


def get_value_of_field_with_key(json_text: str, key: str) -> str:
    """Return the value of the field in the text mapping to the key.

    Args:
        json_text (str): The JSON text.
        key (str): The key for which to obtain the value.

    Raises:
        RuntimeError: Raised when the JSON text is malformed or does not contain the
            given key.

    Returns:
        str: The value of the field in the text mapping to the key.
    """
    json_text = json_text.strip()
    if json_text.startswith("```json") or json_text.endswith("```"):
        # The LLM likely did not follow instructions to return just the plain object.
        json_text = json_text.strip().removeprefix("```json").removesuffix("```")
    try:
        return str(json.loads(json_text)[key])
    except JSONDecodeError as je:
        msg = f"The LLM failed to return a valid JSON object: {json_text}, error = {je}"
        raise RuntimeError(msg) from je
    except KeyError as ke:
        msg = f"The LLM returned valid JSON, but was missing the '{key}' key: {json_text}"
        raise RuntimeError(msg) from ke
