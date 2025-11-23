"""Utilities for manipulating text."""


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
