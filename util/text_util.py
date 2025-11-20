"""Utilities for manipulating text."""


def prepend_line_numbers(lines: list[str], start: int, end: int) -> list[tuple[str, str]]:
    """Return a list of tuples of line numbers with lines.

    Args:
        lines (list[str]): The lines to prepend line numbers to.
        start (int): The start of the line number range.
        end (int): The end of the line number range (inclusive).

    Raises:
        RuntimeError: Raised when the number of lines is not equal to the range.

    Returns:
        list[tuple[str, str]]: A list of tuples of line numbers with lines.
    """
    if len(lines) != abs(end - start):
        msg = (
            f"Mismatch between length of lines ({len(lines)}) and "
            f"range of lines (start = {start}, end = {end})"
        )
        raise RuntimeError(msg)
    line_number_padding = len(str(end))
    return [(f"{str(n).ljust(line_number_padding)}", lines[n - start]) for n in range(start, end)]
