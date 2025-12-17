"""Utilities for manipulating text."""

CBMC_COMMENT_PREFIX = "// CBMC_ANNOTATION: "


def prepend_line_numbers(lines: list[str], start: int, end: int) -> list[tuple[str, str]]:
    """Return a list of tuples of line numbers with lines.

    Args:
        lines (list[str]): The lines that will get line numbers.
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
    line_number_width = len(str(end))
    return [(f"{str(n).ljust(line_number_width)}", lines[n - start]) for n in range(start, end)]


def comment_out_cbmc_annotations(lines: list[str]) -> list[str]:
    """Comment out CBMC __CPROVER specifications in the source code.

    This function finds lines containing __CPROVER annotations (like __CPROVER_requires,
    __CPROVER_ensures, etc.) and comments them out by prepending '//' to each line.
    Handles both single-line and multi-line specifications by tracking parentheses.

    Args:
        lines (list[str]): The lines of C source code to process.

    Returns:
        list[str]: The lines with __CPROVER specifications commented out.
    """
    result = []
    in_spec = False
    paren_count = 0

    for line in lines:
        stripped = line.lstrip()

        # Check if this line starts a CBMC spec
        if stripped.startswith("__CPROVER") and not in_spec:
            in_spec = True

        if in_spec:
            result.append(f"{CBMC_COMMENT_PREFIX}{line}")

            # Count parentheses to determine when spec ends
            for char in line:
                if char == "(":
                    paren_count += 1
                elif char == ")":
                    paren_count -= 1
                    if paren_count == 0:
                        in_spec = False
                        break
        else:
            result.append(line)

    return result


def uncomment_cbmc_annotations(lines: list[str]) -> list[str]:
    """Remove CBMC_COMMENT_PREFIX in each line.

    Args:
        lines (list[str]): The lines in which to remove the CBMC_COMMENT_PREFIX.

    Returns:
        list[str]: The lines with CBMC_COMMENT_PREFIX removed
    """
    return [line.removeprefix(CBMC_COMMENT_PREFIX) for line in lines]
