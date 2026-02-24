"""Utilities for manipulating text."""

import re
from pathlib import PurePosixPath

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
    return [line.replace(CBMC_COMMENT_PREFIX, "") for line in lines]


def normalize_cbmc_output_paths(
    output: str,
    function_name: str,
    *,
    temp_file_path: str | None = None,
) -> str:
    """Return CBMC output with temp file paths replaced by a stable name.

    CBMC error output includes the path to the temporary file that was compiled
    (e.g., '/app/specs/get_min_maxABC123.c'). These random paths make LLM cache
    keys non-deterministic. This function replaces any such path with a stable
    name (e.g., 'get_min_max.c') so that prompts are reproducible across runs.

    When *temp_file_path* is provided the function first performs exact literal
    replacements for the full path and its basename, which is faster and more
    precise.  A regex pass is always applied afterwards to catch any remaining
    occurrences (e.g., paths that differ slightly from the one supplied).

    Args:
        output: The raw CBMC stdout or stderr output.
        function_name: The name of the function being verified.
        temp_file_path: Optional exact path to the temp file that was compiled.
            When given, its full path and basename are replaced first via exact
            string substitution before the regex fallback.

    Returns:
        The CBMC output with temp file paths replaced by '{function_name}.c'.
    """
    stable_name = f"{function_name}.c"

    # Precise literal replacement when the exact path is known.
    if temp_file_path is not None:
        basename = PurePosixPath(temp_file_path).name
        output = output.replace(temp_file_path, stable_name)
        output = output.replace(basename, stable_name)

    # Regex fallback: catches any remaining temp-file references.
    return re.sub(
        r"\S*" + re.escape(function_name) + r"[a-zA-Z0-9_-]+\.c",
        stable_name,
        output,
    )
