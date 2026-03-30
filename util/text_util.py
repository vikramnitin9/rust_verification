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

    Returns:
        list[tuple[str, str]]: A list of tuples of line numbers with lines.

    Raises:
        RuntimeError: Raised when the number of lines is not equal to the number of
            elements in the range, or when the end of the line number range is less
            than the start.

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
    """Return CBMC output with non-deterministic content replaced by stable values.

    CBMC output includes several pieces of non-deterministic content that make
    LLM cache keys vary across machines and architectures:

    1. Temp file paths (e.g., '/app/specs/get_min_maxABC123.c') — replaced with
       a stable name (e.g., 'get_min_max.c').
    2. Architecture strings in CBMC's version banner and library lines
       (e.g., 'CBMC version 6.7.1 (cbmc-6.7.1) 64-bit arm64 linux' or
       'Adding CPROVER library (arm64)') — the architecture token is replaced
       with the stable placeholder '<arch>' so that cache keys are identical on
       ARM64 and x86-64 hosts.

    When *temp_file_path* is provided the function first performs exact literal
    replacements for the full path and its basename, which is faster and more
    precise.  Regex passes are always applied afterwards.

    Args:
        output: The raw CBMC stdout or stderr output.
        function_name: The name of the function being verified.
        temp_file_path: Optional exact path to the temp file that was compiled.
            When given, its full path and basename are replaced first via exact
            string substitution before the regex fallback.

    Returns:
        The CBMC output with non-deterministic content replaced by stable values.
    """
    stable_name = f"{function_name}.c"

    # Precise literal replacement when the exact path is known.
    if temp_file_path is not None:
        basename = PurePosixPath(temp_file_path).name
        output = output.replace(temp_file_path, stable_name)
        output = output.replace(basename, stable_name)

    # Regex fallback: catches any remaining temp-file references.
    output = re.sub(
        r"\S*" + re.escape(function_name) + r"[a-zA-Z0-9_-]+\.c",
        stable_name,
        output,
    )

    # Normalize architecture-specific strings in CBMC's version banner,
    # e.g. 'CBMC version 6.7.1 (cbmc-6.7.1) 64-bit arm64 linux'
    #   -> 'CBMC version 6.7.1 (cbmc-6.7.1) 64-bit <arch> linux'
    output = re.sub(
        r"(CBMC version \S+ \(\S+\) \d+-bit )\w+( linux)",
        r"\1<arch>\2",
        output,
    )

    # Normalize architecture in CPROVER library lines,
    # e.g. 'Adding CPROVER library (arm64)' -> 'Adding CPROVER library (<arch>)'
    output = re.sub(
        r"(Adding CPROVER library \()\w+(\))",
        r"\1<arch>\2",
        output,
    )

    return output
