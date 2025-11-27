"""Utility methods for working with CBMC specifications."""

import time
from pathlib import Path

from .parsec_result import ParsecResult
from .specifications import FunctionSpecification

PRECONDITION_PREFIX = "__CPROVER_requires"
POSTCONDITION_PREFIX = "__CPROVER_ensures"


def extract_specification(function_lines: list[str]) -> FunctionSpecification:
    """Extract the lines of a function that map to a CBMC specification.

    Args:
        function_lines (list[str]): The lines of a function, which includes a CBMC specification.

    Returns:
        FunctionSpecification: The specification parsed from the lines of a C function.
    """
    stripped_lines = [line.strip() for line in function_lines]
    preconditions = []
    postconditions = []
    for i, line in enumerate(stripped_lines):
        if line.startswith(PRECONDITION_PREFIX):
            preconditions.append(_get_spec_lines(i, stripped_lines))
        elif line.startswith(POSTCONDITION_PREFIX):
            postconditions.append(_get_spec_lines(i, stripped_lines))
    return FunctionSpecification(
        preconditions=preconditions,
        postconditions=postconditions,
    )


def get_file_with_updated_function(
    function_name: str, updated_function_impl: str, parsec_result: ParsecResult, original_src: Path
) -> Path:
    original_function = parsec_result.get_function(function_name)
    if not original_function:
        msg = f"Could not find definition for function '{function_name}' to update"
        raise RuntimeError(msg)
    prev_start_line = original_function.start_line
    prev_start_col = original_function.start_col
    prev_end_line = original_function.end_line
    prev_end_col = original_function.end_col

    # Use `with` and `readlines()` here to enable line-by-line file reading.
    with Path(original_src).open(encoding="utf-8") as f:
        lines = f.readlines()

    before = [*lines[: prev_start_line - 1], *[lines[prev_start_line - 1][: prev_start_col - 1]]]
    after = [*lines[prev_end_line - 1][prev_end_col:], *lines[prev_end_line:]]
    file_content_with_candidate_specs = "".join([*before, updated_function_impl, *after])

    tmp_file = Path(_get_temporary_file_name(function_name, original_src))
    tmp_file.parent.mkdir(exist_ok=True, parents=True)
    tmp_file.write_text(file_content_with_candidate_specs, encoding="utf-8")
    return tmp_file


def update_parsec_analysis(
    function_name: str, updated_function_content: str, parsec_result: ParsecResult
) -> None:
    original_function = parsec_result.get_function(function_name)
    if not original_function:
        msg = f"Could not find definition for function '{function_name}' to update"
        raise RuntimeError(msg)
    prev_start_line = original_function.start_line
    prev_start_col = original_function.start_col
    prev_end_line = original_function.end_line
    prev_end_col = original_function.end_col

    # Update the line/col info for this function.
    function_len = len(updated_function_content.splitlines())
    new_end_line = prev_start_line + function_len - 1
    new_end_col = (
        len(updated_function_content.splitlines()[-1])
        if function_len > 1
        else prev_start_col + len(updated_function_content)
    )
    original_function.end_line = new_end_line
    original_function.end_col = new_end_col
    original_function.set_specifications(
        extract_specification(updated_function_content.splitlines())
    )

    # Update line/col info for other functions.
    line_offset = function_len - (prev_end_line - prev_start_line + 1)
    for other_func in parsec_result.functions.values():
        if other_func.name == original_function.name:
            # We've already updated the original function.
            continue
        if other_func.start_line > prev_end_line:
            other_func.start_line += line_offset
            other_func.end_line += line_offset
        elif other_func.start_line == prev_end_line and other_func.start_col >= prev_end_col:
            other_func.start_col += new_end_col - prev_end_col
            other_func.end_col += new_end_col - prev_end_col
        elif other_func.end_line > prev_end_line:
            other_func.end_line += line_offset
        elif other_func.end_line == prev_end_line and other_func.end_col >= prev_end_col:
            other_func.end_col += new_end_col - prev_end_col


def update_source_file(updated_file_content: str, file: Path) -> None:
    Path(file).write_text(updated_file_content, encoding="utf-8")


def update_function_declaration(
    function_name: str, updated_function_content: str, parsec_result: ParsecResult, file: Path
) -> str:
    """Return the contents of the file after updating the function declaration.

    Args:
        function_name (str): The name of the function to update.
        updated_function_content (str): The new contents of the function.
        parsec_result (ParsecResult): The ParseC result containing function definitions.
        file (Path): The path to the file containing the function.

    Raises:
        RuntimeError: Raised when the function to be updated cannot be found.

    Returns:
        str: The contents of the file after updating the function declaration.
    """
    function = parsec_result.get_function(function_name)
    if not function:
        msg = f"Could not find definition for function '{function_name}' to update"
        raise RuntimeError(msg)
    start_line = function.start_line
    start_col = function.start_col
    end_line = function.end_line
    end_col = function.end_col

    # Use `with` and `readlines()` here to enable line-by-line file reading.
    with Path(file).open(encoding="utf-8") as f:
        lines = f.readlines()

    before = [*lines[: start_line - 1], *[lines[start_line - 1][: start_col - 1]]]
    after = [*lines[end_line - 1][end_col:], *lines[end_line:]]
    new_contents = "".join([*before, updated_function_content, *after])

    # Update the line/col info for this function.
    function_len = len(updated_function_content.splitlines())
    new_end_line = start_line + function_len - 1
    new_end_col = (
        len(updated_function_content.splitlines()[-1])
        if function_len > 1
        else start_col + len(updated_function_content)
    )
    function.end_line = new_end_line
    function.end_col = new_end_col
    function.set_specifications(extract_specification(updated_function_content.splitlines()))

    # Update line/col info for other functions.
    line_offset = function_len - (end_line - start_line + 1)
    for other_func in parsec_result.functions.values():
        if other_func.name == function.name:
            continue
        if other_func.start_line > end_line:
            other_func.start_line += line_offset
            other_func.end_line += line_offset
        elif other_func.start_line == end_line and other_func.start_col >= end_col:
            other_func.start_col += new_end_col - end_col
            other_func.end_col += new_end_col - end_col
        elif other_func.end_line > end_line:
            other_func.end_line += line_offset
        elif other_func.end_line == end_line and other_func.end_col >= end_col:
            other_func.end_col += new_end_col - end_col

    Path(file).write_text(new_contents, encoding="utf-8")
    return new_contents


def _get_spec_lines(i: int, lines: list[str]) -> str:
    """Extract specifications from the lines of a function.

    Args:
        i (int): The starting line of the specification.
        lines (list[str]): The lines of the function source code.

    Returns:
        str: The extracted specification.
    """
    curr_spec = ""
    open_parens = 0
    close_parens = 0
    for line in lines[i:]:
        open_parens += line.count("(")
        close_parens += line.count(")")
        curr_spec += line.strip()
        if open_parens == close_parens and open_parens > 0:
            break
    return curr_spec


def _get_temporary_file_name(function_name: str, src: Path) -> str:
    now_ts = int(time.time())
    path_to_src_no_ext = src.with_suffix("")
    ext = src.suffix
    return f"{path_to_src_no_ext}-{function_name}-candidate-specs-{now_ts}{ext}"
