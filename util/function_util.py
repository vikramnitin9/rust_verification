"""Utility methods for working with CBMC specifications."""

import time
from pathlib import Path

import tree_sitter_c as tsc
from tree_sitter import Language, Parser, Query, QueryCursor

from .parsec_function import ParsecFunction
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


def get_signature_and_body(src: str, lang: str) -> tuple[str, str]:
    """Return the signature and body of a function.

    The first element of the tuple comprises the signature, the second element comprises the body.

    Args:
        src (str): The source code of the function.
        lang (str): The language of the source function.

    Returns:
        tuple[str, str]: The signature and the body of a function.
    """
    if lang != "c":
        msg = f"Unsupported language: {lang}"
        raise RuntimeError(msg)
    ts_lang = Language(tsc.language())
    parser = Parser(ts_lang)
    tree = parser.parse(bytes(src, encoding="utf-8"))
    query = Query(
        ts_lang,
        """
        (function_definition
          body: (compound_statement) @function.body) @function.definition
        """,
    )
    query_cursor = QueryCursor(query)
    captures = query_cursor.captures(tree.root_node)

    definition_node = captures["function.definition"][0]
    body_node = captures["function.body"][0]

    signature = src[definition_node.start_byte : body_node.start_byte].strip()
    body = body_node.text.decode(encoding="utf-8")
    return (signature, body)


def get_source_code_with_specs(
    function_name: str, specifications: FunctionSpecification, parsec_result: ParsecResult
) -> str:
    """Return the source code of a function with the specifications inserted.

    Note: This does *not* update the ParsecResult with the specified function declaration.

    Args:
        function_name (str): The name of the function for which to return the updated source code.
        specifications (FunctionSpecification): The specifications for the function.
        parsec_result (ParsecResult): The ParsecResult.

    Raises:
        RuntimeError: Raised when the function is missing from the ParsecResult.

    Returns:
        str: The source code of a function with the specifications inserted.
    """
    if function := parsec_result.get_function(function_name=function_name):
        (signature, body) = get_signature_and_body(function.get_source_code(), lang="c")
        specs = "\n".join(
            spec for spec in specifications.preconditions + specifications.postconditions
        )
        return f"{signature}\n{specs}\n{body}"
    msg = f"{function_name} missing from ParsecResult"
    raise RuntimeError(msg)


def get_file_with_updated_function(
    function_name: str,
    updated_function_declaration: str,
    parsec_result: ParsecResult,
    original_src: Path,
) -> Path:
    """Return a path to a new file containing a function with an updated declaration.

    Args:
        function_name (str): The name of the function with an updated declaration.
        updated_function_declaration (str): The updated function declaration.
        parsec_result (ParsecResult): The ParsecResult.
        original_src (Path): The path to the original file with the original function
            declaration.

    Raises:
        RuntimeError: Raised when the original declaration for the function with the updated
            declaration is missing from the ParsecResult.

    Returns:
        Path: The path to the new file.
    """
    original_function = parsec_result.get_function(function_name)
    if not original_function:
        msg = f"Could not find definition for function '{function_name}' to update"
        raise RuntimeError(msg)
    file_content_with_candidate_specs = _insert_updated_function_declaration(
        original_function, updated_function_declaration, original_src
    )
    tmp_file = Path(_get_temporary_file_name(function_name, original_src))
    tmp_file.parent.mkdir(exist_ok=True, parents=True)
    tmp_file.write_text(file_content_with_candidate_specs, encoding="utf-8")
    return tmp_file


def update_parsec_result(
    function_name: str, updated_function_content: str, parsec_result: ParsecResult
) -> None:
    """Update the entry for a function in the ParsecResult with its updated version.

    Args:
        function_name (str): The function to update in the ParsecResult.
        updated_function_content (str): The updated function content.
        parsec_result (ParsecResult): The parsec result to update.

    Raises:
        RuntimeError: Raised when there is no function to update in the parsec result.
    """
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

    # Update the actual source code.
    new_contents = _insert_updated_function_declaration(function, updated_function_content, file)
    Path(file).write_text(new_contents, encoding="utf-8")

    start_line = function.start_line
    start_col = function.start_col
    end_line = function.end_line
    end_col = function.end_col

    # Update the line/col info for this function in the Parsec Result.
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


def _insert_updated_function_declaration(
    function: ParsecFunction, updated_function_declaration: str, path_to_src: Path
) -> str:
    """Return contents of the file where the function is defined with its new declaration.

    Args:
        function (ParsecFunction): The function with a new declaration.
        updated_function_declaration (str): The updated function declaration.
        path_to_src (Path): The path to the source code.

    Returns:
        str: The contents of the file where the function is defined with its new declaration.
    """
    start_line = function.start_line
    start_col = function.start_col
    end_line = function.end_line
    end_col = function.end_col

    # Use `with` and `readlines()` here to enable line-by-line file reading.
    with Path(path_to_src).open(encoding="utf-8") as f:
        lines = f.readlines()

    before = [*lines[: start_line - 1], *[lines[start_line - 1][: start_col - 1]]]
    after = [*lines[end_line - 1][end_col:], *lines[end_line:]]
    return "".join([*before, updated_function_declaration, *after])
