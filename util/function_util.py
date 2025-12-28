"""Utility methods for working with CBMC specifications."""

import tempfile
from pathlib import Path

import tree_sitter_c as tsc
from tree_sitter import Language, Parser, Query, QueryCursor

from .c_function import CFunction
from .function_specification import FunctionSpecification
from .parsec_file import ParsecFile

PRECONDITION_PREFIX = "__CPROVER_requires"
POSTCONDITION_PREFIX = "__CPROVER_ensures"

TREE_SITTER_LANG = Language(tsc.language())
PARSER = Parser(TREE_SITTER_LANG)


def extract_specification(function_lines: list[str]) -> FunctionSpecification | None:
    """Extract a FunctionSpecification from the lines of a function.

    Args:
        function_lines (list[str]): The lines of a function, which may include a CBMC specification.

    Returns:
        FunctionSpecification | None: The specification parsed from the lines of a C function.
    """
    stripped_lines = [line.strip() for line in function_lines]
    preconditions = []
    postconditions = []
    for i, line in enumerate(stripped_lines):
        if line.startswith(PRECONDITION_PREFIX):
            preconditions.append(_get_spec_lines(i, stripped_lines))
        elif line.startswith(POSTCONDITION_PREFIX):
            postconditions.append(_get_spec_lines(i, stripped_lines))
    if preconditions or postconditions:
        return FunctionSpecification(
            preconditions=preconditions,
            postconditions=postconditions,
        )
    return None


def get_signature_and_body(source_code: str, lang: str) -> tuple[str, str]:
    """Return the signature and body of a function.

    The first part of the tuple is the signature of the function and any comments that may appear
    before the body. For example, given the function declaration:

        int main() // This
        // is a comment.
        {
            return 1;
        }

    The first element of the tuple comprises:

        int main() // This
        // is a comment.

    The second element of the tuple is everything excluding the signature. For the example above,
    the element comprises:

        {
            return 1;
        }

    The curly braces are included.

    Args:
        source_code (str): The source code of the function.
        lang (str): The programming language in which the function is written.

    Returns:
        tuple[str, str]: The signature and the body of a function.
    """
    if lang != "c":
        msg = f"Unsupported language: {lang}"
        raise RuntimeError(msg)
    tree = PARSER.parse(bytes(source_code, encoding="utf-8"))
    # The query syntax is defined at
    # https://tree-sitter.github.io/tree-sitter/using-parsers/queries/1-syntax.html .
    query = Query(
        TREE_SITTER_LANG,
        """
        (function_definition
          body: (compound_statement) @this_function_body) @this_function_definition
        """,
    )
    query_cursor = QueryCursor(query)
    captures = query_cursor.captures(tree.root_node)

    try:
        definition_node = captures["this_function_definition"][0]
        body_node = captures["this_function_body"][0]
    except (KeyError, IndexError) as e:
        msg = f"Failed to parse a function definition from source code: {e}"
        raise RuntimeError(msg) from e

    signature = source_code[definition_node.start_byte : body_node.start_byte].strip()
    body = source_code[body_node.start_byte : body_node.end_byte].strip()
    return (signature, body)


def get_source_code_with_inserted_spec(
    function_name: str,
    specification: FunctionSpecification,
    parsec_file: ParsecFile,
    *,
    comment_out_spec: bool = False,
) -> str:
    """Return the source code of a function with the specification inserted.

    Note: This does *not* update the ParsecFile with the specified function declaration.

    Args:
        function_name (str): The name of the function for which to return the updated source code.
        specification (FunctionSpecification): The specification for the function.
        parsec_file (ParsecFile): The ParsecFile.
        comment_out_spec (bool): Whether to comment out CBMC specs.

    Returns:
        str: The source code of a function with the specification inserted.
    """
    function = parsec_file.get_function(function_name=function_name)
    (signature, body) = get_signature_and_body(function.get_source_code(), lang="c")
    specs = "\n".join(
        f"// {spec}" if comment_out_spec else spec
        for spec in specification.preconditions + specification.postconditions
    )
    return f"{signature}\n{specs}\n{body}"


def get_source_file_content_with_specifications(
    specified_functions: dict[CFunction, FunctionSpecification],
    parsec_file: ParsecFile,
    original_source_file_path: Path,
) -> str:
    """Return the content of the given source code file after specification insertion.

    Args:
        specified_functions (dict[CFunction, FunctionSpecification]): The map of functions to specs.
        parsec_file (ParsecFile): The ParsecFile parse from the original source code file.
        original_source_file_path (Path): The path to the original source code file.

    Returns:
        str: The content of the given source code file after specification insertion.
    """
    original_file_content = original_source_file_path.read_text(encoding="utf-8")
    with tempfile.NamedTemporaryFile(mode="w+t") as tmp_f:
        tf_path = Path(tmp_f.name)
        # Start out with a temporary file that is identical to the initial file (pre-specs).
        tmp_f.write(original_file_content)
        tmp_f.flush()
        for function, specification in specified_functions.items():
            # Get the source code of the function from the original file, and insert the specs.
            function_with_specs = get_source_code_with_inserted_spec(
                function_name=function.name, specification=specification, parsec_file=parsec_file
            )
            content_with_specs = _replace_function_declaration(
                function=function,
                updated_function_declaration=function_with_specs,
                path_to_src=tf_path,
            )
            # The temporary file's new content will be the previous content, with updated specs.
            tmp_f.seek(0)
            tmp_f.truncate()
            tmp_f.write(content_with_specs)
            tmp_f.flush()
        tmp_f.seek(0)
        return tmp_f.read()


def update_parsec_file(
    function_name: str, updated_function_content: str, parsec_file: ParsecFile
) -> None:
    """Update the entry for a function in the ParsecFile with its updated version.

    Args:
        function_name (str): The function to update in the ParsecFile.
        updated_function_content (str): The updated function content.
        parsec_file (ParsecFile): The parsec file to update.
    """
    original_function = parsec_file.get_function(function_name)
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
    spec = extract_specification(updated_function_content.splitlines())
    if spec:
        original_function.set_specifications(specifications=spec)

    # Update line/col info for other functions.
    line_offset = function_len - (prev_end_line - prev_start_line + 1)
    for other_func in parsec_file.functions.values():
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
    function_name: str, updated_function_content: str, parsec_file: ParsecFile, file: Path
) -> str:
    """Return the contents of the file after updating the function declaration.

    Args:
        function_name (str): The name of the function to update.
        updated_function_content (str): The new contents of the function.
        parsec_file (ParsecFile): The ParseC file containing function definitions.
        file (Path): The file that contains the function (and possibly other functions).

    Returns:
        str: The contents of the file after updating the function declaration.
    """
    function = parsec_file.get_function(function_name)

    # Update the actual source code.
    new_contents = _replace_function_declaration(function, updated_function_content, file)
    Path(file).write_text(new_contents, encoding="utf-8")

    start_line = function.start_line
    start_col = function.start_col
    end_line = function.end_line
    end_col = function.end_col

    # Update the line/col info for this function in the Parsec file.
    function_lines = updated_function_content.splitlines()
    num_lines = len(function_lines)
    new_end_line = start_line + num_lines - 1
    new_end_col = (
        len(function_lines[-1]) if num_lines > 1 else start_col + len(updated_function_content)
    )
    function.end_line = new_end_line
    function.end_col = new_end_col
    spec = extract_specification(function_lines)
    if spec:
        function.set_specifications(spec)

    # Update line/col info for other functions.
    line_offset = num_lines - (end_line - start_line + 1)
    for other_func in parsec_file.functions.values():
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
    """Extract one specification from the lines of a function.

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


def _replace_function_declaration(
    function: CFunction, updated_function_declaration: str, path_to_src: Path
) -> str:
    """Return contents of the file where the function is defined with its new declaration.

    Args:
        function (CFunction): The function with a new declaration.
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
