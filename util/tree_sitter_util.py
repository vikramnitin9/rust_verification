"""Utilities for working with tree-sitter ASTs."""

from __future__ import annotations

from enum import StrEnum
from typing import TYPE_CHECKING

import tree_sitter_c as tsc
from tree_sitter import Language, Node, Parser

from .c_function import CFunction

if TYPE_CHECKING:
    from pathlib import Path

_TREE_SITTER_LANG = Language(tsc.language())
_PARSER = Parser(_TREE_SITTER_LANG)


class IdentifierNodeParentType(StrEnum):
    """Represent the parent node type of an identifier node.

    A definition node comprises a function definition in C (i.e., the signature and implementation).
    A declaration node comprises only the signature.
    A call expression comprises a function call.
    """

    FUNCTION_DEFINITION = "function_definition"
    DECLARATION = "declaration"
    CALL_EXPRESSION = "call_expression"


def get_function_identifiers(tree_root: Node) -> list[tuple[Node, IdentifierNodeParentType]]:
    """Return all identifier nodes from definition and declaration nodes in the given tree.

    Args:
        tree_root (Node): The root node of the tree to search.

    Returns:
        list[tuple[Node, IdentifierNodeParentType]]: All identifier nodes and the type of their
            immediate parent node.
    """
    result = []

    def traverse(node: Node) -> None:
        """Collect the identifier nodes found underneath function definition or declaration nodes.

        This function closes over the `result` variable defined in the enclosing scope.

        Args:
            node (Node): The node from which to start collecting function definition or declaration
                nodes.
        """
        if node.type == "function_definition":
            declarator = node.child_by_field_name("declarator")
            identifier = _find_identifier_in_declarator_or_definition(declarator)
            if identifier is not None:
                result.append((identifier, IdentifierNodeParentType.FUNCTION_DEFINITION))
        elif node.type == "declaration":
            # Only include declarations that are function prototypes, not variable declarations.
            declarator = node.child_by_field_name("declarator")
            if _is_function_declarator(declarator):
                identifier = _find_identifier_in_declarator_or_definition(declarator)
                if identifier is not None:
                    result.append((identifier, IdentifierNodeParentType.DECLARATION))
        for child in node.children:
            traverse(child)

    traverse(tree_root)
    return result


def get_identifier_nodes_from_call_expressions(
    tree_root: Node,
) -> list[tuple[Node, IdentifierNodeParentType]]:
    """Get identifier nodes from function call expressions.

    Args:
        tree_root (Node): The root node of the tree to search.

    Returns:
        list[tuple[Node, IdentifierNodeParentType]]: All identifier nodes and the type of their
            immediate parent node.
    """
    result = []

    def traverse(node: Node) -> None:
        """Collect the into `result` the identifier nodes underneath call expression nodes.

        Args:
            node (Node): The node from which to start collecting identifier nodes.
        """
        if node.type == "call_expression":
            function_node = node.child_by_field_name("function")
            assert function_node, "Expected a function node under a call_expression node"
            if function_node.type == "identifier":
                assert function_node.text, "Expected an identifier node to have text"
                result.append((function_node, IdentifierNodeParentType.CALL_EXPRESSION))
        for child in node.children:
            traverse(child)

    traverse(tree_root)
    return result


def _is_function_declarator(declarator: Node | None) -> bool:
    """Return true if a declarator is or contains a function_declarator.

    A declarator can be a function_declarator node itself, e.g.,

        int main() { }

    But other declarators (such as those for function prototypes) have function_declarator nodes
    as children, e.g.,

        int prototype();

    Args:
        declarator (Node | None): The declarator node to check.

    Returns:
        True if the declarator is or contains a function_declarator, False otherwise.
    """
    if declarator is None:
        return False
    if declarator.type == "function_declarator":
        return True

    nested_declarator = declarator.child_by_field_name("declarator")
    if nested_declarator is not None:
        return _is_function_declarator(nested_declarator)

    return False


def _find_identifier_in_declarator_or_definition(
    declarator_or_definition: Node | None,
) -> Node | None:
    """Recursively find the unique identifier node within a declarator or definition node.

    An identifier node contains the name of a function.

    Handles nested declarators (e.g., pointer_declarator -> function_declarator -> identifier).

    Args:
        declarator_or_definition (Node | None): The declarator or definition node to search.

    Returns:
        Node | None: The identifier node if found, None otherwise.
    """
    if declarator_or_definition is None:
        return None
    if declarator_or_definition.type == "identifier":
        return declarator_or_definition

    nested_declarator = declarator_or_definition.child_by_field_name("declarator")
    if nested_declarator is not None:
        # If there is a nested declarator, follow that path first to check
        # whether there are identifiers to get. A "nested declarator" is
        # something like `int (*f)(int x)`, which in tree-sitter is a
        # function_declarator around a pointer_declarator.
        return _find_identifier_in_declarator_or_definition(nested_declarator)

    # This handles cases where a function identifier might not be contained in an immediate
    # identifier node (e.g., `int (*fp)(int)`).
    for child in declarator_or_definition.children:
        identifier = _find_identifier_in_declarator_or_definition(child)
        if identifier is not None:
            return identifier
    return None


def parse_c_file(path: Path) -> list[CFunction]:
    """Parse a C source file and return a list of CFunctions defined in it.

    Uses tree-sitter to extract function definitions, their source locations, signatures,
    and direct callee names. Only ``function_definition`` nodes are included; forward
    declarations (without a body) are skipped.

    Args:
        path (Path): Path to the C source file to parse.

    Returns:
        list[CFunction]: One CFunction per function definition found in the file.
    """
    source = path.read_bytes()
    tree = _PARSER.parse(source)
    functions: list[CFunction] = []

    def collect(node: Node) -> None:
        """Collect all function definition nodes found under the given node, including itself.

        Args:
            node (Node): The node under which to collect function definition nodes.
        """
        if node.type == "function_definition":
            fn = _extract_c_function(node, source, str(path.resolve()))
            if fn is not None:
                functions.append(fn)
            # C does not allow nested function definitions, so no need to recurse into the body.
            return
        for child in node.children:
            collect(child)

    collect(tree.root_node)
    return functions


def _byte_col_to_char_col(source: bytes, row: int, byte_col: int) -> int:
    """Convert a tree-sitter byte-offset column to a Unicode character (codepoint) index.

    tree-sitter reports column positions as byte offsets into the line. Python string
    indexing operates on Unicode codepoints, so the two diverge whenever a line contains
    multi-byte UTF-8 characters (e.g. non-ASCII in comments or string literals).

    Args:
        source (bytes): The raw UTF-8 bytes of the source file.
        row (int): The 0-indexed row (line number) within the file.
        byte_col (int): The byte offset within that line as returned by tree-sitter.

    Returns:
        int: The corresponding Unicode character index.
    """
    line_bytes = source.split(b"\n")[row]
    return len(line_bytes[:byte_col].decode("utf-8"))


def _extract_c_function(node: Node, source: bytes, file_name: str) -> CFunction | None:
    """Build a CFunction from a tree-sitter ``function_definition`` node.

    Args:
        node (Node): A ``function_definition`` node.
        source (bytes): The raw bytes of the source file.
        file_name (str): Absolute path to the source file.

    Returns:
        CFunction | None: The extracted CFunction, or None if the node lacks a
            recognisable identifier or body.
    """
    declarator = node.child_by_field_name("declarator")
    identifier = _find_identifier_in_declarator_or_definition(declarator)
    if identifier is None or not identifier.text:
        return None

    body = node.child_by_field_name("body")
    if body is None:
        return None

    name = identifier.text.decode("utf-8")
    # The signature is everything from the start of the function_definition node up to (but not
    # including) the opening brace of the body, with surrounding whitespace stripped.
    signature = source[node.start_byte : body.start_byte].decode("utf-8").strip()

    # tree-sitter uses 0-indexed rows and columns (columns are byte offsets).
    # CFunction uses 1-indexed lines (start_line, end_line) and 1-indexed start_col.
    # end_col is the 0-indexed exclusive character index within the last line.
    # Downstream consumers (get_original_source_code, _replace_function_definitions) index
    # into decoded Python strings, so byte offsets must be converted to character indices.
    start_line = node.start_point.row + 1
    start_col = _byte_col_to_char_col(source, node.start_point.row, node.start_point.column) + 1
    end_line = node.end_point.row + 1
    end_col = _byte_col_to_char_col(source, node.end_point.row, node.end_point.column)

    callee_names = _collect_callee_names(body)

    return CFunction(
        name=name,
        signature=signature,
        file_name=file_name,
        start_line=start_line,
        start_col=start_col,
        end_line=end_line,
        end_col=end_col,
        callee_names=callee_names,
    )


def _collect_callee_names(body: Node) -> list[str]:
    """Return the names of all directly called functions within a function body.

    Only direct calls (``identifier`` as the function node of a ``call_expression``) are
    collected. Indirect calls via function pointers are not included.

    Args:
        body (Node): The ``compound_statement`` body node of a function definition.

    Returns:
        list[str]: Deduplicated list of callee names in order of first appearance.
    """
    seen: set[str] = set()
    callee_names: list[str] = []

    def traverse(node: Node) -> None:
        if node.type == "call_expression":
            func_node = node.child_by_field_name("function")
            if func_node is not None and func_node.type == "identifier" and func_node.text:
                name = func_node.text.decode("utf-8")
                if name not in seen:
                    seen.add(name)
                    callee_names.append(name)
        for child in node.children:
            traverse(child)

    traverse(body)
    return callee_names
