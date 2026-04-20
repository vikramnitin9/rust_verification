"""Utilities for working with tree-sitter ASTs."""

from __future__ import annotations

from enum import StrEnum
from pathlib import Path
from typing import TYPE_CHECKING

import tree_sitter_c as tsc
from loguru import logger
from tree_sitter import Language, Node, Parser, Tree

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


def parse_content(content: str, language_extension: str = ".c") -> Tree:
    """Return a tree_sitter AST parsed from the given source code string.

    This only supports parsing C ASTs, for now.

    Arguments:
        content (str): The source code to parse.
        language_extension (str): The language extension of the language to parse an AST for.
            Defaults to C (.c).

    Returns:
        Tree: A tree_sitter AST.
    """
    match language_extension:
        case ".c":
            return _PARSER.parse(bytes(content, encoding="utf-8"))
        case _:
            msg = f"Unsupported language for tree_sitter utils: {language_extension}"
            raise ValueError(msg)


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
        elif node.type == "ERROR":
            # Within ERROR nodes tree-sitter may fail to recognise function calls as
            # call_expression nodes (e.g. inside non-standard CBMC annotation syntax such
            # as __CPROVER_ensures).  Explicitly look for identifier nodes that are
            # immediately followed by `(` as a sibling — the hallmark of a function call
            # that error-recovery decomposed into separate tokens.
            for i, child in enumerate(node.children):
                if (
                    child.type == "identifier"
                    and i + 1 < len(node.children)
                    and node.children[i + 1].type == "("
                ):
                    assert child.text, "Expected an identifier node to have text"
                    result.append((child, IdentifierNodeParentType.CALL_EXPRESSION))
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


def get_functions_from_file(path: Path) -> list[CFunction]:
    """Parse a C source file and return a list of CFunctions defined in it.

    Uses tree-sitter to extract function definitions, their source locations, signatures,
    and direct callee names. Only `function_definition` nodes are included; forward
    declarations (without a body) are skipped.

    Args:
        path (Path): Path to the C source file to parse.

    Returns:
        list[CFunction]: One CFunction per function definition found in the file.
    """
    source = path.read_bytes()
    functions: list[CFunction] = []

    def collect(node: Node) -> None:
        """Collect all function nodes found under the given node, including itself.

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

    tree = _PARSER.parse(source)
    if not tree:
        msg = f"Tree sitter failed to parse a tree from '{path}'"
        raise ValueError(msg)
    if tree.root_node.has_error:
        # tree-sitter has fault-tolerant parsing; the presence of an error node doesn't mean we
        # should immediately give up. Files with CBMC specifications inserted into them
        # (which aren't legal C) will still be parsed.
        msg = (
            f"File '{path}' parsed into a tree with errors; "
            "this may be due to the presence of CBMC specifications"
        )
        logger.warning(msg)
    collect(tree.root_node)

    return functions


def _extract_c_function(node: Node, source: bytes, file_name: str) -> CFunction | None:
    """Build a CFunction from a tree-sitter `function_definition` node.

    Args:
        node (Node): A `function_definition` node.
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

    # tree-sitter uses 0-indexed rows and columns.
    # CFunction uses 1-indexed lines (start_line, end_line) and 1-indexed start_col.
    # end_col is the 0-indexed exclusive byte offset within the last line, matching the
    # convention used by get_source_code and _replace_function_definitions.
    start_line = node.start_point.row + 1
    start_col = node.start_point.column + 1
    end_line = node.end_point.row + 1
    end_col = node.end_point.column

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

    Only direct calls (`identifier` as the function node of a `call_expression`) are
    collected. Indirect calls via function pointers are not included.

    Args:
        body (Node): The `compound_statement` body node of a function definition.

    Returns:
        list[str]: Deduplicated list of callee names in order of first appearance.
    """
    callee_names: set[str] = set()

    def traverse(node: Node) -> None:
        """Traverse the given node and collect names of function call expressions.

        Closes over `callee_names`.

        Args:
            node (Node): The node under which to collect names of function call expressions.
        """
        if node.type == "call_expression":
            if (
                (func_node := node.child_by_field_name("function"))
                and func_node.type == "identifier"
                and func_node.text
            ):
                name = func_node.text.decode("utf-8")
                callee_names.add(name)
        for child in node.children:
            traverse(child)

    traverse(body)
    return list(callee_names)
