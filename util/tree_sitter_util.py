"""Utilities for working with tree-sitter ASTs."""

from tree_sitter import Node


def collect_function_identifiers(tree_root: Node) -> list[Node]:
    """Collect identifier nodes from definition and declaration nodes in the given tree.

    Args:
        tree_root: The root node of the tree to search.

    Returns:
        list[Node]: Identifier nodes from definition and declaration nodes in the given tree.
    """
    result = []

    def traverse(node: Node) -> None:
        if node.type in {"function_definition", "function_declaration"}:
            declarator = node.child_by_field_name("declarator")
            identifier = _find_identifier_in_declarator(declarator)
            if identifier is not None:
                result.append(identifier)
        elif node.type == "declaration":
            # Only include declarations that are function prototypes, not variable declarations
            declarator = node.child_by_field_name("declarator")
            if _is_function_declarator(declarator):
                identifier = _find_identifier_in_declarator(declarator)
                if identifier is not None:
                    result.append(identifier)
        for child in node.children:
            traverse(child)

    traverse(tree_root)
    return result


def collect_call_identifiers(tree_root: Node) -> list[Node]:
    """Collect identifier nodes from function call expressions.

    Args:
        tree_root: The root node of the tree to search.

    Returns:
        List of identifier nodes that are function names in call expressions.
    """
    result = []

    def traverse(node: Node) -> None:
        if node.type == "call_expression":
            function_node = node.child_by_field_name("function")
            if function_node and function_node.type == "identifier" and function_node.text:
                result.append(function_node)
        for child in node.children:
            traverse(child)

    traverse(tree_root)
    return result


def _is_function_declarator(declarator: Node | None) -> bool:
    """Check if a declarator is or contains a function_declarator.

    Args:
        declarator: The declarator node to check.

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


def _find_identifier_in_declarator(declarator: Node | None) -> Node | None:
    """Recursively find an identifier node within a declarator.

    Handles nested declarators (e.g., pointer_declarator -> function_declarator -> identifier).

    Args:
        declarator: The declarator node to search.

    Returns:
        The identifier node if found, None otherwise.
    """
    if declarator is None:
        return None
    if declarator.type == "identifier":
        return declarator

    nested_declarator = declarator.child_by_field_name("declarator")
    if nested_declarator is not None:
        return _find_identifier_in_declarator(nested_declarator)

    for child in declarator.children:
        identifier = _find_identifier_in_declarator(child)
        if identifier is not None:
            return identifier
    return None
