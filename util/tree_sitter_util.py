"""Utilities for working with tree-sitter ASTs."""

from collections.abc import Set as AbstractSet
from enum import StrEnum

from tree_sitter import Node


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
        tree_root: The root node of the tree to search.

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
        tree_root: The root node of the tree to search.

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


def collect_nodes_by_type(node: Node, node_type: str) -> list[Node]:
    """Recursively collect all descendant nodes (including `node` itself) of a given type.

    Args:
        node (Node): The root of the sub-tree to search.
        node_type (str): The tree-sitter node type string to match (e.g.
            ``"binary_expression"`` or ``"number_literal"``).

    Returns:
        list[Node]: All matching nodes in pre-order.
    """
    result: list[Node] = []
    if node.type == node_type:
        result.append(node)
    for child in node.children:
        result.extend(collect_nodes_by_type(child, node_type))
    return result


def get_operator_node(
    binary_expr: Node, source_bytes: bytes, valid_operators: AbstractSet[str]
) -> Node | None:
    """Return the anonymous operator child of a ``binary_expression`` node.

    In the tree-sitter C grammar, the operator within a ``binary_expression``
    is an *anonymous* (unnamed) child node whose text is the operator symbol.

    Args:
        binary_expr (Node): A ``binary_expression`` node.
        source_bytes (bytes): The source bytes used to decode node text.
        valid_operators (AbstractSet[str]): The set of operator symbols to match against.

    Returns:
        Node | None: The operator node, or ``None`` if none is found.
    """
    for child in binary_expr.children:
        if not child.is_named:
            text = node_text(source_bytes, child)
            if text in valid_operators:
                return child
    return None


def node_text(source_bytes: bytes, node: Node) -> str:
    """Return the original source text covered by `node`.

    Args:
        source_bytes (bytes): The source bytes to slice.
        node (Node): The tree-sitter node whose text to retrieve.

    Returns:
        str: The source text for the node.
    """
    return source_bytes[node.start_byte : node.end_byte].decode("utf-8")


def replace_node(source_bytes: bytes, node: Node, replacement: str) -> str:
    """Return a new source string with `node`'s text replaced by `replacement`.

    Args:
        source_bytes (bytes): The source bytes to modify.
        node (Node): The tree-sitter node to replace.
        replacement (str): The replacement text.

    Returns:
        str: The full source string with the substitution applied.
    """
    return (
        source_bytes[: node.start_byte]
        + replacement.encode("utf-8")
        + source_bytes[node.end_byte :]
    ).decode("utf-8")


def _is_function_declarator(declarator: Node | None) -> bool:
    """Return true if a declarator is or contains a function_declarator.

    A declarator can be a function_declarator node itself, e.g.,

        int main() { }

    But other declarators (such as those for function prototypes) have function_declarator nodes
    as children, e.g.,

        int prototype();

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


def _find_identifier_in_declarator_or_definition(
    declarator_or_definition: Node | None,
) -> Node | None:
    """Recursively find the unique identifier node within a declarator or definition node.

    An identifier node contains the name of a function.

    Handles nested declarators (e.g., pointer_declarator -> function_declarator -> identifier).

    Args:
        declarator_or_definition: The declarator or definition node to search.

    Returns:
        The identifier node if found, None otherwise.
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
