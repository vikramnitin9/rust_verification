"""Utilities for working with tree-sitter ASTs."""

from tree_sitter import Node


def get_function_identifiers(tree_root: Node) -> list[Node]:
    """Return all identifier nodes from definition and declaration nodes in the given tree.

    Args:
        tree_root: The root node of the tree to search.

    Returns:
        list[Node]: All identifier nodes from definition and declaration nodes in the given tree.
    """
    result = []

    def traverse(node: Node) -> None:
        """Collect the identifier nodes found underneath function definition or declaration nodes.

        This function closes over the `result` variable defined in the enclosing scope.

        Args:
            node (Node): The node from which to start collecting function definition or declaration
                nodes.
        """
        if node.type in {"function_definition", "function_declaration"}:
            declarator = node.child_by_field_name("declarator")
            identifier = _find_identifier_in_declarator_or_definition(declarator)
            if identifier is not None:
                result.append(identifier)
        elif node.type == "declaration":
            # Only include declarations that are function prototypes, not variable declarations.
            declarator = node.child_by_field_name("declarator")
            if _is_function_declarator(declarator):
                identifier = _find_identifier_in_declarator_or_definition(declarator)
                if identifier is not None:
                    result.append(identifier)
        for child in node.children:
            traverse(child)

    traverse(tree_root)
    return result


def get_call_identifiers(tree_root: Node) -> list[Node]:
    """Get identifier nodes from function call expressions.

    Args:
        tree_root: The root node of the tree to search.

    Returns:
        list[Node]: Identifier nodes that are function names in call expressions.
    """
    result = []

    def traverse(node: Node) -> None:
        """Collect the identifier nodes underneath call expression nodes.

        This function closes over the `result` variable defined in the enclosing scope.

        Args:
            node (Node): The node from which to start collecting identifier nodes.
        """
        if node.type == "call_expression":
            function_node = node.child_by_field_name("function")
            assert function_node, "Expected a function node under a call_expression node"
            if function_node.type == "identifier":
                assert function_node.text, "Expected an identifier node to have text"
                result.append(function_node)
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

    for child in declarator_or_definition.children:
        identifier = _find_identifier_in_declarator_or_definition(child)
        if identifier is not None:
            return identifier
    return None
