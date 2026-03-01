#!/opt/miniconda3/bin/python

"""Module to generate the CBMC ANSI-C stub files, modified for use with Avocado."""

import argparse
import re
from dataclasses import dataclass
from pathlib import Path

import tree_sitter_c as tsc
from loguru import logger
from tree_sitter import Language, Node, Parser, Tree

C_LANGUAGE = Language(tsc.language())
C_PARSER = Parser(C_LANGUAGE)
AVOCADO_FUNCTION_PREFIX = "avocado_"
CPROVER_PREFIX = "__CPROVER"
DO_NOT_RENAME_PATTERN = rf"^({re.escape(AVOCADO_FUNCTION_PREFIX)}|{re.escape(CPROVER_PREFIX)})"


@dataclass(frozen=True)
class RenameMetadata:
    """Capture metadata for renaming ANSI-C functions to Avocado stubs.

    Attributes:
        avocado_name (str): The ANSI-C function's name as an Avocado stub.
        original_file_path (Path): The path to the original file in which the function is defined.
    """

    avocado_name: str
    original_file_path: Path


def main() -> None:
    """Generate the modified ANSI-C stub files from CBMC's original set of stub files.

    The original ANSI-C stub files used in Avocado are found here:

            https://github.com/diffblue/cbmc/tree/develop/src/ansi-c/library

    For each function declaration and definition, we rename the function by prepending `avocado_`.
    This is a workaround for: https://github.com/diffblue/cbmc/issues/8844
    """
    parser = argparse.ArgumentParser(description="Generate ANSI-C stub files to use with Avocado.")
    parser.add_argument(
        "--c-sources",
        type=str,
        required=True,
        help="Path to the directory containing unmangled C CBMC models.",
    )
    args = parser.parse_args()
    c_src_dir = args.c_sources
    c_src_files = list(Path(c_src_dir).glob("*.c"))

    # First pass: rename all function declarations and definitions, collecting metadata
    all_renamed_functions = {}
    for c_src in c_src_files:
        original_function_rename_metadata = _rename_function_declarations_and_definitions(c_src)
        all_renamed_functions.update(original_function_rename_metadata)

    # Second pass: rename all function calls in all files
    for c_src in c_src_files:
        _rename_function_calls_in_file(c_src, all_renamed_functions)


def _rename_function_declarations_and_definitions(
    original_c_src: Path,
) -> dict[str, RenameMetadata]:
    """Rename each function in the original C program to its Avocado stub name.

    Args:
        original_c_src (Path): The path to the original C file.

    Returns:
        dict[str, RenameMetadata]: The rename metadata for each function in the original C file.
    """
    logger.debug(f"Processing {original_c_src}")
    src_content = original_c_src.read_bytes()
    parsed_src = C_PARSER.parse(src_content)
    function_identifiers = _collect_function_identifiers(parsed_src)
    src_after_renaming, original_names_to_avocado_names = _rename_functions_in_src(
        src_content, function_identifiers
    )
    original_c_src.write_text(src_after_renaming.decode(), encoding="utf-8")
    return {
        original_name: RenameMetadata(avocado_name, original_c_src)
        for original_name, avocado_name in original_names_to_avocado_names.items()
    }


def _rename_function_calls_in_file(
    file_path: Path, original_name_to_rename_metadata: dict[str, RenameMetadata]
) -> None:
    """Rename function calls in the given source file to use Avocado-prefixed names.

    Args:
        file_path: The C source file to process.
        original_name_to_rename_metadata: Map from original function names to their rename metadata.
    """
    src_content = file_path.read_bytes()
    parsed_src = C_PARSER.parse(src_content)

    # Collect all call_expression identifiers that need renaming
    call_identifiers_to_rename = []

    def traverse(node: Node) -> None:
        if node.type == "call_expression":
            function_node = node.child_by_field_name("function")
            if function_node and function_node.type == "identifier" and function_node.text:
                original_name = function_node.text.decode()
                if original_name in original_name_to_rename_metadata:
                    call_identifiers_to_rename.append(function_node)
        for child in node.children:
            traverse(child)

    traverse(parsed_src.root_node)

    if not call_identifiers_to_rename:
        return

    # Apply renaming in descending byte order
    renamed_src = bytearray(src_content)
    for call_node in sorted(call_identifiers_to_rename, key=lambda n: n.start_byte, reverse=True):
        start = call_node.start_byte
        end = call_node.end_byte
        original_name = call_node.text.decode()
        avocado_name = original_name_to_rename_metadata[original_name].avocado_name

        logger.debug(f"Renaming call to {original_name} -> {avocado_name} in {file_path}")
        renamed_src[start:end] = avocado_name.encode()

    file_path.write_bytes(bytes(renamed_src))


def _collect_function_identifiers(tree: Tree) -> list[Node]:
    """Return the identifier nodes parsed from function definitions and declarations.

    Args:
        tree (Tree): The tree from which to start collecting identifiers.

    Returns:
        list[Node]: The identifier nodes parsed from function definitions and declarations.
    """
    result = []

    def _find_identifier_in_declarator(declarator: Node | None) -> Node | None:
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

    def traverse(node):
        if node.type in {"function_definition", "function_declaration"}:
            declarator = node.child_by_field_name("declarator")
            identifier = _find_identifier_in_declarator(declarator)
            if identifier is not None and _should_prepend_avocado_prefix(identifier):
                result.append(identifier)
        for child in node.children:
            traverse(child)

    traverse(tree.root_node)
    return result


def _should_prepend_avocado_prefix(node: Node) -> bool:
    """Return True iff the given node should be renamed with the avocado_ prefix.

    A node should be renamed iff:
        - It is an identifier node
        - It does NOT begin with `__CPROVER` or `avocado_` (indicating it has been already renamed).

    Args:
        node (Node): The node to check for renaming.

    Returns:
        bool: True iff the node should be renamed with the avocado_ prefix.
    """
    return (
        node.type == "identifier"
        and node.text is not None
        and not re.match(DO_NOT_RENAME_PATTERN, node.text.decode())
    )


def _rename_functions_in_src(
    src_content: bytes, function_id_nodes: list[Node]
) -> tuple[bytes, dict[str, str]]:
    """Return the source content and map from previous names to Avocado names after renaming.

    Args:
        src_content (bytes): The source content.
        function_id_nodes (list[Node]): The function id nodes to rename.

    Returns:
        tuple[bytes, dict[str, str]]: The source content and map from previous names to Avocado
            names after renaming.
    """
    renamed_src = bytearray(src_content)
    prev_names_to_avocado_names = {}
    for ident_node in sorted(function_id_nodes, key=lambda node: node.start_byte, reverse=True):
        start = ident_node.start_byte
        end = ident_node.end_byte
        if not ident_node.text:
            msg = "Identity node '' was missing a '.text' attribute"
            logger.error(msg)
            raise ValueError(msg)
        original_function_id = ident_node.text.decode()
        expected_identifier = original_function_id.encode()
        original_slice = bytes(renamed_src[start:end])
        if original_slice != expected_identifier:
            msg = (
                "Refusing to rename non-identifier slice at "
                f"[{start}:{end}]: expected {expected_identifier!r}, got {original_slice!r}"
            )
            logger.error(msg)
            raise ValueError(msg)
        renamed_function_id = f"{AVOCADO_FUNCTION_PREFIX}{original_function_id}"
        logger.debug(f"Renaming {original_function_id} -> {renamed_function_id}")
        prev_names_to_avocado_names[original_function_id] = renamed_function_id
        renamed_src[start:end] = renamed_function_id.encode()
    return (bytes(renamed_src), prev_names_to_avocado_names)


if __name__ == "__main__":
    main()
