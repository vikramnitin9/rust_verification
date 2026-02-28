#!/opt/miniconda3/bin/python

"""Module to generate the CBMC ANSI-C stub files, modified for use with Avocado."""

import argparse
from pathlib import Path

import tree_sitter_c as tsc
from loguru import logger
from tree_sitter import Language, Node, Parser, Tree

C_LANGUAGE = Language(tsc.language())
C_PARSER = Parser(C_LANGUAGE)
AVOCADO_FUNCTION_PREFIX = "avocado_"
CPROVER_PREFIX = "__CPROVER"


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
    files = _get_c_files(c_src_dir)
    for c_src in files:
        _rename_functions(c_src)


def _get_c_files(folder: str) -> list[Path]:
    """Return the path to the C files (i.e., files ending in '.c') at the given folder.

    Args:
        folder (str): The folder at which to look for C files.

    Returns:
        list[Path]: The path to the C files at the given folder.
    """
    c_files = []
    for entry in Path.iterdir(Path(folder)):
        path = Path(folder) / entry
        if path.name.endswith(".c"):
            c_files.append(path)
    return c_files


def _rename_functions(original_c_src: Path) -> None:
    """Rename the functions found in the C file at the given path.

    Args:
        original_c_src (Path): The path to the original C file.
    """
    logger.debug(f"Processing {original_c_src}")
    src_content = original_c_src.read_bytes()
    parsed_src = C_PARSER.parse(src_content)
    function_identifiers = _collect_function_identifiers(parsed_src)
    src_after_renaming = _rename_functions_in_src(src_content, function_identifiers).decode()
    original_c_src.write_text(src_after_renaming, encoding="utf-8")


def _collect_function_identifiers(tree: Tree) -> list[Node]:
    """Return the identifier nodes parsed from function definitions and declarations.

    Args:
        tree (Tree): The tree from which to start collecting identifiers.

    Returns:
        list[Node]: The identifier nodes parsed from function definitions and declarations.
    """
    result = []

    def traverse(node):
        if node.type == "function_definition":
            for child in node.children:
                if child.type == "function_declarator":
                    result.extend(
                        [subchild for subchild in child.children if _is_node_to_rename(node)]
                    )
        if node.type == "function_declaration":
            for child in node.children:
                if child.type == "function_declarator":
                    result.extend(
                        [subchild for subchild in child.children if _is_node_to_rename(node)]
                    )
        for child in node.children:
            traverse(child)

    traverse(tree.root_node)
    return result


def _is_node_to_rename(node: Node) -> bool:
    if node.type == "identifier":
        return node.text is not None and node.text.decode().startswith(CPROVER_PREFIX)
    return False


def _rename_functions_in_src(src_content: bytes, function_id_nodes: list[Node]) -> bytes:
    """Return the source content after applying renaming.

    Args:
        src_content (bytes): The source content.
        function_id_nodes (list[Node]): The function id nodes to rename.

    Returns:
        bytes: The source content after applying renaming.
    """
    # Build the renamed source by replacing identifiers safely
    last_end = 0
    renamed_src = bytearray()
    for ident_node in function_id_nodes:
        start = ident_node.start_byte
        end = ident_node.end_byte
        if not ident_node.text:
            msg = "Identity node '' was missing a '.text' attribute"
            logger.error(msg)
            raise ValueError(msg)
        original_function_id = ident_node.text.decode()
        renamed_function_id = f"{AVOCADO_FUNCTION_PREFIX}{original_function_id}"
        logger.debug(f"Renaming {original_function_id} -> {renamed_function_id}")
        # Append unchanged region
        renamed_src += src_content[last_end:start]
        # Append renamed identifier
        renamed_src += renamed_function_id.encode()
        last_end = end
    # Append the remainder of the source
    renamed_src += src_content[last_end:]
    return bytes(renamed_src)


if __name__ == "__main__":
    main()
