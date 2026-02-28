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


def _get_c_files(model_dir: str) -> list[Path]:
    c_files = []
    for entry in Path.iterdir(Path(model_dir)):
        path = Path(model_dir) / entry
        if path.name.endswith(".c"):
            c_files.append(path)
    return c_files


def _rename_functions(c_src: Path) -> None:
    logger.debug(f"Processing {c_src}")
    src_content = c_src.read_bytes()
    parsed_src = C_PARSER.parse(src_content)
    function_identifiers = _collect_function_declarator_identifiers(parsed_src)
    print(_apply_renaming(src_content, function_identifiers).decode())


def _collect_function_declarator_identifiers(tree: Tree) -> list[Node]:
    result = []

    def traverse(node):
        # Handle function definitions
        if node.type == "function_definition":
            for child in node.children:
                if child.type == "function_declarator":
                    result.extend(
                        [subchild for subchild in child.children if subchild.type == "identifier"]
                    )
        # Handle function declarations (prototypes)
        if node.type == "function_declaration":
            for child in node.children:
                if child.type == "function_declarator":
                    result.extend(
                        [subchild for subchild in child.children if subchild.type == "identifier"]
                    )
        for i in range(node.child_count):
            traverse(node.child(i))

    traverse(tree.root_node)
    return result


def _apply_renaming(src_content: bytes, function_id_nodes: list[Node]) -> bytes:
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
