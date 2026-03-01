#!/opt/miniconda3/bin/python

"""Module to generate the CBMC ANSI-C stub files, modified for use with Avocado."""

import argparse
import pickle as pkl
import re
from pathlib import Path

import tree_sitter_c as tsc
from loguru import logger
from tree_sitter import Language, Node, Parser, Tree

from util.tree_sitter_util import (
    collect_call_identifiers,
    collect_function_identifiers,
)
from verification.avocado_stub_util import RenameMetadata

C_LANGUAGE = Language(tsc.language())
C_PARSER = Parser(C_LANGUAGE)
AVOCADO_FUNCTION_PREFIX = "avocado_"
CPROVER_PREFIX = "__CPROVER"
DO_NOT_RENAME_PATTERN = rf"^({re.escape(AVOCADO_FUNCTION_PREFIX)}|{re.escape(CPROVER_PREFIX)})"


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

    all_renamed_functions: dict[str, RenameMetadata] = {}

    # First pass: rename all relevant function declarations and definitions.
    for c_src in c_src_files:
        original_function_rename_metadata = _rename_function_declarations_and_definitions(c_src)
        all_renamed_functions.update(original_function_rename_metadata)

    # Second pass: rename all function calls in all files
    for c_src in c_src_files:
        _rename_function_calls(c_src, all_renamed_functions)

    rename_map_dir = "verification/cbmc_stubs"
    rename_map_pkl = "c_stub_rename_map.pkl"
    try:
        with Path(f"{rename_map_dir}/{rename_map_pkl}").open("wb") as f:
            pkl.dump(all_renamed_functions, f)
        logger.debug(
            f"Map from original functions to Avocado stubs saved to "
            f"'{rename_map_dir}/{rename_map_pkl}'"
        )
    except pkl.PicklingError as e:
        msg = f"Failed to save a map from original functions to Avocado stubs with error: {e}"
        raise RuntimeError(msg) from e


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
    function_identifiers = _collect_function_identifiers_for_renaming(parsed_src)
    src_after_renaming, original_names_to_avocado_names = _rename_functions_in_src(
        src_content, function_identifiers
    )
    original_c_src.write_text(src_after_renaming.decode(), encoding="utf-8")
    return {
        original_name: RenameMetadata(avocado_name, original_c_src)
        for original_name, avocado_name in original_names_to_avocado_names.items()
    }


def _rename_function_calls(
    file_path: Path, original_name_to_rename_metadata: dict[str, RenameMetadata]
) -> None:
    """Rename function calls in the given source file to use Avocado-prefixed names.

    Args:
        file_path: The C source file to process.
        original_name_to_rename_metadata: Map from original function names to their rename metadata.
    """
    src_content = file_path.read_bytes()
    parsed_src = C_PARSER.parse(src_content)

    def _is_identifier_renamed(node: Node) -> bool:
        return node.text is not None and node.text.decode() in original_name_to_rename_metadata

    call_identifiers = collect_call_identifiers(parsed_src.root_node)
    call_identifiers_to_rename = [
        call_id for call_id in call_identifiers if _is_identifier_renamed(call_id)
    ]

    if not call_identifiers_to_rename:
        return

    # Apply renaming in descending byte order.
    renamed_src = bytearray(src_content)
    for call_node in sorted(
        call_identifiers_to_rename, key=lambda node: node.start_byte, reverse=True
    ):
        start = call_node.start_byte
        end = call_node.end_byte
        original_name = call_node.text.decode()
        avocado_name = original_name_to_rename_metadata[original_name].avocado_name

        logger.debug(f"Renaming call to {original_name} -> {avocado_name} in {file_path}")
        renamed_src[start:end] = avocado_name.encode()

    file_path.write_bytes(bytes(renamed_src))


def _collect_function_identifiers_for_renaming(tree: Tree) -> list[Node]:
    """Return the identifier nodes parsed from function definitions and declarations for renaming.

    Args:
        tree (Tree): The tree from which to start collecting identifiers.

    Returns:
        list[Node]: The identifier nodes parsed from function definitions and declarations for
            renaming.
    """
    return [
        function_id
        for function_id in collect_function_identifiers(tree.root_node)
        if _should_prepend_avocado_prefix(function_id)
    ]


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
        and node.text != "if"  # No idea why this is getting parsed.
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
    original_names_to_avocado_names = {}
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
        original_names_to_avocado_names[original_function_id] = renamed_function_id
        renamed_src[start:end] = renamed_function_id.encode()
    return (bytes(renamed_src), original_names_to_avocado_names)


if __name__ == "__main__":
    main()
