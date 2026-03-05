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
    get_call_identifiers,
    get_function_identifiers,
)
from verification.avocado_stub_util import RenameData

C_LANGUAGE = Language(tsc.language())
C_PARSER = Parser(C_LANGUAGE)
AVOCADO_FUNCTION_PREFIX = "_avocado_"
CPROVER_PREFIX = "__CPROVER"
VERIFIER_PREFIX = "__VERIFIER"
DO_NOT_RENAME_PATTERN = (
    rf"^({re.escape(AVOCADO_FUNCTION_PREFIX)}|"
    rf"{re.escape(VERIFIER_PREFIX)}|{re.escape(CPROVER_PREFIX)})"
)


def main() -> None:
    """Generate the modified stub files for libraries in the ANSI-C standard.

    CBMC's stubs of the functions declared in the ANSI-C standard are found here:

            https://github.com/diffblue/cbmc/tree/develop/src/ansi-c/library

    For each function declaration and definition, we rename the function by prepending `_avocado_`.
    This is a workaround for: https://github.com/diffblue/cbmc/issues/8844
    """
    parser = argparse.ArgumentParser(
        description=(
            "Generate stub files for functions defined in the ANSI-C standard to use with Avocado."
        )
    )
    parser.add_argument(
        "--c-sources",
        type=str,
        required=True,
        help="Path to the directory containing unmangled C CBMC models.",
    )
    args = parser.parse_args()
    c_src_dir = args.c_sources
    c_src_files = list(Path(c_src_dir).glob("*.c"))

    all_renamed_functions: dict[str, RenameData] = {}

    # First pass: rename all relevant function declarations and definitions.
    for c_src in c_src_files:
        function_rename_data = _rename_function_declarations_and_definitions(c_src)
        all_renamed_functions.update(function_rename_data)

    # Second pass: rename function calls for which an Avocado stub exists.
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
    path_to_src: Path,
) -> dict[str, RenameData]:
    """Rename each function in the original C program to its Avocado stub name.

    This updates each file in-place.

    Args:
        path_to_src (Path): The path to the original C file.

    Returns:
        dict[str, RenameData]: The rename data for each function in the original C file.
    """
    logger.debug(f"Processing {path_to_src}")
    src_content = path_to_src.read_bytes()
    parsed_src = C_PARSER.parse(src_content)
    function_identifiers = _get_function_identifiers_for_avocado_stub_renaming(parsed_src)
    src_after_renaming, original_names_to_avocado_names = _rename_functions_in_src(
        src_content, function_identifiers
    )
    path_to_src.write_text(src_after_renaming.decode(), encoding="utf-8")
    return {
        name: RenameData(avocado_name, path_to_src)
        for name, avocado_name in original_names_to_avocado_names.items()
    }


def _rename_function_calls(file_path: Path, name_to_rename_data: dict[str, RenameData]) -> None:
    """Rename function calls in the given source file for which an Avocado stub exists.

    Args:
        file_path: The C source file to modify (i.e., apply renaming to).
        name_to_rename_data: Map from original function names to their rename metadata.
    """
    src_content = file_path.read_bytes()
    parsed_src = C_PARSER.parse(src_content)

    def _is_identifier_renamed(node: Node) -> bool:
        assert node.text is not None, (
            f"Expected a call_identifier node '{node}' to have a non-None 'text' field"
        )
        return node.text is not None and node.text.decode() in name_to_rename_data

    call_identifiers = get_call_identifiers(parsed_src.root_node)
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
        function_name = call_node.text.decode()
        avocado_function_name = name_to_rename_data[function_name].avocado_name

        logger.debug(f"Renaming call to {function_name} -> {avocado_function_name} in {file_path}")
        renamed_src[start:end] = avocado_function_name.encode()

    file_path.write_bytes(bytes(renamed_src))


def _get_function_identifiers_for_avocado_stub_renaming(tree: Tree) -> list[Node]:
    """Return the identifier nodes parsed from function definitions and declarations for renaming.

    Args:
        tree (Tree): The tree from which to start collecting identifiers.

    Returns:
        list[Node]: The identifier nodes parsed from function definitions and declarations for
            renaming.
    """
    return [
        function_id
        for function_id in get_function_identifiers(tree.root_node)
        if _should_prepend_avocado_prefix(function_id)
    ]


def _should_prepend_avocado_prefix(node: Node) -> bool:
    """Return True iff the given node should be renamed with the _avocado_ prefix.

    A node should be renamed iff:
        - It is an identifier node
        - It does NOT begin with:
            - `__CPROVER`.
            - `_avocado_`(indicating it has been already renamed).
            - `__VERIFIER`

    Args:
        node (Node): The node to check for renaming.

    Returns:
        bool: True iff the node should be renamed with the _avocado_ prefix.
    """
    if node.type == "identifier":
        assert node.text is not None, (
            f"Expected an identifier node: '{node}' to have a non-None .text field"
        )
        return not (
            re.match(DO_NOT_RENAME_PATTERN, node.text.decode()) or node.text.decode() == "if"
        )
    return False


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
            msg = f"Identifier node '{ident_node}' was missing a '.text' attribute"
            logger.error(msg)
            raise ValueError(msg)
        original_function_identifier = ident_node.text.decode()
        expected_identifier = original_function_identifier.encode()
        original_slice = bytes(renamed_src[start:end])
        if original_slice != expected_identifier:
            msg = (
                "Refusing to rename non-identifier slice at "
                f"[{start}:{end}]: expected {expected_identifier!r}, got {original_slice!r}"
            )
            logger.error(msg)
            raise ValueError(msg)
        renamed_function_id = f"{AVOCADO_FUNCTION_PREFIX}{original_function_identifier}"
        logger.debug(f"Renaming {original_function_identifier} -> {renamed_function_id}")
        original_names_to_avocado_names[original_function_identifier] = renamed_function_id
        renamed_src[start:end] = renamed_function_id.encode()
    return (bytes(renamed_src), original_names_to_avocado_names)


if __name__ == "__main__":
    main()
