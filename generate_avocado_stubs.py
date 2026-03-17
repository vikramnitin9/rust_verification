#!/opt/miniconda3/bin/python

"""Generate stub files for libraries defined by the ANSI-C standard, modified for use w/Avocado."""

import argparse
import pickle as pkl
import re
from collections import defaultdict
from pathlib import Path

import tree_sitter_c as tsc
from loguru import logger
from tree_sitter import Language, Node, Parser, Tree

from util.tree_sitter_util import (
    IdentifierNodeParentType,
    get_function_identifiers,
    get_identifier_nodes_from_call_expressions,
)
from verification.avocado_stub_util import (
    AVOCADO_FUNCTION_PREFIX,
    C_KEYWORD_FILE_PATH,
    RenameData,
)

C_LANGUAGE = Language(tsc.language())
C_PARSER = Parser(C_LANGUAGE)
C_KEYWORDS = {
    kw for kw in Path(C_KEYWORD_FILE_PATH).read_text().splitlines() if not kw.startswith("//")
}

CPROVER_PREFIX = "__CPROVER"
VERIFIER_PREFIX = "__VERIFIER"
DO_NOT_RENAME_PATTERN = (
    rf"^({re.escape(AVOCADO_FUNCTION_PREFIX)}|"
    rf"{re.escape(VERIFIER_PREFIX)}|{re.escape(CPROVER_PREFIX)})"
)


def main() -> None:
    """Generate the modified stub files in-place for libraries in the ANSI-C standard.

    See the documentation in `avocado_stub_util.py` for additional details.

    CBMC's stubs of the functions declared in the ANSI-C standard are found here:

            https://github.com/diffblue/cbmc/tree/develop/src/ansi-c/library

    This script requires a local copy of the C files under that directory.

    For each function declaration and definition, we rename the function by prepending `_avocado_`.
    This is a workaround for: https://github.com/diffblue/cbmc/issues/8844

    Function calls for any of the renamed functions are also updated (i.e., renamed) to reflect
    the new names.
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
        help=(
            "Path to the directory containing C files from: "
            "https://github.com/diffblue/cbmc/tree/develop/src/ansi-c/library. "
            "Renaming is done in-place."
        ),
    )
    args = parser.parse_args()
    c_src_dir = args.c_sources
    c_src_files = list(Path(c_src_dir).glob("*.c"))

    all_renamed_functions: dict[str, list[RenameData]] = defaultdict(list)

    # Step 1: rename function declarations and definitions in the C stubs matching the check in
    # `_should_prepend_avocado_prefix`.
    for c_src in c_src_files:
        # Note: rename_data is a list, since an identifier could be found in a definition and
        # declaration. We need to keep track of this information.
        original_identifier_to_rename_data_from_file = (
            _rename_function_declarations_and_definitions(c_src)
        )
        for (
            original_identifier,
            rename_data,
        ) in original_identifier_to_rename_data_from_file.items():
            all_renamed_functions[original_identifier].extend(rename_data)

    # Step 2: For which an Avocado stub exists, rename function calls in the C stubs.
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
) -> dict[str, list[RenameData]]:
    """Rename each function in a C file (e.g., a program, library) to its Avocado stub identifier.

    This updates each file in-place.

    Args:
        path_to_src (Path): The path to the original C file.

    Returns:
        dict[str, list[RenameData]]: The rename data for each function in the original C file.
    """
    logger.debug(f"Processing {path_to_src}")
    src_content = path_to_src.read_bytes()
    parsed_src = C_PARSER.parse(src_content)
    function_identifier_and_parent_node_types = _get_function_identifiers_for_avocado_stub_renaming(
        parsed_src
    )
    src_after_renaming, original_names_to_avocado_names = (
        _rename_function_declarations_and_definitions_in_src_in_place(
            src_content, function_identifier_and_parent_node_types
        )
    )
    path_to_src.write_text(src_after_renaming.decode(), encoding="utf-8")
    rename_data = defaultdict(list)
    for name, (avocado_name, parent_node_type) in original_names_to_avocado_names.items():
        rename_data[name].append(RenameData(avocado_name, parent_node_type, path_to_src))
    return rename_data


def _rename_function_calls(
    file_path: Path, identifier_to_rename_data: dict[str, list[RenameData]]
) -> None:
    """In the source file, rename function calls for which an Avocado stub exists.

    Args:
        file_path: The C source file to modify (i.e., apply renaming to).
        identifier_to_rename_data: Map from original function identifiers to their rename data.
    """
    src_content = file_path.read_bytes()
    parsed_src = C_PARSER.parse(src_content)

    def _should_rename_identifier_node(node: Node) -> bool:
        """Return True iff the node is an identifier node that should be renamed.

        An identifier node should be renamed if it is found in identifier_to_rename_data.

        Args:
            node (Node): The node to check for renaming, it must be a node of type `identifier`.

        Returns:
            bool: True iff the node is an identifier node that should be renamed.
        """
        assert node.type == "identifier", f"Expected '{node}' to be an 'identifier' node."
        assert node.text is not None, (
            f"Expected a call_identifier node '{node}' to have a non-None 'text' field"
        )
        if node.parent is None or node.parent.type != "call_expression":
            return False
        return node.text.decode() in identifier_to_rename_data

    identifier_node_from_call_expressions_and_parent_nodes = (
        get_identifier_nodes_from_call_expressions(parsed_src.root_node)
    )
    identifier_nodes_to_rename = [
        identifier_node
        for identifier_node, _ in identifier_node_from_call_expressions_and_parent_nodes
        if _should_rename_identifier_node(identifier_node)
    ]

    if not identifier_nodes_to_rename:
        return

    # Apply renaming in the given source file, in descending byte order.
    renamed_src = bytearray(src_content)
    for identifier_node_from_call_expression_node in sorted(
        identifier_nodes_to_rename, key=lambda node: node.start_byte, reverse=True
    ):
        start = identifier_node_from_call_expression_node.start_byte
        end = identifier_node_from_call_expression_node.end_byte
        function_name = identifier_node_from_call_expression_node.text.decode()

        renamed_function_name = _get_avocado_function_identifier(function_name)

        logger.debug(f"Renaming call to {function_name} -> {renamed_function_name} in {file_path}")
        renamed_src[start:end] = renamed_function_name.encode()

    file_path.write_bytes(bytes(renamed_src))


def _get_function_identifiers_for_avocado_stub_renaming(
    tree: Tree,
) -> list[tuple[Node, IdentifierNodeParentType]]:
    """Return the identifier nodes parsed from function definitions and declarations for renaming.

    Args:
        tree (Tree): The tree from which to start collecting identifiers.

    Returns:
        list[tuple[Node, IdentifierNodeParentType]]: The identifier nodes parsed from function
            definitions and declarations for renaming.
    """
    return [
        function_id_and_parent_type
        for function_id_and_parent_type in get_function_identifiers(tree.root_node)
        if _should_rename(function_id_and_parent_type[0])
    ]


def _should_rename(node: Node) -> bool:
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
        identifier_text = node.text.decode()
        if identifier_text in C_KEYWORDS:
            # Do not rename any C keywords.
            return False
        return not any(
            identifier_text.startswith(prefix)
            for prefix in (AVOCADO_FUNCTION_PREFIX, VERIFIER_PREFIX, CPROVER_PREFIX)
        )
    return False


def _rename_function_declarations_and_definitions_in_src_in_place(
    src_content: bytes,
    function_identifier_and_parent_node_type: list[tuple[Node, IdentifierNodeParentType]],
) -> tuple[bytes, dict[str, tuple[str, IdentifierNodeParentType]]]:
    """Return the C source code and map from previous identifiers to Avocado identifiers.

    Note: Renaming is done in-place and only for function declarations and definitions.

    Args:
        src_content (bytes): The source content.
        function_identifier_and_parent_node_type (list[tuple[Node, IdentifierNodeParentType]]):
            The function id nodes to rename along with their parent nodes types.

    Returns:
       tuple[bytes, dict[str, tuple[str, IdentifierNodeParentType]]]: The source content and map
            from previous identifiers to Avocado identifiers.
    """
    renamed_src = bytearray(src_content)
    original_names_to_avocado_names = {}
    for ident_node, parent_node_type in sorted(
        function_identifier_and_parent_node_type, key=lambda pair: pair[0].start_byte, reverse=True
    ):
        start = ident_node.start_byte
        end = ident_node.end_byte
        assert ident_node.text, "An identifier node must have a '.text' attribute"
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
        renamed_function_id = _get_avocado_function_identifier(original_function_identifier)
        logger.debug(f"Renaming {original_function_identifier} -> {renamed_function_id}")
        original_names_to_avocado_names[original_function_identifier] = (
            renamed_function_id,
            parent_node_type,
        )
        renamed_src[start:end] = renamed_function_id.encode()
    return (bytes(renamed_src), original_names_to_avocado_names)


def _get_avocado_function_identifier(original_function_identifier: str) -> str:
    """Return the Avocado function identifier for the given identifier.

    Args:
        original_function_identifier (str): The original function identifier.

    Returns:
        str: The Avocado function identifier for the given identifier.
    """
    return AVOCADO_FUNCTION_PREFIX + original_function_identifier


if __name__ == "__main__":
    main()
