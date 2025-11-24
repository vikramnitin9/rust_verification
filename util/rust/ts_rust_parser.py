"""Tree-sitter based Rust Parser Class."""

from pathlib import Path

import tree_sitter_rust as tsrust
from tree_sitter import Language, Node, Parser

from .rust_parser import RustFunction, RustTypeWrapper


class TsRustParser:
    """Class for parsing Rust source code via tree-sitter (TS).

    Attributes:
        _parser (Parser): The tree-sitter parser used to parse Rust source code.

    """

    _parser: Parser

    def __init__(self) -> None:
        rs_language = Language(tsrust.language())
        self._parser = Parser(rs_language)

    def get_functions_defined_in_file(self, file_name: str) -> dict[str, RustFunction]:
        """Return the Rust functions defined in the given file.

        Args:
            file_name (str): The file from which to parse Rust functions.

        Returns:
            list[RustFunction]: The list of Rust functions defined in the given file.
        """
        path_to_src = Path(file_name)
        tree = self._parser.parse(path_to_src.read_bytes())
        function_nodes = self._collect_nodes_of_type(tree.root_node, typ="function_item")
        parsed_fns = [self._parse_rust_function(fn_node) for fn_node in function_nodes]
        return {fn.name: fn for fn in parsed_fns if fn}

    def _collect_nodes_of_type(self, root_node: Node, typ: str) -> list[Node]:
        target_nodes, stack = [], [root_node]
        while stack:
            curr_node = stack.pop()
            if curr_node.type == typ:
                target_nodes.append(curr_node)
            stack.extend(curr_node.children)
        return target_nodes

    def _parse_rust_function(self, function_item_node: Node) -> RustFunction | None:
        fn_name = function_item_node.child_by_field_name("name")
        param_nodes = function_item_node.child_by_field_name("parameters")
        param_to_type: dict[str, RustTypeWrapper] = {}
        if not fn_name or not param_nodes:
            return None
        if not fn_name.text:
            return None
        if not param_nodes.named_children:
            # Zero-argument function declaration.
            return RustFunction(name=fn_name.text.decode("utf-8"), param_to_type=param_to_type)

        for param_node in param_nodes.named_children:
            name_and_type = self._parse_parameter(param_node)
            if name_and_type:
                name, typ = name_and_type
                param_to_type[name] = typ
        return RustFunction(name=fn_name.text.decode("utf-8"), param_to_type=param_to_type)

    def _parse_parameter(self, parameter_node: Node) -> tuple[str, RustTypeWrapper]:
        param_name_node = parameter_node.child_by_field_name("pattern")
        param_type_node = parameter_node.child_by_field_name("type")
        assert param_name_node and param_name_node.text, (
            f"Malformed parameter node: {parameter_node}"
        )
        assert param_type_node and param_type_node.text, (
            f"Malformed parameter node: {parameter_node}"
        )
        print(parameter_node)
        return (
            param_name_node.text.decode(encoding="utf-8"),
            self._get_rust_type_wrapper(param_type_node),
        )

    def _get_rust_type_wrapper(self, type_node: Node) -> RustTypeWrapper:
        match type_node.type:
            case tnode if tnode == "primitive_type" or tnode == "type_identifier":
                assert type_node.text, f"Malformed parameter node: {type_node}"
                return RustTypeWrapper(
                    rust_type=type_node.text.decode(encoding="utf-8"), is_reference=False
                )
            case "reference_type":
                is_mutable_reference = any(
                    child.type == "mutable_specifier" for child in type_node.children
                )
                base_type = type_node.child_by_field_name("type")
                assert base_type and base_type.text, f"Malformed base type node: {base_type}"
                return RustTypeWrapper(
                    rust_type=base_type.text.decode(encoding="utf-8"),
                    is_reference=True,
                    is_mutable=is_mutable_reference,
                )
            case unhandled_type:
                assert type_node.text, f"Malformed type node: {type_node}"
                msg = (
                    f"Unhandled type in RustTypeWrapper creation: "
                    f"'{unhandled_type}', type node = {type_node.text.decode(encoding='utf-8')}"
                )
                raise RuntimeError(msg)
