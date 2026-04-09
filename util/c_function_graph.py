"""Represents the result of parsing one or more C source files."""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

import networkx as nx
from loguru import logger

from util.tree_sitter_util import parse_c_file

if TYPE_CHECKING:
    from pathlib import Path

    from util.c_function import CFunction


@dataclass
class CFunctionGraph:
    """Represents the result of parsing a "project": one or more C source files.

    Functions are extracted using tree-sitter.
    """

    # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
    # NOTE: Each node in call_graph is a CFunction.
    call_graph: nx.DiGraph  # type: ignore[type-arg]
    # This is an absolute path to either a single file or a directory containing multiple files.
    input_path: Path | None = None
    files: list[str] = field(default_factory=list)
    # The key for `functions` is a function name.
    # This will not work if static functions have the same name in different files.
    functions: dict[str, CFunction] = field(default_factory=dict)

    enums: list[dict[str, Any]] = field(default_factory=list)
    structs: list[dict[str, Any]] = field(default_factory=list)
    global_vars: list[dict[str, Any]] = field(default_factory=list)

    def __init__(self, input_path: Path) -> None:
        """Create a CFunctionGraph from the given C file or directory that contains C files.

        If the path is a single file, that file is parsed.

        If the path is a directory, all `*.c` files found recursively under the
        directory are parsed.

        Args:
            input_path (Path): The path to a file or directory to be analyzed.
        """
        self.input_path = input_path

        if input_path.is_file():
            c_files = [input_path]
        elif input_path.is_dir():
            c_files = list(input_path.rglob("*.c"))
        else:
            msg = f"Path does not exist or is not a file or directory: {input_path}"
            raise FileNotFoundError(msg)

        if not c_files:
            msg = f"No .c files found in: {input_path}"
            raise FileNotFoundError(msg)

        function_analyses: list[CFunction] = []
        for c_file in c_files:
            function_analyses.extend(parse_c_file(c_file))

        self.files = [str(f) for f in c_files]
        self.functions = {analysis.name: analysis for analysis in function_analyses}
        self.enums = []
        self.structs = []
        self.global_vars = []

        # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
        # Each node in call_graph is a CFunction.
        self.call_graph: nx.DiGraph = nx.DiGraph()  # type: ignore[type-arg]
        for func in self.functions.values():
            self.call_graph.add_node(func)
            for callee_name in func.callee_names:
                if callee := self.functions.get(callee_name):
                    self.call_graph.add_edge(func, callee)

    @staticmethod
    def get_functions_defined_in_file(file_path: Path) -> list[CFunction]:
        """Return the functions defined in the given file.

        Args:
            file_path (Path): The path to the file from which to extract functions.

        Returns:
            list[CFunction]: The CFunctions parsed from the given file.
        """
        if file_path.is_dir():
            msg = f"Expected a file at {file_path}, but got a directory"
            raise ValueError(msg)
        return parse_c_file(file_path)

    def get_function_or_none(self, function_name: str) -> CFunction | None:
        """Return the CFunction representation for the function with the given name, or None.

        Args:
            function_name (str): The name of the function.

        Returns:
            CFunction | None: The CFunction with the given name, or None if no function
                with that name exists.
        """
        return self.functions.get(function_name)

    def get_function(self, function_name: str) -> CFunction:
        """Return the CFunction representation for the function with the given name.

        Args:
            function_name (str): The name of the function.

        Returns:
            CFunction: The CFunction with the given name.

        Raises:
            RuntimeError: if no function with that name exists.
        """
        result = self.get_function_or_none(function_name)
        if result is None:
            msg = f"No function named '{function_name}' exists"
            raise RuntimeError(msg)
        return result

    def get_callees(self, function: CFunction) -> list[CFunction]:
        """Return the callees of the given function.

        Args:
            function (CFunction): The function whose callees are returned.

        Returns:
            list[CFunction]: The callees of the given function.
        """
        callees: list[CFunction] = []
        for callee_name in function.callee_names:
            if callee_analysis := self.get_function_or_none(callee_name):
                callees.append(callee_analysis)
            else:
                logger.warning(
                    f"Callee function {callee_name} was missing from the project analysis"
                )
        return callees

    def get_functions_in_topological_order(self, *, reverse_order: bool = False) -> list[CFunction]:
        """Return the CFunctions in this CFunctionGraph's call graph in topological order.

        Note: If a topological ordering is impossible, this function will topologically sort
        the condensation graph of SCCs, then choose a postorder DFS within each SCC.

        Args:
            reverse_order (bool, optional): True iff the topological ordering should be reversed.
                Defaults to False.

        Returns:
            list[CFunction]: The CFunctions in this CFunctionGraph's call graph in topological
                order.
        """
        if not self.call_graph.nodes():
            return []

        # Self-edges must be removed before computing the topological sort.
        # Operate over a copy of the call graph to avoid modifying the original graph.
        call_graph_copy = copy.copy(self.call_graph)
        self_edges = nx.selfloop_edges(call_graph_copy)
        call_graph_copy.remove_edges_from(self_edges)

        functions: list[CFunction] = []
        try:
            functions = list(nx.topological_sort(call_graph_copy))
        except nx.NetworkXUnfeasible:
            logger.error("Cycles detected in call graph. Performing best-effort topological sort.")
            condensation = nx.condensation(call_graph_copy)
            for scc in nx.topological_sort(condensation):
                scc_subgraph = call_graph_copy.subgraph(condensation.nodes[scc]["members"])
                functions.extend(nx.dfs_postorder_nodes(scc_subgraph))

        return list(reversed(functions)) if reverse_order else functions
