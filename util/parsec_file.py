"""Represents the result of running ParseC over C source code."""

from __future__ import annotations

import copy
import json
import os
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import networkx as nx
from loguru import logger

from util import text_util
from util.c_function import CFunction


@dataclass
class ParsecFile:
    """Represents the top-level result obtained by running `parsec` on a single C file.

    For more details on these fields, see the ParseC documentation:
    https://github.com/vikramnitin9/parsec/blob/main/README.md

    Note: The functions in a `ParsecFile` do not have specifications. This is due to the the fact
    that LLVM cannot parse CBMC specs, which are not instances of valid C grammar.

    ParseC is a LLVM/Clang-based tool to parse a C program (hence the name).
    It extracts functions, structures, etc. along with their inter-dependencies.

    Note that ParseC can be run on a single C file, or a project.
    However, our current implementation of ParsecFile only supports running ParseC on a single C file.
    See https://github.com/vikramnitin9/rust_verification/issues/69

    """

    # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
    # NOTE: Each node in call_graph represents a function name and is of type `str`.
    call_graph: nx.DiGraph  # type: ignore[type-arg]
    file_path: Path

    # ParseC returns a list of dictionaries with one list item per function.
    # We parse these into CFunction objects and index them by function name.
    # This could have problems for static functions with the same name in different files.
    # The projects we are currently using to test our tool do not have static functions,
    # but this needs to be kept in mind for complex projects.
    functions: dict[str, CFunction] = field(default_factory=dict)

    # Enums, structs, and global_vars are all represented as lists of dictionaries
    # For the exact format of these dictionaries, see the ParseC documentation (linked above).
    enums: list[dict[str, Any]] = field(default_factory=list)
    structs: list[dict[str, Any]] = field(default_factory=list)
    global_vars: list[dict[str, Any]] = field(default_factory=list)

    def __init__(self, file_path: Path):
        """Create an instance of ParsecFile from the file at `file_path`.

        Args:
            file_path (Path): The path to a JSON file written by ParseC.
        """
        self.file_path = file_path
        parsec_analysis = self._run_parsec(file_path)
        function_analyses = [CFunction(f) for f in parsec_analysis.get("functions", [])]
        self.enums = parsec_analysis.get("enums", [])
        self.structs = parsec_analysis.get("structs", [])
        self.global_vars = parsec_analysis.get("globals", [])
        self.functions = {analysis.name: analysis for analysis in function_analyses}
        # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
        # NOTE: Each node in call_graph represents a function name and is of type `str`.
        self.call_graph: nx.DiGraph = nx.DiGraph()  # type: ignore[type-arg]
        for func_name, func in self.functions.items():
            self.call_graph.add_node(func_name)
            for callee_name in func.callee_names:
                self.call_graph.add_edge(func_name, callee_name)

    @staticmethod
    def parse_source_with_cbmc_annotations(
        path_to_file_with_cbmc_annotations: Path,
    ) -> ParsecFile:
        """Create an instance of ParsecFile by parsing a .c file with CBMC annotations.

        Parsec relies on an LLVM parser, which does not admit C programs with CBMC annotations.
        A workaround is to comment-out the CBMC annotations.

        Args:
            path_to_file_with_cbmc_annotations (Path): The file with CBMC annotations.

        Returns:
            ParsecFile: The ParsecFile.
        """
        content_of_file_with_cbmc_annotations = (
            path_to_file_with_cbmc_annotations.read_text(encoding="utf-8").splitlines()
        )
        file_lines_with_commented_out_annotations = "\n".join(
            text_util.comment_out_cbmc_annotations(
                content_of_file_with_cbmc_annotations
            )
        )
        tmp_file_with_commented_out_cbmc_annotations = Path(
            f"{path_to_file_with_cbmc_annotations.with_suffix('')}-cbmc-commented-out{path_to_file_with_cbmc_annotations.suffix}"
        )
        tmp_file_with_commented_out_cbmc_annotations.write_text(
            file_lines_with_commented_out_annotations,
            encoding="utf-8",
        )
        return ParsecFile(tmp_file_with_commented_out_cbmc_annotations)

    def get_function_or_none(self, function_name: str) -> CFunction | None:
        """Return the CFunction representation for a function with the given name.

        Args:
            function_name (str): The name of the function for which to return the CFunction.

        Returns:
            CFunction | None: The CFunction with the given name, or None if no function
                with that name exists.
        """
        return self.functions.get(function_name, None)

    def get_function(self, function_name: str) -> CFunction:
        """Return the CFunction representation for a function with the given name.

        Args:
            function_name (str): The name of the function for which to return the CFunction.

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
            function (CFunction): The function for which to return the callees.

        Returns:
            list[CFunction]: The callees of the given function.
        """
        callees: list[CFunction] = []
        for callee_name in function.callee_names:
            if callee_analysis := self.get_function_or_none(callee_name):
                callees.append(callee_analysis)
            else:
                logger.error(
                    f"LLVM Analysis for callee function {callee_name} not found"
                )
        return callees

    def get_names_of_recursive_functions(self) -> list[str]:
        """Return the names of directly-recursive functions in this ParsecFile's call graph.

        Note: This does not detect mutually-recursive functions.

        Returns:
            list[str]: The names of directly-recursive functions in this ParsecFile's call graph.
        """
        return [f for f in self.call_graph if self.call_graph.has_edge(f, f)]

    def get_function_names_in_topological_order(
        self, reverse_order: bool = False
    ) -> list[str]:
        """Return the function names in this ParsecFile's call graph in topological order.

        Args:
            reverse_order (bool, optional): True iff the topological ordering should be reversed.
                Defaults to False.

        Returns:
            list[str]: The function names in this Parsec File's call graph in topological order.
        """
        # Self-edges must be removed before computing the topological sort.
        # Operate over a copy of the call graph to avoid modifying the original graph.
        call_graph_copy = copy.copy(self.call_graph)
        self_edges = nx.selfloop_edges(call_graph_copy)
        call_graph_copy.remove_edges_from(self_edges)

        if not call_graph_copy.nodes():
            return []
        try:
            names_in_topological_order = list(nx.topological_sort(call_graph_copy))
            if reverse_order:
                names_in_topological_order.reverse()
            return names_in_topological_order
        except nx.NetworkXUnfeasible:
            logger.warning(
                "Cycles detected in call graph: "
                "Using postorder DFS traversal for function ordering."
            )
            return self._get_function_names_in_postorder_dfs(
                reverse_order=reverse_order
            )

    def _get_function_names_in_postorder_dfs(self, reverse_order: bool) -> list[str]:
        """Return the function names in this ParsecFile's call graph collected via DFS traversal.

        Args:
            reverse_order (bool): True iff the result of the DFS traversal should be reversed.

        Returns:
            list[str]: The function names in this ParsecFile's call graph collected via a DFS
                traversal.
        """
        result = list(nx.dfs_postorder_nodes(self.call_graph))
        if reverse_order:
            result.reverse()
        return result

    # MDE: Please document and discuss relationship to other functions with similar names.
    def _run_parsec(self, file_path: Path) -> dict[str, Any]:
        """Internal function that run the parsec executable and returns its results.

        Args:
            file_path (Path): The path to a C file to be analyzed by ParseC.

        Returns:
            dict[str, Any]: The JSON output produced by ParseC as a dictionary.
        """
        parsec_build_dir = os.environ.get("PARSEC_BUILD_DIR")
        if not parsec_build_dir:
            raise Exception("$PARSEC_BUILD_DIR not set.")
        try:
            cmd = f"{parsec_build_dir}/parsec --rename-main=false --add-instr=false {file_path}"
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            if result.returncode != 0:
                msg = f"Error running parsec: {result.stderr} {result.stdout}"
                raise Exception(msg)
        except subprocess.CalledProcessError as e:
            raise Exception("Error running parsec.") from e

        path_to_result = Path("analysis.json")
        if not path_to_result.exists():
            raise Exception("parsec failed to produce an analysis")
        with path_to_result.open(encoding="utf-8") as f:
            parsec_analysis = json.load(f)
        return parsec_analysis
