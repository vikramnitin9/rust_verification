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
from util.parsec_function import ParsecFunction


@dataclass
class ParsecFile:
    """Represents the top-level result obtained by running `parsec` on a C project (or file).

    Note: The functions in a `ParsecFile` do not have specifications. This is due to the the fact
    that LLVM cannot parse CBMC specs, which are not instances of valid C grammar.

    ParseC is a LLVM/Clang-based tool to parse a C program (hence the name).
    It extracts functions, structures, etc. along with their inter-dependencies.

    ParseC can be run on a single C file, or a project. In the case where it is run on a single C
    file, the `enums` and `files` fields will be empty.

    See: parsec/README.md for additional documentation.
    """

    # MDE: There should be a comment stating the type of the nodes in `call_graph`, even if the
    # type-checker cannot utilize it.
    # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
    call_graph: nx.DiGraph  # type: ignore[type-arg]
    file_path: Path
    enums: list[Any] = field(default_factory=list)
    files: list[str] = field(default_factory=list)
    functions: dict[str, ParsecFunction] = field(default_factory=dict)

    def __init__(self, file_path: Path):
        """Create an instance of ParsecFile from the file at `file_path`.

        Args:
            file_path (Path): The path to a JSON file written by ParseC.
        """
        self.file_path = file_path
        analysis_result_file = self._run_parsec(file_path)
        with Path(analysis_result_file).open(encoding="utf-8") as f:
            parsec_analysis = json.load(f)
            function_analyses = [ParsecFunction(f) for f in parsec_analysis.get("functions", [])]
            self.enums = parsec_analysis.get("enums", [])
            self.files = parsec_analysis.get("files", [])
            self.functions = {analysis.name: analysis for analysis in function_analyses}
            # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
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
        content_of_file_with_cbmc_annotations = path_to_file_with_cbmc_annotations.read_text(
            encoding="utf-8"
        ).splitlines()
        file_lines_with_commented_out_annotations = "\n".join(
            text_util.comment_out_cbmc_annotations(content_of_file_with_cbmc_annotations)
        )
        tmp_file_with_commented_out_cbmc_annotations = Path(
            f"{path_to_file_with_cbmc_annotations.with_suffix('')}-cbmc-commented-out{path_to_file_with_cbmc_annotations.suffix}"
        )
        tmp_file_with_commented_out_cbmc_annotations.write_text(
            file_lines_with_commented_out_annotations,
            encoding="utf-8",
        )
        return ParsecFile(tmp_file_with_commented_out_cbmc_annotations)

    def copy(self, *, remove_self_edges_in_call_graph: bool = False) -> ParsecFile:
        """Return a copy of this ParsecFile, optionally removing its call graph's self-edges.

        Args:
            remove_self_edges_in_call_graph (bool, optional): True iff the call graph's self-edges
                should be removed. Defaults to False.

        Returns:
            ParsecFile: A copy of this ParsecFile.
        """
        parsec_file_copy = copy.deepcopy(self)
        if remove_self_edges_in_call_graph:
            self_edges = nx.selfloop_edges(self.call_graph)
            parsec_file_copy.call_graph.remove_edges_from(self_edges)
        return parsec_file_copy

    def get_function_or_none(self, function_name: str) -> ParsecFunction | None:
        """Return the ParsecFunction representation for a function with the given name.

        Args:
            function_name (str): The name of the function for which to return the ParsecFunction.

        Returns:
            ParsecFunction | None: The ParsecFunction with the given name, or None if no function
                with that name exists.
        """
        return self.functions.get(function_name, None)

    def get_function(self, function_name: str) -> ParsecFunction:
        """Return the ParsecFunction representation for a function with the given name.

        Args:
            function_name (str): The name of the function for which to return the ParsecFunction.

        Returns:
            ParsecFunction: The ParsecFunction with the given name.

        Raises:
            RuntimeError: if no function with that name exists.
        """
        result = self.get_function_or_none(function_name)
        if result is None:
            msg = f"No function named '{function_name}' exists"
            raise RuntimeError(msg)
        return result

    def get_callees(self, function: ParsecFunction) -> list[ParsecFunction]:
        """Return the callees of the given function.

        Args:
            function (ParsecFunction): The function for which to return the callees.

        Returns:
            list[ParsecFunction]: The callees of the given function.
        """
        callees: list[ParsecFunction] = []
        for callee_name in function.callee_names:
            if callee_analysis := self.get_function_or_none(callee_name):
                callees.append(callee_analysis)
            else:
                logger.error(f"LLVM Analysis for callee function {callee_name} not found")
        return callees

    def get_names_of_recursive_functions(self) -> list[str]:
        """Return the names of directly-recursive functions in this ParsecFile's call graph.

        Note: This does not detect mutually-recursive functions.

        Returns:
            list[str]: The names of directly-recursive functions in this ParsecFile's call graph.
        """
        return [f for f in self.call_graph if self.call_graph.has_edge(f, f)]

    def get_function_names_in_topological_order(self, reverse_order: bool = False) -> list[str]:
        """Return the function names in this ParsecFile's call graph in topological order.

        Args:
            reverse_order (bool, optional): True iff the topological ordering should be reversed.
                Defaults to False.

        Returns:
            list[str]: The function names in this Parsec Result's call graph in topological order.
        """
        if not self.call_graph.nodes():
            return []
        try:
            names_in_topological_order = list(nx.topological_sort(self.call_graph))
            if reverse_order:
                names_in_topological_order.reverse()
            return names_in_topological_order
        except nx.NetworkXUnfeasible:
            logger.warning(
                "Cycles detected in call graph: "
                "Using postorder DFS traversal for function ordering."
            )
            return self._get_function_names_in_postorder_dfs(reverse_order=reverse_order)

    def _get_function_names_in_postorder_dfs(self, reverse_order: bool) -> list[str]:
        """Return the function names in this ParsecFile's call graph collected via DFS traversal.

        Args:
            reverse_order (bool): True iff the result of the DFS traversal should be reversed.

        Returns:
            list[str]: The function names in this ParsecFile's call graph collected via a DFS
                traversal.
        """
        func_names = [f for f in self.call_graph.nodes if f != ""]
        visited: set[str] = set()
        result: list[str] = []
        for f in func_names:
            if f not in visited:
                for node in nx.dfs_postorder_nodes(self.call_graph, source=f):
                    if node not in visited:
                        visited.add(node)
                        result.append(node)
        if reverse_order:
            result.reverse()
        return result

    def _run_parsec(self, file_path: Path) -> Path:
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
        return path_to_result
