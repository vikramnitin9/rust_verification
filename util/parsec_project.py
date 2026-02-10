"""Represents the result of running ParseC over C source code."""

from __future__ import annotations

import copy
import json
import subprocess
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any

import networkx as nx
from loguru import logger

from util import text_util
from util.c_function import CFunction


class ParsecRunMode(str, Enum):
    """Defines run modes for Parsec."""

    FILE = "FILE"
    DIRECTORY = "DIRECTORY"


@dataclass
class ParsecProject:
    """Represents the result of parsing a "project": one or more C source files.

    The fields of this class are populated from the result of running ParseC.
    For more details on the fields of this class, see the ParseC documentation:
    https://github.com/vikramnitin9/parsec/blob/main/README.md

    ParseC is a LLVM/Clang-based tool to parse a C program.
    It extracts functions, structures, etc. along with their inter-dependencies.
    """

    # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
    # NOTE: Each node in call_graph is a CFunction.
    call_graph: nx.DiGraph  # type: ignore[type-arg]
    # Exactly one of file_path and project_root is populated, depending on whether this
    # ParsecProject represents a single file or a directory of files.
    file_path: Path | None = None
    project_root: Path | None = None
    files: list[str] = field(default_factory=list)
    # ParseC returns one dictionary per function.
    # Each dictionary is parsed into CFunction objects, which are indexed by function name.
    # This could have problems for static functions with the same name in different files.
    # The projects we are currently using to test our tool do not have static functions,
    # but this needs to be kept in mind for complex projects.
    functions: dict[str, CFunction] = field(default_factory=dict)

    # For the exact format of these dictionaries, see the ParseC documentation (linked above).
    enums: list[dict[str, Any]] = field(default_factory=list)
    structs: list[dict[str, Any]] = field(default_factory=list)
    global_vars: list[dict[str, Any]] = field(default_factory=list)

    def __init__(self, input_path: Path):
        """Create a ParsecProject from the given file or directory.

        If the path is a single file, that file is analyzed.

        If the path is a directory, the directory must contain a compile_commands.json
        compilation database located at `{input_path}/compile_commands.json`.
        All C source files referenced in the compilation database are analyzed.

        Args:
            input_path (Path): The path to a file or directory to be analyzed.
        """
        if input_path.is_dir():
            compile_commands_path = input_path / "compile_commands.json"
            if not compile_commands_path.exists():
                msg = f"compile_commands.json not found in {input_path}"
                raise FileNotFoundError(msg)
            self.project_root = input_path
            parsec_analysis = self._run_parsec(input_path, run_mode=ParsecRunMode.DIRECTORY)
        else:
            self.file_path = input_path
            parsec_analysis = self._run_parsec(input_path, run_mode=ParsecRunMode.FILE)

        function_analyses = [CFunction(f) for f in parsec_analysis.get("functions", [])]
        self.enums = parsec_analysis.get("enums", [])
        self.files = parsec_analysis.get("files", [])
        self.functions = {analysis.name: analysis for analysis in function_analyses}
        self.global_vars = parsec_analysis.get("global_vars", [])
        self.structs = parsec_analysis.get("structs", [])
        # "ignore[type-arg]" because nx.DiGraph does not expose subscriptable types.
        # Each node in call_graph is a CFunction.
        self.call_graph: nx.DiGraph = nx.DiGraph()  # type: ignore[type-arg]
        for func in self.functions.values():
            self.call_graph.add_node(func)
            for callee_name in func.callee_names:
                if callee := self.functions.get(callee_name):
                    self.call_graph.add_edge(func, callee)

    @staticmethod
    def parse_source_with_cbmc_annotations(
        path_to_file_with_cbmc_annotations: Path,
    ) -> ParsecProject:
        """Create a ParsecProject by parsing a .c file with CBMC annotations.

        Any CBMC annotations are ignored and do not appear in the result.

        Args:
            path_to_file_with_cbmc_annotations (Path): The file with CBMC annotations.

        Returns:
            ParsecProject: The ParsecProject.
        """
        lines_of_file_with_cbmc_annotations = path_to_file_with_cbmc_annotations.read_text(
            encoding="utf-8"
        ).splitlines()
        lines_of_file_with_commented_out_annotations = "\n".join(
            text_util.comment_out_cbmc_annotations(lines_of_file_with_cbmc_annotations)
        )
        tmp_file_with_commented_out_cbmc_annotations = Path(
            f"{path_to_file_with_cbmc_annotations.with_suffix('')}-cbmc-commented-out{path_to_file_with_cbmc_annotations.suffix}"
        )
        tmp_file_with_commented_out_cbmc_annotations.write_text(
            lines_of_file_with_commented_out_annotations,
            encoding="utf-8",
        )
        return ParsecProject(tmp_file_with_commented_out_cbmc_annotations)

    def get_function_or_none(self, function_name: str) -> CFunction | None:
        """Return the CFunction representation for the function with the given name.

        Args:
            function_name (str): The name of the function.

        Returns:
            CFunction | None: The CFunction with the given name, or None if no function
                with that name exists.
        """
        return self.functions.get(function_name, None)

    def get_function(self, function_name: str) -> CFunction:
        """Return the CFunction representation for a function with the given name.

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
                logger.error(f"LLVM Analysis for callee function {callee_name} not found")
        return callees

    def get_functions_in_topological_order(self, reverse_order: bool = False) -> list[CFunction]:
        """Return the CFunctions in this ParsecProject's call graph in topological order.

        Note: If a topological ordering is impossible, this function defaults to returning the
        functions collected via a postorder DFS traversal.

        Args:
            reverse_order (bool, optional): True iff the topological ordering should be reversed.
                Defaults to False.

        Returns:
            list[CFunction]: The CFunctions in this ParsecProject's call graph in topological order.
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
            logger.error(
                "Cycles detected in call graph: "
                "Using postorder DFS traversal for function ordering."
            )
            functions = list(nx.dfs_postorder_nodes(call_graph_copy))

        return list(reversed(functions)) if reverse_order else functions

    def _run_parsec(self, path: Path, run_mode: ParsecRunMode) -> dict[str, Any]:
        """Return the result of running Parsec at the given path.

        The path represents a file or directory path, depending on the run mode.

        Args:
            path (Path): The path at which to run Parsec.
            run_mode (ParsecRunMode): The run mode.

        Returns:
            dict[str, Any]: The result of running Parsec at the given path.
        """
        cmd = f"parsec --rename-main=false --add-instr=false {
            path if run_mode == ParsecRunMode.FILE else f'-p {path}'
        }"
        result = None
        try:
            if run_mode == ParsecRunMode.FILE:
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            elif run_mode == ParsecRunMode.DIRECTORY:
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=path)
        except subprocess.CalledProcessError as e:
            raise RuntimeError("Error running parsec") from e

        if not result:
            msg = f"Failed to run parsec due to an unrecognized run mode = {run_mode}"
            raise RuntimeError(msg)

        path_to_result = Path("analysis.json")
        if not path_to_result.exists():
            raise Exception("parsec failed to produce an analysis")
        return json.loads(path_to_result.read_text(encoding="utf-8"))
