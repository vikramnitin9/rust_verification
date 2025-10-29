"""Represents the result of running ParseC over C source code."""

from __future__ import annotations

import json
import os
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import networkx as nx

from util.parsec_function import ParsecFunction


@dataclass
class ParsecResult:
    """Represents the top-level result obtained by running `parsec` on a C file.

    ParseC is a LLVM/Clang-based tool to parse a C program (hence the name).
    It extracts functions, structures, etc. along with their inter-dependencies.
    """

    enums: list[Any] = field(default_factory=list)
    files: list[str] = field(default_factory=list)
    functions: dict[str, ParsecFunction] = field(default_factory=dict)

    def __init__(self, file_path: Path):
        analysis_file = self._run_parsec(file_path)
        with Path(analysis_file).open(encoding="utf-8") as f:
            parsec_analysis = json.load(f)
            function_analyses = [ParsecFunction(f) for f in parsec_analysis.get("functions", [])]
            self.enums = parsec_analysis.get("enums", [])
            self.files = parsec_analysis.get("files", [])
            self.functions = {analysis.name: analysis for analysis in function_analyses}

    def get_analysis_for_function(self, function_name: str) -> ParsecFunction | None:
        """Return the ParsecFunction representation for a function with the given name.

        Args:
            function_name (str): The name of the function for which to return the ParsecFunction.

        Returns:
            ParsecFunction | None: The ParsecFunction, otherwise None.
        """
        return self.functions.get(function_name, None)

    def get_callees(self, function: ParsecFunction) -> list[ParsecFunction]:
        """Return the callees of the given function.

        Args:
            function (ParsecFunction): The function for which to return the callees.

        Returns:
            list[ParsecFunction]: The callees of the given function.
        """
        callees: list[ParsecFunction] = []
        for callee_name in function.callee_names:
            if callee_analysis := self.get_analysis_for_function(callee_name):
                callees.append(callee_analysis)
            else:
                print(f"LLVM Analysis for callee function {callee_name} not found")
        return callees

    def get_call_graph(self) -> nx.DiGraph:  # type: ignore[type-arg]
        """Return the call graph for this Parsec result.

        Returns:
            nx.DiGraph: The call graph for this Parsec result.
        """
        call_graph: nx.DiGraph[str] = nx.DiGraph()
        for func_name, func in self.functions.items():
            call_graph.add_node(func_name)
            for callee_name in func.callee_names:
                call_graph.add_edge(func_name, callee_name)
        return call_graph

    def _run_parsec(self, file_path: Path) -> Path:
        parsec_build_dir = os.environ.get("PARSEC_BUILD_DIR")
        if not parsec_build_dir:
            raise Exception("$PARSEC_BUILD_DIR not set.")
        try:
            cmd = f"{parsec_build_dir}/parsec --rename-main=false --add-instr=false {file_path}"
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            if result.returncode != 0:
                msg = f"Error running parsec: {result.stderr}"
                raise Exception(msg)
        except subprocess.CalledProcessError as e:
            raise Exception("Error running parsec.") from e

        path_to_result = Path("analysis.json")
        if not path_to_result.exists():
            raise Exception("parsec failed to produce an analysis")
        return path_to_result
