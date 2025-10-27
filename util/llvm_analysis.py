"""Represents an LLVM analysis over source code."""

from __future__ import annotations

import json
import os
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import networkx as nx

from util.function import LlvmFunction


@dataclass
class LLVMAnalysis:
    """Represents the top-level LLVM analysis obtained by running parsec on a C file."""

    enums: list[Any] = field(default_factory=list)
    files: list[str] = field(default_factory=list)
    functions: dict[str, LlvmFunction] = field(default_factory=dict)

    def __init__(self, file_path: Path):
        # Check if PARSEC_BUILD_DIR is set
        parsec_build_dir = os.environ.get("PARSEC_BUILD_DIR")
        if parsec_build_dir is None:
            raise Exception("Error: $PARSEC_BUILD_DIR not set.")
        try:
            cmd = f"{parsec_build_dir}/parsec --rename-main=false --add-instr=false {file_path}"
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            if result.returncode != 0:
                msg = f"Error running parsec: {result.stderr}"
                raise Exception(msg)
        except subprocess.CalledProcessError as e:
            raise Exception("Error running parsec.") from e

        analysis_file = Path("analysis.json")
        if not analysis_file.exists():
            raise Exception("Error: analysis.json not found after running parsec.")
        with Path(analysis_file).open(encoding="utf-8") as f:
            raw_analysis = json.load(f)
            function_analyses = [LlvmFunction(f) for f in raw_analysis.get("functions", [])]
            self.enums = raw_analysis.get("enums", [])
            self.files = raw_analysis.get("files", [])
            self.functions = {analysis.name: analysis for analysis in function_analyses}

    def get_analysis_for_function(self, function_name: str) -> LlvmFunction | None:
        """Return the LLVM analysis for a function with the given name.

        Args:
            function_name (str): The name of the function for which to return the LLVM analysis.

        Returns:
            LlvmFunction | None: The LLVM analysis for the function, otherwise None.
        """
        return self.functions.get(function_name, None)

    def get_callees(self, function: LlvmFunction) -> list[LlvmFunction]:
        """Return the callees of the given function.

        Args:
            function (LlvmFunction): The function for which to return the callees.

        Returns:
            list[LlvmFunction]: The callees of the given function.
        """
        callees: list[LlvmFunction] = []
        for callee_name in function.callee_names:
            if callee_analysis := self.get_analysis_for_function(callee_name):
                callees.append(callee_analysis)
            else:
                print(f"LLVM Analysis for callee function {callee_name} not found")
        return callees

    def get_call_graph(self) -> nx.DiGraph:  # type: ignore[type-arg]
        """Return the call graph for the LLVM analysis.

        Returns:
            nx.DiGraph: The call graph for the LLVM analysis.
        """
        call_graph: nx.DiGraph[str] = nx.DiGraph()
        for func_name, func in self.functions.items():
            call_graph.add_node(func_name)
            for callee_name in func.callee_names:
                call_graph.add_edge(func_name, callee_name)
        return call_graph
