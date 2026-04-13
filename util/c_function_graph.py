"""Represents the result of parsing one or more C source files."""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

import networkx as nx
from loguru import logger

from util.tree_sitter_util import get_functions_from_file

if TYPE_CHECKING:
    from util.c_function import CFunction

DEFAULT_EXTERNAL_FUNCTION_DIR: Path = Path("/app/verification/cbmc_stubs/")
_DEFAULT_EXTERNAL_DOCUMENTATION_JSON: str = (
    "/app/verification/docs/ansi_c_library_documentation.json"
)


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

    def __init__(
        self, input_path: Path, external_function_dir: Path = DEFAULT_EXTERNAL_FUNCTION_DIR
    ) -> None:
        """Create a CFunctionGraph from the given C file or directory that contains C files.

        If the path is a single file, that file is parsed.

        If the path is a directory, all `*.c` files found recursively under the
        directory are parsed.

        Any callee that is not found in the project is looked up in the documentation manager to
        determine which header declares it.

        The corresponding `.c` file (same base name, `.c` extension) is resolved under
        `external_function_dir` and, if present, parsed and added to the graph.

        Args:
            input_path (Path): The path to a file or directory to be analyzed.
            external_function_dir (Path): The directory containing `.c` files for
                external functions.
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
            function_analyses.extend(get_functions_from_file(c_file))

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

        self._load_external_callees(Path(external_function_dir))

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
        return get_functions_from_file(file_path)

    def _load_external_callees(
        self,
        external_function_dir: Path,
    ) -> None:
        """Parse and load files for callee functions not found in the project.

        For each callee name absent from `self.functions`, the documentation manager is queried
        for the header that declares it. The corresponding `.c` file (header basename with
        `.c` extension) is resolved under `external_function_dir` and, if it exists, parsed via
        `load_external_functions`.

        Args:
            external_function_dir (Path): Directory containing `.c` files for external functions.
        """
        # Lazy import to avoid a circular dependency: util → verification → util.
        from verification.external_function_documentation_manager import (  # noqa: PLC0415
            ExternalFunctionDocumentationManager,
        )

        documentation_manager = ExternalFunctionDocumentationManager(
            _DEFAULT_EXTERNAL_DOCUMENTATION_JSON
        )

        unknown_callees = {
            callee_name
            for func in self.functions.values()
            for callee_name in func.callee_names
            if callee_name not in self.functions
        }

        stub_paths: set[Path] = set()
        for callee_name in unknown_callees:
            header = documentation_manager.get_header_declaring_function(callee_name)
            if header is None:
                continue
            stub_path = external_function_dir / Path(header).with_suffix(".c").name
            if stub_path.exists():
                stub_paths.add(stub_path)

        if stub_paths:
            self._load_external_functions(list(stub_paths))

    def _load_external_functions(self, paths: list[Path]) -> None:
        """Parse functions from external files and add them to the graph.

        Note: We could cache functions that have already been parsed. We can revisit this if it
        turns out to be a performance bottleneck.

        Functions found in the project always take precedence over external functions — if a name
        collision occurs the project function is kept. Edges between project functions and external
        functions (and between external functions) are wired into the call graph after all external
        functions have been loaded.

        Args:
            paths (list[Path]): Paths to external C source files (e.g. library stubs).
        """
        # Lazy import to avoid a circular dependency: util → verification → util.
        from verification.avocado_stub_util import AVOCADO_FUNCTION_PREFIX  # noqa: PLC0415

        for path in paths:
            for fn in get_functions_from_file(path):
                if fn.name not in self.functions:
                    fn.is_external_function = True
                    self.functions[fn.name] = fn
                    self.call_graph.add_node(fn)
                    # External stubs are stored under their prefixed name (e.g.
                    # `_avocado_memcpy`), but callers reference the original name
                    # (e.g. `memcpy`). Register an alias so both names resolve to
                    # the same function.
                    if fn.name.startswith(AVOCADO_FUNCTION_PREFIX):
                        original_name = fn.name[len(AVOCADO_FUNCTION_PREFIX) :]
                        if original_name not in self.functions:
                            self.functions[original_name] = fn

        # Re-wire edges now that the full function set is known.
        for func in self.functions.values():
            for callee_name in func.callee_names:
                if callee := self.functions.get(callee_name):
                    if not self.call_graph.has_edge(func, callee):
                        self.call_graph.add_edge(func, callee)

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
