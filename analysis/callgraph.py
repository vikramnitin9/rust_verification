"""Module for working with call graphs generated via ParseC."""

import copy
from pathlib import Path

import networkx as nx

from util import ParsecResult


class CallGraph:
    """Represents a call graph, used to determine the order in which specifications are generated.

    Attributes:
        input_file (Path): The path to the input source code file for which this call graph
            is constructed.
        parsec_result (ParsecResult): The result of running ParseC on the input file.
        call_graph (nx.DiGraph): The call graph, derived from the LLVM analysis via networkx.
    """

    input_file: Path
    parsec_result: ParsecResult
    call_graph: nx.DiGraph  # type: ignore[type-arg]

    def __init__(self, input_file: Path):
        self.input_file = input_file
        self.parsec_result = ParsecResult(input_file)
        self.call_graph = self.parsec_result.get_call_graph()

    def remove_self_edges(self) -> "CallGraph":
        """Return a copy of this call graph, with self-edges (i.e., direct recursive calls) removed.

        Note: This operation does not remove any nodes from the call graph.

        Returns:
            CallGraph: A copy of this call graph, with self-edges removed.
        """
        callgraph_copy = copy.deepcopy(self)
        self_loops = list(nx.selfloop_edges(callgraph_copy.call_graph))
        callgraph_copy.call_graph.remove_edges_from(self_loops)
        return callgraph_copy

    def get_names_of_recursive_functions(self) -> list[str]:
        """Return the names of directly-recursive functions in this code graph.

        Note: This does not detect mutually-recursive functions.

        Returns:
            list[str]: The names of directly-recursive functions in this code graph.
        """
        return [f for f in self.call_graph if self.call_graph.has_edge(f, f)]

    def get_function_names_in_topological_order(self, reverse_order: bool = False) -> list[str]:
        """Return the function names in this code graph in topological order.

        Args:
            reverse_order (bool, optional): True iff the topological ordering should be reversed.
                Defaults to False.

        Returns:
            list[str]: The function names in this code graph in topological order.
        """
        if not self.call_graph.nodes():
            return []
        try:
            names_in_topological_order = list(nx.topological_sort(self.call_graph))
            if reverse_order:
                names_in_topological_order.reverse()
            return names_in_topological_order
        except nx.NetworkXUnfeasible:
            print(
                "Cycles detected in call graph: "
                "Using postorder DFS traversal for function ordering."
            )
            return self._get_function_names_in_postorder_dfs(reverse_order=reverse_order)

    def _get_function_names_in_postorder_dfs(self, reverse_order: bool) -> list[str]:
        """Return the function names in this code graph collected via a DFS traversal.

        Args:
            reverse_order (bool): True iff the result of the DFS traversal should be reversed.

        Returns:
            list[str]: The function names in this code graph collected via a DFS traversal.
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
