from pathlib import Path
from util import LLVMAnalysis

import networkx as nx
import copy


class CodeGraph:
    """Represents a code graph, used to determine the order in which specifications are generated.

    Attributes:
        path_to_input_file (str): The path to the input source code file for which this code graph is constructed.
        llvm_analysis (LLVMAnalysis): The result of running an LLVM code graph analysis on the input file.
        call_graph (nx.DiGraph): The call graph, derived from the LLVM analysis via networkx.
    """

    path_to_input_file: Path
    llvm_analysis: LLVMAnalysis
    call_graph: nx.DiGraph  # type: ignore[type-arg]

    def __init__(self, path_to_input_file: Path):
        self.path_to_input_file = path_to_input_file
        self.llvm_analysis = LLVMAnalysis(path_to_input_file)
        self.call_graph = self.llvm_analysis.get_call_graph()

    def remove_recursive_loops(self) -> "CodeGraph":
        """Return a copy of this code graph, with self-edges (i.e., recursive calls) removed.

        Returns:
            CodeGraph: A copy of this code graph, with self-edges removed.
        """
        codegraph_copy = copy.deepcopy(self)
        self_loops = list(nx.selfloop_edges(codegraph_copy.call_graph))
        codegraph_copy.call_graph.remove_edges_from(self_loops)
        return codegraph_copy

    def get_names_of_recursive_functions(self) -> list[str]:
        """Return the names of directly-recursive functions in this code graph.

        Note: I do not think this detects mutually-recursive functions.

        Returns:
            list[str]: The names of directly-recursive functions in this code graph.
        """
        return [f for f in self.call_graph if self.call_graph.has_edge(f, f)]

    def get_function_names_in_topological_order(
        self, reverse_order: bool = False
    ) -> list[str]:
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
                "Cycles detected in call graph. Using DFS postorder traversal for function ordering"
            )
            func_names = [f for f in self.call_graph.nodes if f != ""]
            if not func_names:
                return []
            return list(nx.dfs_postorder_nodes(self.call_graph, source=func_names[0]))
