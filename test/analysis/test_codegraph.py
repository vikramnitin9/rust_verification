from pathlib import Path

from analysis import CallGraph


def test_simple_file_no_recursion() -> None:
    simple_c_file = Path("test/data/callgraph/simple.c")
    callgraph = CallGraph(simple_c_file)
    assert callgraph.get_names_of_recursive_functions() == []


def test_graph_with_direct_recursion() -> None:
    path_to_file = Path("test/data/callgraph/direct_recursion.c")
    callgraph = CallGraph(path_to_file)
    assert callgraph.get_names_of_recursive_functions() == ["recursive_function"]


def test_remove_recursive_functions() -> None:
    path_to_file = Path("test/data/callgraph/direct_recursion.c")
    unmodified_callgraph = CallGraph(path_to_file)
    assert unmodified_callgraph.get_names_of_recursive_functions() == ["recursive_function"]

    callgraph_no_loops = unmodified_callgraph.prune_self_loops()
    assert callgraph_no_loops.get_names_of_recursive_functions() == []
    assert unmodified_callgraph.get_names_of_recursive_functions() == ["recursive_function"]


def test_get_functions_reverse_topological_ordering() -> None:
    path_to_file = Path("test/data/callgraph/ordering.c")
    callgraph = CallGraph(path_to_file)
    reverse_topological_ordering = callgraph.get_function_names_in_topological_order(
        reverse_order=True
    )
    # All callers must come after the callee in a reverse topological ordering
    for caller, callee in callgraph.call_graph.edges():
        caller_index = reverse_topological_ordering.index(caller)
        callee_index = reverse_topological_ordering.index(callee)
        assert caller_index > callee_index, (
            f"{caller} calls {callee}, but appears before {callee} in the reverse topological sort"
        )
