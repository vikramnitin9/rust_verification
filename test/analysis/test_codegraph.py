from pathlib import Path

from analysis import CodeGraph


def test_simple_file_no_recursion() -> None:
    simple_c_file = Path("test/data/codegraph/simple.c")
    codegraph = CodeGraph(simple_c_file)
    assert codegraph.get_names_of_recursive_functions() == []


def test_graph_with_direct_recursion() -> None:
    path_to_file = Path("test/data/codegraph/direct_recursion.c")
    codegraph = CodeGraph(path_to_file)
    assert codegraph.get_names_of_recursive_functions() == ["recursive_function"]


def test_remove_recursive_functions() -> None:
    path_to_file = Path("test/data/codegraph/direct_recursion.c")
    unmodified_codegraph = CodeGraph(path_to_file)
    assert unmodified_codegraph.get_names_of_recursive_functions() == ["recursive_function"]

    codegraph_no_loops = unmodified_codegraph.remove_recursive_loops()
    assert codegraph_no_loops.get_names_of_recursive_functions() == []
    assert unmodified_codegraph.get_names_of_recursive_functions() == ["recursive_function"]


def test_get_functions_reverse_topological_ordering() -> None:
    path_to_file = Path("test/data/codegraph/ordering.c")
    codegraph = CodeGraph(path_to_file)
    reverse_topological_ordering = codegraph.get_function_names_in_topological_order(
        reverse_order=True
    )
    # All callers must come after the callee in a reverse topological ordering
    for caller, callee in codegraph.call_graph.edges():
        caller_index = reverse_topological_ordering.index(caller)
        callee_index = reverse_topological_ordering.index(callee)
        assert caller_index > callee_index, (
            f"{caller} calls {callee}, but appears before {callee} in the reverse topological sort"
        )
