from typing import Any, Dict
from pathlib import Path


def extract_func(filename: Path, func_analysis: Any) -> str:
    """Return the source code of a function given its analysis info.

    Args:
        filename (str): The name of the source code file.
        func_analysis (JSON): The function analysis info from LLVM.

    Returns:
        str: The source code of a function given its analysis info.
    """
    start_line = func_analysis["startLine"]
    start_col = func_analysis["startCol"]
    end_col = func_analysis["endCol"]
    end_line = func_analysis["endLine"]

    with open(filename, mode="r", encoding="utf-8") as f:
        lines = f.readlines()

    if start_line < 1 or end_line > len(lines) or start_line > end_line:
        raise ValueError("Invalid line range in function analysis")

    func_lines = lines[start_line - 1 : end_line]
    func_lines[0] = func_lines[0][start_col - 1 :]
    func_lines[-1] = func_lines[-1][: end_col - 1]

    return "".join(func_lines)


def get_llvm_func_analysis(func_name: str, llvm_analysis: Dict[str, Any]) -> Any | None:
    """Return an LLVM function analysis for a function with the given name.

    Args:
        func_name (str): The function for which to return an LLVM function analysis.
        llvm_analysis (Dict[str, Any]): The LLVM analysis.

    Returns:
        Any | None: The LLVM function analysis for a function with the given name, otherwise None.
    """
    func_analysis = next(
        (f for f in llvm_analysis["functions"] if f["name"] == func_name), None
    )
    # This should not happen
    if func_analysis is None:
        print(f"Function {func_name} not found in LLVM analysis, skipping.")
        return None
    return func_analysis
