def extract_func(filename, func_analysis) -> str:
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

    with open(filename, "r") as f:
        lines = f.readlines()

    func_lines = lines[start_line - 1 : end_line]
    func_lines[0] = func_lines[0][start_col - 1 :]
    func_lines[-1] = func_lines[-1][: end_col - 1]

    return "".join(func_lines)
