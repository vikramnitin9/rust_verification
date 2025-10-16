from typing import Any
from dataclasses import dataclass, field


@dataclass
class LLVMAnalysis:
    """Represents the top-level LLVM analysis obtained by running parsec on a C file."""

    enums: list[Any] = field(default_factory=list)
    files: list[str] = field(default_factory=list)
    functions: dict[str, "Function"] = field(default_factory=dict)

    @staticmethod
    def from_json(raw_analysis: dict[str, Any]) -> "LLVMAnalysis":
        function_analyses = [
            Function.from_json(f) for f in raw_analysis.get("functions", [])
        ]
        return LLVMAnalysis(
            enums=raw_analysis.get("enums", []),
            files=raw_analysis.get("files", []),
            functions={analysis.name: analysis for analysis in function_analyses},
        )

    def get_analysis_for_function(self, function_name: str) -> "Function | None":
        """Return the LLVM analysis for a function with the given name.

        Args:
            function_name (str): The name of the function for which to return the LLVM analysis.

        Returns:
            Function | None: The LLVM analysis for the function, otherwise None.
        """
        return self.functions.get(function_name, None)


@dataclass
class Function:
    """Represents the LLVM analysis for a C function."""

    name: str
    num_args: int
    return_type: str
    signature: str
    file_name: str
    start_col: int
    start_line: int
    end_col: int
    end_line: int
    arg_names: list[str] = field(default_factory=list)
    arg_types: list[str] = field(default_factory=list)
    enums: list[Any] = field(default_factory=list)
    callee_names: list[str] = field(default_factory=list)
    llvm_globals: list[Any] = field(
        default_factory=list
    )  # Cannot call this `globals` as it is a Python keyword.
    structs: list[Any] = field(default_factory=list)

    @staticmethod
    def from_json(raw_analysis: dict[str, Any]) -> "Function":
        return Function(
            name=raw_analysis["name"],
            num_args=raw_analysis["num_args"],
            return_type=raw_analysis["returnType"],
            signature=raw_analysis["signature"],
            file_name=raw_analysis["filename"],
            start_col=raw_analysis["startCol"],
            start_line=raw_analysis["startLine"],
            end_col=raw_analysis["endCol"],
            end_line=raw_analysis["endLine"],
            arg_names=raw_analysis.get("argNames", []),
            arg_types=raw_analysis.get("argTypes", []),
            enums=raw_analysis.get("enums", []),
            callee_names=[
                func["name"]
                for func in raw_analysis.get("functions", [])
                if "name" in func
            ],
            llvm_globals=raw_analysis.get("globals", []),
            structs=raw_analysis.get("structs", []),
        )

    def get_source_code(self) -> str:
        """Returns the source code for this function.

        Returns:
            str: The source code for this function.
        """
        with open(self.file_name, mode="r", encoding="utf-8") as f:
            lines = f.readlines()

        if self.start_line < 1 or self.end_line > len(lines):
            raise ValueError("Function line numbers are out of range of the file.")
        if self.start_line > self.end_line:
            raise ValueError("Function start line is after end line.")
        if self.start_col < 1 or self.end_col < 1:
            raise ValueError("Function column numbers must be 1 or greater.")
        if self.start_line == self.end_line and self.start_col > self.end_col:
            raise ValueError(
                "Function start column is after end column on the same line."
            )

        # Handle 1-based columns; end_col is inclusive
        if self.start_line == self.end_line:
            line = lines[self.start_line - 1]
            return line[self.start_col - 1 : self.end_col]
        func_lines = lines[self.start_line - 1 : self.end_line]
        # First line: drop everything before start_col
        func_lines[0] = func_lines[0][self.start_col - 1 :]
        # Last line: keep up to end_col (inclusive -> end-exclusive slice)
        func_lines[-1] = func_lines[-1][: self.end_col]
        return "".join(func_lines)
