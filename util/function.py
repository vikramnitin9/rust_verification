from dataclasses import dataclass, field

from typing import Any
from string import Template


TEMPLATE_FOR_FUNCTION_PROMPT = Template("""
Function name: $name
Function signature: $signature
""")


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
    preconditions: list[str]
    postconditions: list[str]
    arg_names: list[str] = field(default_factory=list)
    arg_types: list[str] = field(default_factory=list)
    enums: list[Any] = field(default_factory=list)
    callee_names: list[str] = field(default_factory=list)
    llvm_globals: list[Any] = field(
        default_factory=list
    )  # Cannot call this `globals` as it is a Python keyword.
    structs: list[Any] = field(default_factory=list)

    def __init__(self, raw_analysis: dict[str, Any]):
        self.name = raw_analysis["name"]
        self.num_args = raw_analysis["num_args"]
        self.return_type = raw_analysis["returnType"]
        self.signature = raw_analysis["signature"]
        self.file_name = raw_analysis["filename"]
        self.start_col = raw_analysis["startCol"]
        self.start_line = raw_analysis["startLine"]
        self.end_col = raw_analysis["endCol"]
        self.end_line = raw_analysis["endLine"]
        self.preconditions = []
        self.postconditions = []
        self.arg_names = raw_analysis.get("argNames", [])
        self.arg_types = raw_analysis.get("argTypes", [])
        self.enums = raw_analysis.get("enums", [])
        self.callee_names = [
            func["name"] for func in raw_analysis.get("functions", []) if "name" in func
        ]
        self.llvm_globals = raw_analysis.get("globals", [])
        self.structs = raw_analysis.get("structs", [])

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

    def is_specified(self) -> bool:
        """Return True iff this function has pre- or post-conditions.

        Returns:
            bool: True iff this function has pre- or post-conditions.
        """
        return len(self.preconditions) > 0 or len(self.postconditions) > 0

    def __str__(self) -> str:
        function_for_prompt = TEMPLATE_FOR_FUNCTION_PROMPT.safe_substitute(
            name=self.name,
            signature=self.signature,
        )
        if self.preconditions:
            preconds_in_prompt = ", ".join(self.preconditions)
            function_for_prompt += f"\nPreconditions: {preconds_in_prompt}"
        if self.postconditions:
            postconds_in_prompt = ", ".join(self.postconditions)
            function_for_prompt += f"\nPostconditions: {postconds_in_prompt}"
        return function_for_prompt
