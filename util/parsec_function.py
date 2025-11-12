"""Represents the ParseC representation for a C function."""

import pathlib
from dataclasses import dataclass, field
from typing import Any

from .parsec_error import ParsecError
from .specifications import FunctionSpecification


@dataclass
class ParsecFunction:
    """Represents a C function as parsed by ParseC."""

    name: str
    num_args: int
    return_type: str
    signature: str
    file_name: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int
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
        self.start_line = raw_analysis["startLine"]
        self.start_col = raw_analysis["startCol"]
        self.end_line = raw_analysis["endLine"]
        self.end_col = raw_analysis["endCol"]
        self.preconditions = []
        self.postconditions = []
        self.callee_names = []
        self.arg_names = raw_analysis.get("argNames", [])
        self.arg_types = raw_analysis.get("argTypes", [])
        self.enums = raw_analysis.get("enums", [])
        if "callees" not in raw_analysis:
            msg = f"ParseC result: {raw_analysis} was missing a 'callees' key"
            raise ParsecError(msg)
        callees_of_parsec_function = raw_analysis["callees"]
        for func in callees_of_parsec_function:
            if "name" not in func:
                msg = f"ParseC function: {func} did not have a 'name' key"
                raise ParsecError(msg)
            self.callee_names.append(func["name"])
        self.llvm_globals = raw_analysis.get("globals", [])
        self.structs = raw_analysis.get("structs", [])

    def get_source_code(self, include_documentation_comments: bool = False) -> str:
        """Return the source code for this function, optionally including documentation comments.

        Returns:
            str: The source code for this function, optionally including documentation comments.
        """
        with pathlib.Path(self.file_name).open(encoding="utf-8") as f:
            lines = f.readlines()

        if self.start_line < 1 or self.end_line > len(lines):
            raise ValueError("Function line numbers are out of range of the file.")
        if self.start_line > self.end_line:
            raise ValueError("Function start line is after end line.")
        if self.start_col < 1 or self.end_col < 1:
            raise ValueError("Function column numbers must be 1 or greater.")
        if self.start_line == self.end_line and self.start_col > self.end_col:
            raise ValueError("Function start column is after end column on the same line.")

        # Handle 1-based columns; end_col is inclusive
        func_lines = lines[self.start_line - 1 : self.end_line]
        # Note that "end" comes before "beginning", in case they are on the same line.
        func_lines[-1] = func_lines[-1][: self.end_col]
        func_lines[0] = func_lines[0][self.start_col - 1 :]

        source_code = "".join(func_lines)

        if include_documentation_comments:
            source_code = f"{self.get_documentation_comments()}\n{source_code}"

        return source_code

    def get_documentation_comments(self) -> str:
        """Return the content of lines immediately preceding this function (usually documentation).

        Returns:
            str: The documentation comments for this function.
        """
        with pathlib.Path(self.file_name).open(encoding="utf-8") as f:
            lines = f.read().splitlines()

        # Function start/end lines are 1-indexed.
        # But the function signature could be on line 2 of the file, while a comment is on line 1.
        i = self.start_line - 2
        comments: list[str] = []
        multi_line_comment_seen = False
        while i >= 0:
            curr_line = lines[i]
            if not multi_line_comment_seen and (not curr_line or curr_line.isspace()):
                break
            if self._is_comment(curr_line):
                multi_line_comment_seen = curr_line.endswith("*/")
                comments.append(curr_line)
            elif multi_line_comment_seen:
                comments.append(curr_line)
            i -= 1
        comments.reverse()  # Necessary since we walk the source file backwards from the definition.
        return "\n".join(comments) if comments else ""

    def _is_comment(self, line: str) -> bool:
        """Return True iff a line comprises a comment (or part of one).

        Args:
            line (str): The line to check for a comment.

        Returns:
            bool: True iff a line comprises a comment (or part of one).
        """
        stripped_line = line.strip()
        comment_start_delimiters = ["//", "/*", "*"]
        return any(
            stripped_line.startswith(delimit) for delimit in comment_start_delimiters
        ) or stripped_line.endswith("*/")

    def is_specified(self) -> bool:
        """Return True iff this function has pre- or post-conditions.

        Returns:
            bool: True iff this function has pre- or post-conditions.
        """
        return len(self.preconditions) > 0 or len(self.postconditions) > 0

    def set_specifications(self, specifications: FunctionSpecification) -> None:
        """Set the specifications for this function.

        Args:
            specifications (FunctionSpecification): The specifications for this function.
        """
        self.preconditions, self.postconditions = specifications

    def __str__(self) -> str:
        """Return the string representation of this function.

        This method is meant to be used to embed this function into a prompt for an LLM.

        Returns:
            str: The string representation of this function.
        """
        function_name_and_signature = (
            f"""\nFunction name: {self.name}\nFunction signature: {self.signature}\n"""
        )
        if self.preconditions:
            preconds_in_prompt = ", ".join(self.preconditions)
            function_name_and_signature += f"Preconditions: {preconds_in_prompt}\n"
        if self.postconditions:
            postconds_in_prompt = ", ".join(self.postconditions)
            function_name_and_signature += f"Postconditions: {postconds_in_prompt}\n"
        return function_name_and_signature
