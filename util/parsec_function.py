"""Represents the ParseC representation for a C function."""

import pathlib
from dataclasses import dataclass, field
from typing import Any

from .function_specification import FunctionSpecification
from .parsec_error import ParsecError
from .text_util import prepend_line_numbers, uncomment_cbmc_annotations


@dataclass
# MDE: I would rename this to "CFunction", but the current name is also OK.
class ParsecFunction:
    """Represents a C function as parsed by ParseC."""

    # MDE: Cross-reference to the documentation of ParseC, so that a reader can understand the
    # meaning of each of these fields.
    name: str
    num_args: int
    return_type: str
    signature: str
    file_name: str
    start_line: int  # 1-indexed
    start_col: int
    end_line: int  # 1-indexed
    end_col: int
    preconditions: list[str]
    postconditions: list[str]
    arg_names: list[str] = field(default_factory=list)
    arg_types: list[str] = field(default_factory=list)
    enums: list[Any] = field(default_factory=list)
    callee_names: list[str] = field(default_factory=list)
    # MDE: Minor: I would name this `global_vars` rather than `llvm_globals`, which is not as clear.
    llvm_globals: list[Any] = field(
        default_factory=list
    )  # Cannot call this `globals` as it is a Python keyword.
    structs: list[Any] = field(default_factory=list)

    def __init__(self, raw_analysis: dict[str, Any]):
        """Create a new ParsecFunction."""
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

    def get_source_code(
        self,
        include_documentation_comments: bool = False,
        include_line_numbers: bool = False,
        should_uncomment_cbmc_annotations: bool = False,
    ) -> str:
        """Return the source code for this function, optionally including documentation comments.

        Args:
            include_documentation_comments (bool): True iff documentation comments appearing before
                the function signature should be included.
            include_line_numbers (bool): True iff line numbers should be included.
            should_uncomment_cbmc_annotations (bool): True iff any CBMC annotations in the source
                code should be uncommented.

        Returns:
            str: The source code for this function, optionally including documentation comments and
                line numbers.
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
        # Handle "end" before "beginning", in case they are on the same line.
        func_lines[-1] = func_lines[-1][: self.end_col]
        func_lines[0] = func_lines[0][self.start_col - 1 :]

        if should_uncomment_cbmc_annotations:
            func_lines = uncomment_cbmc_annotations(func_lines)

        source_code = "".join(func_lines)

        # MDE: This functionality feels independent of the rest of this function.  I suggest
        # removing it from this method and instead putting it in a function of its own.
        if include_line_numbers:
            source_code = "\n".join(
                f"{line}: {content}"
                for line, content in prepend_line_numbers(
                    source_code.splitlines(), self.start_line, self.end_line + 1
                )
            )

        if include_documentation_comments:
            if documentation := self.get_preceding_comments():
                if include_line_numbers:
                    documentation_lines = documentation.splitlines()
                    documentation = "\n".join(
                        f"{line}: {content}"
                        for line, content in prepend_line_numbers(
                            documentation_lines,
                            self.start_line - len(documentation_lines),
                            self.start_line,
                        )
                    )
                source_code = f"{documentation}\n{source_code}"
        return source_code

    def get_preceding_comments(self) -> str | None:
        """Return the content of lines immediately preceding this function (usually documentation).

        # MDE: "the content of lines": which lines are included.
        # MDE: "usually documentation": what is it when it isn't documentation?

        Returns:
            str | None: The documentation comments for this function or None if there are no
                comments.
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
                multi_line_comment_seen = curr_line.endswith("*/") and "/*" not in curr_line
                comments.append(curr_line)
            elif multi_line_comment_seen:
                comments.append(curr_line)
            i -= 1
        comments.reverse()  # Necessary since we walk the source file backwards from the definition.
        return "\n".join(comments) if comments else None

    def _is_comment(self, line: str) -> bool:
        """Return True iff a line comprises a comment (or part of one).

        # MDE: It's impossible to know whether a line is part of a comment, without seeing the
        # entire file in which the line appears.  Maybe this function is determining whether the
        # given line starts a comment.

        Args:
            line (str): The line to check for a comment.

        Returns:
            bool: True iff a line comprises a comment (or part of one).

        """
        stripped_line = line.strip()
<<<<<<< HEAD
        # MDE: A line starting with "*" could be part of a multiline multiplication expression.
        comment_start_delimiters = ["//", "/*", "*"]

        # MDE: a comment can begin in the middle of a line rather than at the end of one.
        if any(stripped_line.startswith(delimit) for delimit in comment_start_delimiters):
=======
        comment_starts = ("//", "/*", "*")

        if stripped_line.startswith(comment_starts):
>>>>>>> main
            return True

        if stripped_line.endswith("*/"):
            comment_start = stripped_line.find("/*")
            # Catch cases like
            # int global = 1; /* this is a bad practice */
            # which we should not include.
            return comment_start <= 0 or not stripped_line[:comment_start].strip()

        return False

    def has_specification(self) -> bool:
        """Return True iff this function has pre- or post-conditions.

        Returns:
            bool: True iff this function has pre- or post-conditions.
        """
        return len(self.preconditions) > 0 or len(self.postconditions) > 0

    # MDE: I would use "is_self_recursive" which is more common term (according to a Google search).
    def is_direct_recursive(self) -> bool:
        """Return True iff this function is directly recursive.

        Returns:
            bool: True iff this function is directly recursive.
        """
        return self.name in self.callee_names

    def set_specifications(self, specifications: FunctionSpecification) -> None:
        """Set the specifications for this function.

        Args:
            specifications (FunctionSpecification): The specifications for this function.
        """
        self.preconditions, self.postconditions = specifications

    # MDE: Since this routine is for LLM prompting, give it a descriptive name rather than taking
    # over the standard function used for debugging output.
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
