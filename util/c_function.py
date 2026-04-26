"""Represents a C function parsed from source code."""

import pathlib
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .function_specification import FunctionSpecification
from .text_util import prepend_line_numbers, uncomment_cbmc_annotations


@dataclass(eq=False)
class CFunction:
    """Represents a C function parsed from a C source file."""

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
    source_code_with_specs: str

    arg_names: list[str] = field(default_factory=list)
    arg_types: list[str] = field(default_factory=list)
    enums: list[Any] = field(default_factory=list)
    callee_names: list[str] = field(default_factory=list)
    global_vars: list[Any] = field(
        default_factory=list
    )  # Cannot call this `globals` as it is a Python keyword.
    structs: list[Any] = field(default_factory=list)
    # An external function is a function that is not in the immediate call graph parsed from the
    # system under verification. For example, it might be a library function or a stub function
    # (e.g., `verification/cbmc_stubs`).
    # If an implementation (not just the signature) is available for the external function, it is
    # added to the call graph.
    is_external_function: bool = False

    def __init__(
        self,
        name: str,
        signature: str,
        file_name: str,
        start_line: int,
        start_col: int,
        end_line: int,
        end_col: int,
        callee_names: list[str],
        *,
        is_external_function: bool = False,
    ) -> None:
        """Create a new CFunction."""
        self.name = name
        self.signature = signature
        self.file_name = file_name
        self.start_line = start_line
        self.start_col = start_col
        self.end_line = end_line
        self.end_col = end_col
        self.callee_names = callee_names
        self.is_external_function = is_external_function
        self.num_args = 0
        self.return_type = ""
        self.preconditions = []
        self.postconditions = []
        self.source_code_with_specs = ""
        self._cached_source_code = ""
        self.arg_names = []
        self.arg_types = []
        self.enums = []
        self.global_vars = []
        self.structs = []

    def get_source_code(
        self,
        include_documentation_comments: bool = False,
        include_line_numbers: bool = False,
        should_uncomment_cbmc_annotations: bool = False,
    ) -> str:
        """Return the source code for this function read from the original file on disk.

        When called without any formatting options, the result is cached in `_cached_source_code`
        so subsequent plain calls avoid a repeated disk read. Calls with formatting options always
        read from disk, as the formatted result cannot be safely stored alongside the unformatted
        cache.

        Args:
            include_documentation_comments (bool): True iff documentation comments appearing before
                the function signature should be included.
            include_line_numbers (bool): True iff line numbers should be included.
            should_uncomment_cbmc_annotations (bool): True iff any CBMC annotations in the source
                code should be uncommented.

        Returns:
            str: The source code for this function.
        """
        no_formatting = not (
            include_documentation_comments
            or include_line_numbers
            or should_uncomment_cbmc_annotations
        )

        if self._cached_source_code and no_formatting:
            return self._cached_source_code

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
        # These two statements handle "end" before "beginning", in case they are on the same line.
        func_lines[-1] = func_lines[-1][: self.end_col]
        func_lines[0] = func_lines[0][self.start_col - 1 :]

        if should_uncomment_cbmc_annotations:
            func_lines = uncomment_cbmc_annotations(func_lines)

        source_code = "".join(func_lines)

        if no_formatting:
            self._cached_source_code = source_code

        documentation = self.get_preceding_lines_starting_with_comment_delimiters()

        if include_documentation_comments and documentation:
            source_code = f"{documentation}\n{source_code}"

        if include_line_numbers:
            start_line_offset = (
                len(documentation.splitlines())
                if include_documentation_comments and documentation
                else 0
            )
            source_code = self._add_line_numbers(
                source_code=source_code, start_line_offset=start_line_offset
            )

        return source_code

    def set_source_code_with_specs(self, source_code: str) -> None:
        """Store the source code for this function with specifications inserted.

        Args:
            source_code (str): The source code with specifications inserted.
        """
        self.source_code_with_specs = source_code

    def invalidate_source_code_fields(self) -> None:
        """Clear this function's `_cached_source_code` and `source_code_with_specs` field."""
        self._cached_source_code = ""
        self.source_code_with_specs = ""

    def get_source_code_with_specs(self) -> str:
        """Return the source code of this function with CBMC specs inserted.

        Returns:
            str: The source code of this function with CBMC specs inserted.
        """
        return self.source_code_with_specs

    def _add_line_numbers(self, source_code: str, start_line_offset: int) -> str:
        """Return source code with line numbers prepended to each line.

        The start_line_offset parameter is non-zero when there is preceding documentation that
        should be included with the function.

        Args:
            source_code (str): The source code to which to prepend line numbers.
            start_line_offset (int): The start line offset.

        Returns:
            str: The source code of the function with line numbers prepended.
        """
        return "\n".join(
            f"{line}: {content}"
            for line, content in prepend_line_numbers(
                source_code.splitlines(), self.start_line - start_line_offset, self.end_line + 1
            )
        )

    def get_preceding_lines_starting_with_comment_delimiters(self) -> str | None:
        r"""Return the lines immediately preceding this function that start with comment delimiters.

        For example, given the function:

        // This is a comment
        int f()
        {
            return 1;
        }

        Return "// This is a comment".

        Additionally, given the function:

        /**
        * Hello, world!
        */
        int g()

        Return "/**\n* Hello, world!\n*/".

        Returns:
            str | None: The documentation comments for this function or None if there are no
                comments.
        """
        lines = pathlib.Path(self.file_name).read_text(encoding="utf-8").splitlines()

        # Function start/end lines are 1-indexed.
        # But the function signature could be on line 2 of the file, while a comment is on line 1.
        i = self.start_line - 2
        comments: list[str] = []
        multi_line_comment_seen = False
        while i >= 0:
            curr_line = lines[i]
            if not multi_line_comment_seen and (not curr_line or curr_line.isspace()):
                break
            if self._is_line_starting_comment(curr_line):
                multi_line_comment_seen = curr_line.endswith("*/") and "/*" not in curr_line
                comments.append(curr_line)
            elif multi_line_comment_seen:
                comments.append(curr_line)
            i -= 1
        comments.reverse()  # Necessary since we walk the source file backwards from the definition.
        return "\n".join(comments) if comments else None

    def _is_line_starting_comment(self, line: str) -> bool:
        """Return True iff a line starts a comment.

        See Mike's (lightly edited) note below for why we cannot use this as a general comment
        detector:

        "It's impossible to know whether a line is part of a comment, without seeing the entire
        file in which the line appears. Maybe this function is determining whether the given line
        starts a comment."

        Args:
            line (str): The line to check for a comment.

        Returns:
            bool: True iff a line comprises a comment (or part of one).

        """
        stripped_line = line.strip()
        # Mike's note: A line starting with "*" could be part of a multiline multiplication
        # expression.
        comment_starts = ("//", "/*", "*")

        # Mike's note: a comment can begin in the middle of a line rather than at the end of one.
        if stripped_line.startswith(comment_starts):
            # This is fine, since we're determining whether a line starts a comment.
            # There is, however, the possibility of a false positive when a multi-line
            # multiplication expression is encountered.
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

    def is_self_recursive(self) -> bool:
        """Return True iff this function is self-recursive.

        Returns:
            bool: True iff this function is self-recursive.
        """
        return self.name in self.callee_names

    def set_specifications(self, specifications: FunctionSpecification) -> None:
        """Set the specifications for this function.

        Args:
            specifications (FunctionSpecification): The specifications for this function.
        """
        self.preconditions, self.postconditions = specifications

    def get_summary_for_prompt(self) -> str:
        """Return the summary of this function as it appears in a prompt to an LLM.

        A summary for a function in an LLM prompt comprises its name, signature (which also includes
        its name), and its pre and postconditions (if it has either).

        For example, the C function below:

        ```c
        void swap(int* a, int* b)
        __CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))
        __CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
        __CPROVER_ensures(*a == __CPROVER_old(*b))
        __CPROVER_ensures(*b == __CPROVER_old(*a))
        {
            int t = *a;
            *a = *b;
            *b = t;
        }
        ```

        Would have the following summary:

        Function name: swap
        Function signature: void swap(int* a, int* b)
        Preconditions: __CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int))),
            __CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
        Postconditions: __CPROVER_ensures(*a == __CPROVER_old(*b)),
            __CPROVER_ensures(*b == __CPROVER_old(*a))

        Returns:
            str: The summary of this function as it appears in a prompt to an LLM.
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

    def __hash__(self) -> int:
        """Return a hash based on this function's name and signature.

        Returns:
            int: The hash based on this function's name and signature.
        """
        return hash(
            (self.name, CFunction.normalize_signature(self.signature), Path(self.file_name).name)
        )

    def __eq__(self, other: object) -> bool:
        """Return True iff this function is equivalent to another.

        Equality is based on whether two functions have the same name, signature, and file name
        attributes.

        Returns:
            bool: True iff this function is equivalent to another.
        """
        if not isinstance(other, CFunction):
            return False
        normalized_signature = CFunction.normalize_signature(self.signature)
        other_normalized_signature = CFunction.normalize_signature(other.signature)
        return (
            self.name == other.name
            and normalized_signature == other_normalized_signature
            and Path(self.file_name).name == Path(other.file_name).name
        )

    @staticmethod
    def normalize_signature(signature: str) -> str:
        r"""Return a signature with canonical spacing for stable comparisons.

          This normalization runs in two regex passes:

          1. re.sub(r"\s+", " ", signature).strip() collapses runs of whitespace
              (spaces, tabs, newlines) into a single space and trims leading/trailing spaces.
          2. re.sub(r"\s*([(),])\s*", r"\1", normalized) removes surrounding
              whitespace around `(`, `)`, and `,` while preserving the punctuation via the
              capture group `([(),])` and replacement backreference `\1`.

          Together these steps make equivalent signatures compare equal even when ParseC or source
          formatting differs only by whitespace.

        Args:
            signature (str): The signature string to normalize.

        Returns:
            str: The signature with normalized spacing around common punctuation.
        """
        normalized = re.sub(r"\s+", " ", signature).strip()
        return re.sub(r"\s*([(),])\s*", r"\1", normalized)
