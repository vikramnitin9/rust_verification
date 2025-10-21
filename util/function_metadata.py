from dataclasses import dataclass, field
from string import Template
from .function import Function


TEMPLATE_FOR_FUNCTION_CONTEXT_PROMPT = Template("""
Function name: $name
Function signature: $signature
Preconditions: $preconditions
Postconditions: $postconditions
""")


@dataclass
class FunctionMetadata:
    """A function metadata object.

    Attributes:
        name (str): The name of a function.
        signature (str): The signature of a function.
        preconditions (list[str]): The preconditions of a function.
        postconditions (list[str]): The postconditions of a function.
    """

    name: str
    signature: str
    preconditions: list[str] = field(default_factory=list)
    postconditions: list[str] = field(default_factory=list)

    def get_prompt_str(self) -> str:
        """Return the representation of this function metadata object as it should appear in a prompt.

        Returns:
            str: The representation of this function metadata object as it should appear in a prompt.
        """
        preconditions = ",".join(self.preconditions) if self.preconditions else "None"
        postconditions = (
            ",".join(self.postconditions) if self.postconditions else "None"
        )
        return TEMPLATE_FOR_FUNCTION_CONTEXT_PROMPT.safe_substitute(
            name=self.name,
            signature=self.signature,
            preconditions=preconditions,
            postconditions=postconditions,
        )

    def has_specifications(self) -> bool:
        """Return True iff this function has pre- or post-conditions.

        Returns:
            bool: True iff this function has pre- or post-conditions.
        """
        return len(self.preconditions) > 0 or len(self.postconditions) > 0

    @staticmethod
    def from_function_analysis(function: Function) -> "FunctionMetadata":
        """Return a function metadata object parsed from an LLVM analysis JSON object.

        Args:
            function (Function): The LLVM analysis for the function.

        Returns:
            FunctionMetadata: The function metadata object parsed from an LLVM analysis object.
        """
        preconditions = []
        postconditions = []
        lines_of_function = [
            line.strip() for line in function.get_source_code().split("\n")
        ]
        for i, line in enumerate(lines_of_function):
            if line.startswith("__CPROVER_requires"):
                preconditions.append(
                    FunctionMetadata._extract_specification(i, lines_of_function)
                )
            elif line.startswith("__CPROVER_ensures"):
                postconditions.append(
                    FunctionMetadata._extract_specification(i, lines_of_function)
                )
        return FunctionMetadata(
            name=function.name,
            signature=function.signature,
            preconditions=preconditions,
            postconditions=postconditions,
        )

    @staticmethod
    def _extract_specification(i: int, lines: list[str]) -> str:
        """Extract specifications from preconditions and postconditions.

        Returns:
            list[str]: The extracted specifications.
        """
        curr_spec = ""
        open_parens = 0
        close_parens = 0
        for line in lines[i:]:
            open_parens += line.count("(")
            close_parens += line.count(")")
            curr_spec += line.strip()
            if open_parens == close_parens and open_parens > 0:
                break
        return curr_spec
