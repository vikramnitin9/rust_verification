from .llvm_util import extract_func
from dataclasses import dataclass, field
from string import Template

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
    def from_json_and_body(json, source_file: str) -> "FunctionMetadata":
        """Return a function metadata object parsed from an LLVM analysis JSON object.

        Args:
            json (_type_): The LLVM analysis JSON object.
            source_file (str): The source code file in which this method is found.

        Returns:
            FunctionMetadata: The function metadata object parsed from an LLVM analysis object.
        """
        preconditions = []
        postconditions = []
        extracted_function = extract_func(source_file, json)
        for line in [line.strip() for line in extracted_function.split("\n")]:
            if line.startswith("__CPROVER_requires"):
                preconditions.append(line)
            elif line.startswith("__CPROVER_ensures"):
                postconditions.append(line)
        return FunctionMetadata(
            name=json["name"],
            signature=json["signature"],
            preconditions=preconditions,
            postconditions=postconditions,
        )
