from dataclasses import dataclass, field
from string import Template

TEMPLATE_FOR_FUNCTION_CONTEXT_PROMPT = Template("""
Function name: $name
Function signature: $signature
Preconditions: $preconditions
Postconditions: $postconditions
""")


@dataclass
class Function:
    name: str
    signature: str
    preconditions: list[str] = field(default_factory=list)
    postconditions: list[str] = field(default_factory=list)

    def get_prompt_str(self) -> str:
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
        return len(self.preconditions) > 0 or len(self.postconditions) > 0

    @staticmethod
    def from_json_and_body(json, extracted_function: str) -> "Function":
        preconditions = []
        postconditions = []
        for line in [line.strip() for line in extracted_function.split("\n")]:
            if line.startswith("__CPROVER_requires"):
                preconditions.append(line)
            elif line.startswith("__CPROVER_ensures"):
                postconditions.append(line)
        return Function(
            name=json["name"],
            signature=json["signature"],
            preconditions=preconditions,
            postconditions=postconditions,
        )
