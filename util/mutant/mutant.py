"""Represent a mutant for a C function implementation."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Mutant:
    """A mutated version of a C function implementation.

    Each mutant represents exactly one syntactic change from the original implementation (i.e., a
    first-order mutant).

    Attributes:
        source_code (str): The complete, mutated function implementation.
        operator (str): The mutation operator label that produced this mutant.
        description (str): A description of the applied mutation.
        line (int): The 1-indexed line number (within the function implementation) where the
            mutation was applied.
        original (str): The text of the expression that was replaced.
        replacement (str): The text that replaced the original.
    """

    source_code: str
    operator: str
    description: str
    line: int
    original: str
    replacement: str

    @classmethod
    def create(
        cls,
        source_code: str,
        operator: str,
        line: int,
        original: str,
        replacement: str,
    ) -> "Mutant":
        """Construct a `Mutant`, auto-generating the `description` from the other fields.

        The description verb varies by operator:

        - `CRP`: "replaced constant"
        - `RVR`: "replaced return value"
        - all others: "replaced"

        Args:
            source_code (str): The complete, mutated function implementation.
            operator (str): The label corresponding to the mutation operator that produced this
                mutant.
            line (int): The 1-indexed line number where the mutation was applied.
            original (str): The text of the expression that was replaced.
            replacement (str): The text that replaced the original.

        Returns:
            Mutant: A fully populated `Mutant` instance.
        """
        verb = {
            "CRP": "replaced constant",
            "RVR": "replaced return value",
        }.get(operator, "replaced")
        description = f"{operator}: {verb} '{original}' with '{replacement}' at line {line}"
        return cls(
            source_code=source_code,
            operator=operator,
            description=description,
            line=line,
            original=original,
            replacement=replacement,
        )
