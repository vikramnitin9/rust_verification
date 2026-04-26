"""Represent a mutant for a C function implementation."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Mutant:
    """A mutated version of a C function implementation.

    Each mutant represents exactly one syntactic change from the original implementation (i.e., a
    first-order mutant).

    Attributes:
        source_code (str): The complete, mutated function implementation.
        operator (str): The label of the mutation operator that produced this mutant.
        line (int): The 1-indexed line number (within the function implementation) where the
            mutation was applied.
        original_expr (str): The text of the expression that was replaced.
        replacement_expr (str): The text that replaced the original.
        description (str): An English description of the applied mutation,
            including line and original and replacement_expr expressions.
    """

    source_code: str
    operator: str
    line: int
    original_expr: str
    replacement_expr: str
    description: str

    @classmethod
    def create(
        cls,
        source_code: str,
        operator: str,
        line: int,
        original_expr: str,
        replacement_expr: str,
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
            original_expr (str): The text of the expression that was replaced.
            replacement_expr (str): The text that replaced the original.

        Returns:
            Mutant: A fully populated `Mutant` instance.
        """
        verb = {
            "CRP": "replaced constant",
            "RVR": "replaced return value",
        }.get(operator, "replaced")
        description = (
            f"{operator}: {verb} '{original_expr}' with '{replacement_expr}' at line {line}"
        )
        return cls(
            source_code=source_code,
            operator=operator,
            description=description,
            line=line,
            original_expr=original_expr,
            replacement_expr=replacement_expr,
        )
