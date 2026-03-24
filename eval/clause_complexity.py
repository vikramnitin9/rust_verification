"""Module to encapsulate classes representing clause complexity."""

from dataclasses import dataclass


@dataclass(frozen=True)
class ClauseComplexity:
    """Base class for representing clause complexity.

    Attributes:
        clause (str): The clause whose complexity to represent.
    """

    clause: str


@dataclass(frozen=True)
class ClauseComplexityResult(ClauseComplexity):
    """Complexity for a clause that was successfully parsed.

    Attributes:
        num_atoms (int): The number of atoms in a clause.
        num_unique_atoms (int): The number of unique atoms in a clause.
        is_tautology (bool): True if this clause is definitely a tautology.
    """

    num_atoms: int
    num_unique_atoms: int
    is_tautology: bool


@dataclass(frozen=True)
class ClauseComplexityError(ClauseComplexity):
    """A clause that failed to parse.

    Attributes:
        error (str): The error message.
    """

    error: str
