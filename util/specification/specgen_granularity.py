"""Module defining the granularity at which specification generation may occur."""

from enum import Enum


class SpecGenGranularity(str, Enum):
    """Define the granularity at which specification generation may occur.

    CLAUSE-level granularity results in an LLM being prompted to generate a list of possible clauses
    that comprise CBMC pre/postconditions.

    EXPRESSION-level granularity results in an LLM being prompted to generate a list of possible
    expressions that can be input to `__CPROVER` clauses.


    """

    CLAUSE = "CLAUSE"
    EXPRESSION = "EXPRESSION"
