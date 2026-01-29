"""Module for basic repair of common syntax errors observed in generated specs."""

import re
from enum import Enum

from .function_specification import FunctionSpecification


class CProverClause(str, Enum):
    """Represent CPROVER clauses."""

    REQUIRES = "__CPROVER_requires"
    ENSURES = "__CPROVER_ensures"
    ASSIGNS = "__CPROVER_assigns"


# Content inside parens.
CONTENT_INSIDE_PARENS = r"\((.+?)\)"

# E.g., arr[lo..hi], some_obj[0 ... max]
ILLEGAL_ARRAY_RANGE_PATTERN = r"([a-zA-Z_]\w*)\[.+(\.\.\.?|:).+\]"
# E.g., "...", " ..., "
ILLEGAL_ELLIPSES_PATTERN = r"(?<!\[)[,\s]*\.{3}[,\s]*(?!\])"


def fix_syntax(spec: FunctionSpecification) -> FunctionSpecification:
    """Return a fixed (i.e., syntax-corrected) FunctionSpecification.

    A fixed FunctionSpecification comprises a spec which has been modified to fix common
    syntax errors.

    For example, converts `arr[lo:hi]` (which is not valid C code) to `*arr`.

    Args:
        spec (FunctionSpecification): The specification to fix.

    Returns:
        FunctionSpecification: The fixed function specification.
    """
    return FunctionSpecification(
        preconditions=[_fix_clause(clause) for clause in spec.preconditions],
        postconditions=[_fix_clause(clause) for clause in spec.postconditions],
    )


def _fix_clause(clause: str) -> str:
    """Return a fixed clause.

    Args:
        clause (str): The clause to fix.

    Returns:
        str: The fixed clause.
    """
    match _get_clause_expression(clause):
        case (CProverClause.ASSIGNS, expr):
            expr = _remove_ellipsis(expr)
            if illegal_array_pattern := re.search(ILLEGAL_ARRAY_RANGE_PATTERN, expr):
                array_name = illegal_array_pattern.group(1)
                # TODO: What if there's a spec that has both illegal patterns?
                return f"{CProverClause.ASSIGNS.value}(*{array_name})"
            return f"{CProverClause.ASSIGNS.value}({expr})"
        case _:
            return clause


def _get_clause_expression(clause: str) -> tuple[CProverClause, str] | str:
    """Return the expression inside a CProver clause.

    Args:
        clause (str): The clause from which to extract the expression.

    Returns:
        tuple[CProverClause, str] | None: A tuple of the top-level CProver clause
            and the expression, or None if not a recognized clause.
    """
    if clause.startswith("__CPROVER_requires"):
        if match := re.search(CONTENT_INSIDE_PARENS, clause):
            return CProverClause.REQUIRES, match.group(1)
    elif clause.startswith("__CPROVER_ensures"):
        if match := re.search(CONTENT_INSIDE_PARENS, clause):
            return CProverClause.ENSURES, match.group(1)
    elif clause.startswith("__CPROVER_assigns"):
        if match := re.search(CONTENT_INSIDE_PARENS, clause):
            return CProverClause.ASSIGNS, match.group(1)
    # Here, we could have a quantifier, skip for now.
    return clause


def _is_inside_brackets(position: int, text: str) -> bool:
    """Return True iff the position is inside bracket characters in text.

    Args:
        position (int): The position to check.
        text (str): The text.

    Returns:
        bool: True iff the position is inside bracket characters in text.
    """
    depth = 0
    for i in range(position):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
    return depth > 0


def _remove_ellipsis(text: str) -> str:
    """Remove ellipsis ("...") from the given text.

    Args:
        text (str): The text from which to remove ellipsis.

    Returns:
        str: The text with ellipsis removed.
    """
    pattern = r",?\s*\.{3}\s*,?"

    # Find all matches and filter out ones inside brackets
    result = text
    offset = 0

    for match in re.finditer(pattern, text):
        if not _is_inside_brackets(match.start(), text):
            # Calculate adjusted position due to previous replacements
            adj_start = match.start() - offset
            adj_end = match.end() - offset
            result = result[:adj_start] + "," + result[adj_end:]
            offset += (match.end() - match.start()) - 1  # -1 for the comma we insert

    # Clean up
    result = re.sub(r",\s*,", ",", result)
    result = re.sub(r"\s+", " ", result)
    return result.strip(", ")
