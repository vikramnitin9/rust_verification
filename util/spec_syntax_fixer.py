"""Module for fixing  syntax errors in specs."""

import re
from enum import Enum

from .function_specification import FunctionSpecification


class CProverClause(str, Enum):
    """Represent CPROVER clauses."""

    REQUIRES = "__CPROVER_requires"
    ENSURES = "__CPROVER_ensures"
    ASSIGNS = "__CPROVER_assigns"


# Content inside parens.
PARENTHESIZED_CONTENT = r"\((.+?)\)"

# Below are illegal syntax patterns that should be fixed.

# E.g., arr[lo..hi], some_obj[0 ... max]
ILLEGAL_ARRAY_RANGE_PATTERN = r"([a-zA-Z_]\w*)\[.+(\.\.\.?|:).+\]"
# E.g., "...", " ..., "
ILLEGAL_ELLIPSES_PATTERN = r"(?<!\[)[,\s]*\.\.\.?[,\s]*(?!\])"


def fix_syntax(spec: FunctionSpecification) -> FunctionSpecification:
    """Fix syntax errors in the given FunctionSpecification.

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
    if clause.startswith(CProverClause.ASSIGNS.value):
        if match := re.search(PARENTHESIZED_CONTENT, clause):
            return _fix_expr_in_assigns_clause(match.group(1))
        msg = f"Malformed {CProverClause.ASSIGNS.value} clause: {clause}"
        raise ValueError(msg)
    # We do not fix other clauses, for now.
    return clause


def _fix_expr_in_assigns_clause(assigns_expr: str) -> str:
    """Return the fixed version of an expression in a `__CPROVER_assigns` clause.

    Args:
        assigns_expr (str): The expression to fix.

    Returns:
        str: The fixed version of an expression.
    """
    expr = _remove_ellipsis_outside_brackets(assigns_expr)
    if illegal_array_pattern := re.search(ILLEGAL_ARRAY_RANGE_PATTERN, expr):
        array_name = illegal_array_pattern.group(1)
        # TODO: What if there's a spec that has both illegal patterns?
        expr = f"*{array_name}"
    return f"{CProverClause.ASSIGNS.value}({expr})"


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


def _remove_ellipsis_outside_brackets(text: str) -> str:
    """Remove ellipsis ("...") from the given text if it appears outside brackets ("[]").

    For example, the text `arr[1...2]` is not modified, since the ellipses appear inside brackets.
    This is an illegal syntax pattern for array ranges that is handled in
    `_fix_expr_in_assigns_clause`.

    Args:
        text (str): The text from which to remove ellipsis, if it appears outside brackets ("[]").

    Returns:
        str: The text with ellipsis removed.
    """
    # Find all matches, only retain the ones that appear outside of brackets.
    # For example, `arr[1...2]` would not be retained, since that is an illegal array range
    # pattern that is handled elsewhere.
    result = text
    offset = 0

    # Replace "..." by ", ".  Searches in `text` but makes changes in `result`.
    for match in re.finditer(ILLEGAL_ELLIPSES_PATTERN, text):
        if not _is_inside_brackets(match.start(), text):
            # Calculate adjusted position due to previous replacements
            adj_start = match.start() - offset
            adj_end = match.end() - offset
            result = result[:adj_start] + ", " + result[adj_end:]
            offset += (match.end() - match.start()) - 1  # -1 for the comma we insert.

    # Clean up
    if result != text:
        result = re.sub(r",\s*,", ",", result)
        result = re.sub(r"\s+", " ", result)
        result = result.strip(", ")
    return result
