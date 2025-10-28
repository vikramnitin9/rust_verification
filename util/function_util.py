"""Utility methods for working with CBMC specifications."""

from .specifications import Specifications

PRECONDITION_PREFIX = "__CPROVER_requires"
POSTCONDITION_PREFIX = "__CPROVER_ensures"


def extract_specifications(function_lines: list[str]) -> Specifications:
    """Extract the lines of a function that map to a CBMC specification.

    Args:
        function_lines (list[str]): The lines of a function that map to a CBMC specification.

    Returns:
        Specifications: The specifications parsed from the lines of a C function.
    """
    stripped_lines = [line.strip() for line in function_lines]
    preconditions = []
    postconditions = []
    for i, line in enumerate(stripped_lines):
        # TODO: I think just cascaded `if` would be clearer here.
        match line:
            case _ if line.startswith(PRECONDITION_PREFIX):
                preconditions.append(_get_spec_lines(i, stripped_lines))
            case _ if line.startswith(POSTCONDITION_PREFIX):
                postconditions.append(_get_spec_lines(i, stripped_lines))
            case _:
                # TODO: Support other specifications, if necessary.
                continue
    return Specifications(
        preconditions=preconditions,
        postconditions=postconditions,
    )


def _get_spec_lines(i: int, lines: list[str]) -> str:
    """Extract specifications from the lines of a function.

    Args:
        i (int): The starting index of the specification in lines.
        lines (list[str]): The lines of the function source code.

    Returns:
        str: The extracted specification.
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
