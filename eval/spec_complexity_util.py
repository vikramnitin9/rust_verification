"""Class to aid in calculating the complexity of function specifications."""

from dataclasses import dataclass

from lark.exceptions import UnexpectedToken

from translation import CBMCAst, Parser
from translation.ast.cbmc_ast import (
    AndOp,
    Assigns,
    EnsuresClause,
    NotOp,
    OrOp,
    Quantifier,
    RequiresClause,
    ToAst,
)

CBMC_PARSER: Parser[CBMCAst] = Parser(
    path_to_grammar_defn="translation/grammar/cbmc.txt", start="cbmc_clause", transformer=ToAst()
)


@dataclass(frozen=True)
class ClauseComplexityInfo:
    """Encapsulate values used as proxies for the complexity of a clause.

    Attributes:
        num_atoms (int): The number of atoms in a clause.
        is_tautology (bool): True iff this clause is definitely a tautology.
    """

    num_atoms: int
    num_unique_atoms: int
    is_tautology: bool


def get_complexity(clause: str) -> ClauseComplexityInfo:
    """Return the clause complexity info for a given CBMC clause.

    The given clause must be one of a requires, ensures, or assigns clause.

    Args:
        clause (str): The clause for which to compute complexity information.

    Returns:
        ClauseComplexityInfo: The complexity information parsed from a clause.
    """
    match _parse_to_ast(clause):
        case RequiresClause(_, e) | EnsuresClause(_, e) | Assigns(conditions=e, targets=_):
            atoms = get_atoms_in_expression(e)
            return ClauseComplexityInfo(
                num_atoms=len(atoms), num_unique_atoms=len(set(atoms)), is_tautology=is_tautology(e)
            )
        case _:
            msg = f"Cannot compute complexity for unexpected clause '{clause}'"
            raise ValueError(msg)


def get_atoms_in_expression(expr: CBMCAst) -> list[CBMCAst]:
    """Return the atoms comprising the given expression.

    Args:
        expr (CBMCAst): The expression from which to obtain atoms.

    Returns:
        list[CBMCAst]: The atoms comprising the given expression.
    """
    result = []
    match expr:
        case AndOp(left=left, right=right) | OrOp(left=left, right=right):
            result = [*result, *get_atoms_in_expression(left), *get_atoms_in_expression(right)]
        case NotOp(e):
            result = [*result, *get_atoms_in_expression(e)]
        case Quantifier(_, _, body_expr, _):
            result = [*result, *get_atoms_in_expression(body_expr)]
        case e:
            result.append(e)
    return result


def is_tautology(node: CBMCAst) -> bool:
    """Return True if the given node is a tautology.

    Args:
        node (CBMCAst): The node to check for a tautology.

    Returns:
        bool: True iff the node is a tautology.
    """
    match node:
        case OrOp(NotOp(a), b) if a == b:
            return True
        case OrOp(a, NotOp(b)) if a == b:
            return True
        case NotOp(AndOp(a, NotOp(b))) if a == b:
            # Equivalent to !(a && !a) -> !a || a
            return True
        case NotOp(AndOp(NotOp(a), b)) if a == b:
            # Equivalent to !(!a && a) -> a || !a
            return True
        case _:
            return False


def _parse_to_ast(cbmc_str: str) -> CBMCAst:
    """Return a CBMC AST parsed from a string.

    Args:
        cbmc_str (str): The string from which to parse an AST.

    Returns:
        CBMCAst: The AST parsed from the given string.
    """
    try:
        return CBMC_PARSER.parse(cbmc_str)
    except UnexpectedToken as ute:
        msg = f"Failed to parse a CBMC AST from '{cbmc_str}'"
        raise ValueError(msg) from ute
