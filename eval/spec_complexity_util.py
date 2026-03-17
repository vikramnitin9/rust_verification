"""Class to aid in calculating the complexity of function specifications."""

from lark.exceptions import UnexpectedToken

from translation import CBMCAst, Parser
from translation.ast.cbmc_ast import (
    AndOp,
    EnsuresClause,
    EqOp,
    NotOp,
    OrOp,
    Quantifier,
    RequiresClause,
    ToAst,
)

CBMC_PARSER: Parser[CBMCAst] = Parser(
    path_to_grammar_defn="translation/grammar/cbmc.txt", start="cbmc_clause", transformer=ToAst()
)


def count_atoms_in_clause(clause: str) -> int:
    """Return the number of atoms in a CBMC clause.

    An atom is a leaf boolean expression. For example, the expression 'a < b' comprises one atom,
    and the expression 'a < b || c >= d' comprises two,

    Args:
        clause (str): The clause in which to count atoms.

    Returns:
        int: The number of atoms in the clause.
    """

    def _count_atoms_in_ast(node: CBMCAst) -> int:
        """Return the number of atoms in a CBMC AST.

        Atoms are leaf boolean expressions.

        Args:
            node (CBMCAst): The node in which to count the number of atoms.

        Returns:
            int: The number of atoms in a CBMC AST.
        """
        match node:
            case (
                AndOp(left=left, right=right)
                | OrOp(left=left, right=right)
                | EqOp(left=left, right=right)
            ):
                return _count_atoms_in_ast(left) + _count_atoms_in_ast(right)
            case Quantifier(_, _, body_expr, _):
                return _count_atoms_in_ast(body_expr)
            case _:
                return 1

    match _parse_to_ast(clause):
        case RequiresClause(expr=e) | EnsuresClause(expr=e):
            return _count_atoms_in_ast(e)
        case _:
            msg = f"Unexpected AST parsed from clause: {clause}"
            raise ValueError(msg)


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
