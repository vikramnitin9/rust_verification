"""Class to aid in calculating the complexity of function specifications."""

from translation import CBMCAst
from translation.ast.cbmc_ast import NotOp, OrOp


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
        case _:
            return False
