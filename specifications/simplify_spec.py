"""Contains utility functions for simplifying boolean CBMC expressions."""

from translation.ast.cbmc_ast import AndOp, Bool, CbmcAst, NotOp, OrOp


def simplify(node: CbmcAst) -> CbmcAst:
    """Return the given node after applying boolean algebra rules bottom-up.

    Applies the following boolean algebra rules bottom-up: identity, annihilation, idempotence,
    complement, and double negation.

    Args:
        node (CbmcAst): The node to simplify.

    Returns:
        CbmcAst: The simplified version of the given AST node.
    """
    match node:
        case NotOp():
            return _simplify_negation(node)
        case AndOp():
            return _simplify_conjunction(node)
        case OrOp():
            return _simplify_disjunction(node)
        case _:
            return node


def _simplify_negation(not_op: NotOp) -> CbmcAst:
    """Return the simplified form of a negation node.

    E.g., !!a -> a, !true -> false, !false -> true.

    Args:
        not_op (NotOp): The negation node to simplify.

    Returns:
        CbmcAst: The simplified form of a negation node.
    """
    match simplify(not_op.operand):
        case NotOp(op):
            return op
        case Bool(v):
            return Bool(not v)
        case simplified_operand:
            return NotOp(simplified_operand)


def _simplify_conjunction(and_op: AndOp) -> CbmcAst:
    """Return the simplified form of a conjunction node.

    This applies conjunction-specific boolean algebra after recursively simplifying both
    operands:
    - Annihilation: a && false -> false
    - Identity: a && true -> a
    - Idempotence: a && a -> a
    - Complement: a && !a -> false

    Args:
        and_op (AndOp): The conjunction node to simplify.

    Returns:
        CbmcAst: The simplified conjunction.
    """
    match (simplify(and_op.left), simplify(and_op.right)):
        case (Bool(False), _) | (_, Bool(False)):
            return Bool(False)
        case (Bool(True), simplified_right):
            return simplified_right
        case (simplified_left, Bool(True)):
            return simplified_left
        case (simplified_left, simplified_right):
            if simplified_left == simplified_right:
                return simplified_left
            if _are_complements(simplified_left, simplified_right):
                return Bool(False)
            return AndOp(simplified_left, simplified_right)
        case unreachable:
            msg = f"Unreachable case in simplifying a conjunction: {unreachable}"
            raise ValueError(msg)


def _simplify_disjunction(or_op: OrOp) -> CbmcAst:
    """Return the simplified form of a disjunction node.

    This applies disjunction-specific boolean algebra after recursively simplifying both
    operands:
    - Annihilation: a || true -> true
    - Identity: a || false -> a
    - Idempotence: a || a -> a
    - Complement: a || !a -> true

    Args:
        or_op (OrOp): The disjunction node to simplify.

    Returns:
        CbmcAst: The simplified disjunction.
    """
    match (simplify(or_op.left), simplify(or_op.right)):
        case (Bool(True), _) | (_, Bool(True)):
            return Bool(True)
        case (Bool(False), simplified_right):
            return simplified_right
        case (simplified_left, Bool(False)):
            return simplified_left
        case (simplified_left, simplified_right):
            if simplified_left == simplified_right:
                return simplified_left
            if _are_complements(simplified_left, simplified_right):
                return Bool(True)
            return OrOp(simplified_left, simplified_right)
        case unreachable:
            msg = f"Unreachable case in simplifying a disjunction: {unreachable}"
            raise ValueError(msg)


def _are_complements(lhs: CbmcAst, rhs: CbmcAst) -> bool:
    """Return True iff lhs and rhs are boolean complements.

    The test is syntactic.  This function returns true if lhs == !rhs or !lhs == rhs.

    Arguments:
        lhs (CbmcAst): A logical expression.
        rhs (CbmcAst): A logical expression.

    Returns:
        bool: True iff `lhs` and `rhs` are boolean complements.
    """
    match (lhs, rhs):
        case (NotOp(operand), other) | (other, NotOp(operand)):
            return other == operand
        case _:
            return False
