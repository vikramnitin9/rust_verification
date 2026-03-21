"""Class to aid in calculating the size of function specifications."""

from lark.exceptions import UnexpectedInput

from translation import CbmcAst, Parser
from translation.ast.cbmc_ast import (
    AndOp,
    Assigns,
    Bool,
    EnsuresClause,
    NotOp,
    OrOp,
    Quantifier,
    RequiresClause,
    ToAst,
)

from .clause_complexity import ClauseComplexity, ClauseComplexityError, ClauseComplexityResult

CBMC_PARSER: Parser[CbmcAst] = Parser(
    path_to_grammar_defn="translation/grammar/cbmc.txt", start="cbmc_clause", transformer=ToAst()
)


def get_complexity(clause: str) -> ClauseComplexity:
    """Return the clause complexity for a given CBMC clause.

    Args:
        clause (str): A requires, ensures, or assigns clause for which to compute complexity
            information.

    Returns:
        ClauseComplexity: A ClauseComplexity on success, or ClauseComplexityError on failure.
    """
    try:
        ast = _parse_to_ast(clause)
    except ValueError as ve:
        return ClauseComplexityError(clause=clause, error=str(ve))

    match ast:
        case (
            RequiresClause(_, expr_ast)
            | EnsuresClause(_, expr_ast)
            | Assigns(condition=expr_ast, targets=_)
        ):
            return _get_complexity_from_expression(clause, expr_ast)
        case _:
            return ClauseComplexityError(
                clause=clause,
                error=f"Cannot compute complexity for unexpected clause '{clause}'",
            )


def _get_complexity_from_expression(clause: str, expr: CbmcAst | None) -> ClauseComplexityResult:
    """Return the clause complexity calculated from the expression from the given clause.

    Args:
        clause (str): The clause from which the expression originates.
        expr (CbmcAst | None): The expression from the clause.

    Returns:
        ClauseComplexityResult: The clause complexity calculated from the given expression.
    """
    if not expr:
        return ClauseComplexityResult(
            clause=clause, num_atoms=0, num_unique_atoms=0, is_tautology=False
        )
    atoms = get_atoms_in_expression(expr)
    # Cannot use `set(atoms)` because the CbmcAst class is not hashable.
    unique_atoms = []
    for atom in atoms:
        if atom not in unique_atoms:
            unique_atoms.append(atom)
    return ClauseComplexityResult(
        clause=clause,
        num_atoms=len(atoms),
        num_unique_atoms=len(unique_atoms),
        is_tautology=simplify(expr) == Bool(True),
    )


def get_atoms_in_expression(expr: CbmcAst) -> list[CbmcAst]:
    """Return the atoms comprising the given expression.

    Atoms comprise boolean propositions without top-level logical operators.

    Args:
        expr (CbmcAst): The expression from which to obtain atoms.

    Returns:
        list[CbmcAst]: The atoms comprising the given expression.
    """
    match expr:
        case AndOp(left=left, right=right) | OrOp(left=left, right=right):
            return [*get_atoms_in_expression(left), *get_atoms_in_expression(right)]
        case NotOp(e):
            return get_atoms_in_expression(e)
        case Quantifier(expr=body_expr):
            return get_atoms_in_expression(body_expr)
        case e:
            return [e]


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
    match not_op:
        case NotOp(NotOp(op)):
            return simplify(op)
        case NotOp(operand):
            simplified_operand = simplify(operand)
            match simplified_operand:
                case Bool(v):
                    return Bool(not v)
                case _:
                    return (
                        NotOp(simplified_operand)
                        if simplified_operand == operand
                        else simplify(NotOp(simplified_operand))
                    )


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
        case _:
            return and_op


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
        case _:
            return or_op


def _are_complements(lhs: CbmcAst, rhs: CbmcAst) -> bool:
    """Return True iff lhs and rhs are boolean complements (lhs == !rhs or !lhs == rhs).

    Arguments:
        lhs (CbmcAst): The left-hand side of a logical expression.
        rhs (CbmcAst): The right-hand side of a logical expression.

    Returns:
        bool: True iff the lhs and rhs are boolean complements.
    """
    return lhs == NotOp(rhs) or NotOp(lhs) == rhs


def _parse_to_ast(cbmc_str: str) -> CbmcAst:
    """Return a CBMC AST parsed from a string.

    Args:
        cbmc_str (str): The string from which to parse an AST.

    Returns:
        CbmcAst: The AST parsed from the given string.
    """
    try:
        return CBMC_PARSER.parse(cbmc_str)
    except UnexpectedInput as uie:
        msg = f"Failed to parse a CBMC AST from '{cbmc_str}'"
        raise ValueError(msg) from uie
