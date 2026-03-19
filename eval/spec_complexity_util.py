"""Class to aid in calculating the complexity of function specifications."""

from lark.exceptions import UnexpectedToken, VisitError

from translation import CbmcAst, Parser
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

from .clause_complexity import ClauseComplexity, ClauseComplexityError, ClauseComplexityResult

CBMC_PARSER: Parser[CbmcAst] = Parser(
    path_to_grammar_defn="translation/grammar/cbmc.txt", start="cbmc_clause", transformer=ToAst()
)


def get_complexity(clause: str) -> ClauseComplexity:
    """Return the clause complexity info for a given CBMC clause.

    Args:
        clause (str): A requires, ensures, or assigns clause for which to compute complexity
            information.

    Returns:
        ClauseComplexity: A ClauseComplexity on success, or ClauseComplexityError on failure.
    """
    try:
        ast = _parse_to_ast(clause)
    except ValueError as e:
        return ClauseComplexityError(clause=clause, error=str(e))

    match ast:
        case RequiresClause(_, e) | EnsuresClause(_, e) | Assigns(condition=e, targets=_):
            return _get_complexity_from_expression(clause, e)
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
        is_tautology=is_tautology(expr),
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


def is_tautology(node: CbmcAst) -> bool:
    """Return True if the given node is a tautology.

    Args:
        node (CbmcAst): The node to check for a tautology.

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


def _parse_to_ast(cbmc_str: str) -> CbmcAst:
    """Return a CBMC AST parsed from a string.

    Args:
        cbmc_str (str): The string from which to parse an AST.

    Returns:
        CbmcAst: The AST parsed from the given string.
    """
    try:
        return CBMC_PARSER.parse(cbmc_str)
    except UnexpectedToken as ute:
        msg = f"Failed to parse a CBMC AST from '{cbmc_str}'"
        raise ValueError(msg) from ute
    except VisitError as ve:
        msg = f"Failed to parse a CBMC AST from '{cbmc_str}'"
        raise ValueError(msg) from ve
