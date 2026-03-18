"""Class to aid in calculating the complexity of function specifications."""

from dataclasses import dataclass

from lark.exceptions import UnexpectedToken, VisitError

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
    """Base class for clause complexity results."""

    clause: str


@dataclass(frozen=True)
class ClauseComplexity(ClauseComplexityInfo):
    """Complexity info for a clause that was successfully parsed.

    Attributes:
        clause (str): The original clause string.
        num_atoms (int): The number of atoms in a clause.
        num_unique_atoms (int): The number of unique atoms in a clause.
        is_tautology (bool): True iff this clause is definitely a tautology.
    """

    num_atoms: int
    num_unique_atoms: int
    is_tautology: bool


@dataclass(frozen=True)
class ClauseComplexityError(ClauseComplexityInfo):
    """Represents a clause that failed to parse.

    Attributes:
        clause (str): The original clause string.
        error (str): The error message from the failed parse.
    """

    error: str


def get_complexity(clause: str) -> ClauseComplexityInfo:
    """Return the clause complexity info for a given CBMC clause.

    Args:
        clause (str): A requires, ensures, or assigns clause for which to compute complexity
            information.

    Returns:
        ClauseComplexityInfo: A ClauseComplexity on success, or ClauseComplexityError on failure.
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


def _get_complexity_from_expression(clause: str, expr: CBMCAst | None) -> ClauseComplexity:
    """Return the clause complexity calculated from the expression from the given clause.

    Args:
        clause (str): The clause from which the expression originates.
        expr (CBMCAst | None): The expression from the clause.

    Returns:
        ClauseComplexity: The clause complexity calculated from the given expression.
    """
    if not expr:
        return ClauseComplexity(clause=clause, num_atoms=0, num_unique_atoms=0, is_tautology=False)
    atoms = get_atoms_in_expression(expr)
    # Cannot use `set(atoms)` because the CBMCAst class is not hashable.
    unique_atoms = [atom for i, atom in enumerate(atoms) if atom not in atoms[:i]]
    return ClauseComplexity(
        clause=clause,
        num_atoms=len(atoms),
        num_unique_atoms=len(unique_atoms),
        is_tautology=is_tautology(expr),
    )


def get_atoms_in_expression(expr: CBMCAst) -> list[CBMCAst]:
    """Return the atoms comprising the given expression.

    Atoms comprise boolean propositions without top-level logical operators.

    Args:
        expr (CBMCAst): The expression from which to obtain atoms.

    Returns:
        list[CBMCAst]: The atoms comprising the given expression.
    """
    result: list[CBMCAst] = []
    match expr:
        case AndOp(left=left, right=right) | OrOp(left=left, right=right):
            result = [*result, *get_atoms_in_expression(left), *get_atoms_in_expression(right)]
        case NotOp(e):
            result = [*result, *get_atoms_in_expression(e)]
        case Quantifier(expr=body_expr):
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
    except VisitError as ve:
        msg = f"Failed to parse a CBMC AST from '{cbmc_str}'"
        raise ValueError(msg) from ve
