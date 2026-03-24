"""Class to aid in calculating the size of function specifications."""

from lark.exceptions import UnexpectedInput

from specifications import simplify
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

    An atom is a boolean proposition without top-level logical operators.

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
