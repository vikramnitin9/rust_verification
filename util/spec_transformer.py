"""Class for applying transformations to specifications."""

from translation.ast.cbmc_ast import (
    AndOp,
    Assigns,
    CBMCAst,
    EnsuresClause,
    OrOp,
    RequiresClause,
    ToAst,
)
from translation.parser import Parser
from util import FunctionSpecification


class SpecTransformer:
    """Class for applying transformations to specifications.

    Attributes:
        (_parser): Parser[CBMCAst]: A parser for CBMC specifications.

    """

    _parser: Parser[CBMCAst]

    def __init__(self) -> None:
        """Create a new SpecTransformer."""
        self._parser = Parser(
            path_to_grammar_defn="translation/grammar/cbmc.txt",
            start="cbmc_clause",
            transformer=ToAst(),
        )

    def move_preconditions_to_assigns(self, spec: FunctionSpecification) -> FunctionSpecification:
        """Return a spec where precondition expressions are moved to conditions for assigns clauses.

        There are cases where a specification might contain preconditions that are *too* strong,
        effectively weakening the entire specification. Below is one example:

            ```c
            void f1(struct pair_of_pairs *pp)
            __CPROVER_requires(pp != NULL)
            __CPROVER_requires(pp->p != NULL)
            __CPROVER_requires(pp->p->buf != NULL)
            __CPROVER_ensures(pp->p->buf[0] == 0)
            __CPROVER_assigns(pp->p->buf[0])
            {
                if(pp && pp->p && pp->p->buf)
                    pp->p->buf[0] = 0;
            }
            ```

        It is the case that `f1` might be called with a NULL `pp` (or `pp->p` or `pp->p->buf`), and
        the function accounts for this with a conditional check. A more expressive and accurate
        specification would be:

            __CPROVER_ensures(pp->p->buf[0] == 0)
            __CPROVER_assigns(
                pp != NULL && pp->p != NULL && pp->p->buf != NULL : pp->p->buf[0]
            )

        Where each expression in a precondition is provided as a condition for the assignment
        `pp->p->buf[0]`.

        Args:
            spec (FunctionSpecification): The specification.

        Returns:
            FunctionSpecification: The specification, where each precondition expression is moved
                to a condition for assignment clauses.
        """
        if not spec.preconditions:
            return spec

        preconditions = [self._parser.parse(clause) for clause in spec.preconditions]
        postconditions = [self._parser.parse(clause) for clause in spec.postconditions]
        precondition_exprs = [
            clause.expr for clause in preconditions if isinstance(clause, RequiresClause)
        ]
        conjunction_of_preconditions_exprs = self._apply_logical_op(precondition_exprs, AndOp)

        updated_postconditions = []
        is_assigns_clause_updated = False
        for clause in postconditions:
            if isinstance(clause, Assigns):
                clause.condition = conjunction_of_preconditions_exprs
                is_assigns_clause_updated = True
            updated_postconditions.append(clause.to_string())

        return (
            FunctionSpecification(preconditions=[], postconditions=updated_postconditions)
            if is_assigns_clause_updated
            else spec
        )

    def move_preconditions_to_ensures(self, spec: FunctionSpecification) -> FunctionSpecification:
        """Return a spec where precondition exprs are moved to disjunctions for ensures clauses.

        There are cases where a specification might contain preconditions that are *too* strong,
        effectively weakening the entire specification. Below is one example:

            ```c
            void f1(struct pair_of_pairs *pp)
            __CPROVER_requires(pp != NULL)
            __CPROVER_requires(pp->p != NULL)
            __CPROVER_requires(pp->p->buf != NULL)
            __CPROVER_ensures(pp->p->buf[0] == 0)
            {
                if(pp && pp->p && pp->p->buf)
                    pp->p->buf[0] = 0;
            }
            ```

        Function `f1` might be called with a NULL `pp` (or `pp->p` or `pp->p->buf`), and
        the function accounts for this with a conditional check. A more expressive spec is:

            __CPROVER_ensures(
                pp == NULL || pp->p == NULL || pp->p->buf == NULL || pp->p->buf[0] == 0
            )

        Args:
            spec (FunctionSpecification): The specification.

        Returns:
            FunctionSpecification: The specification, where each precondition expression is moved
                to a disjunction in ensures clauses.
        """
        if not spec.preconditions:
            return spec

        preconditions = [self._parser.parse(clause) for clause in spec.preconditions]
        postconditions = [self._parser.parse(clause) for clause in spec.postconditions]
        negated_precondition_exprs = [
            clause.expr.negate() for clause in preconditions if isinstance(clause, RequiresClause)
        ]
        disjunction_of_negated_precondition_exprs = self._apply_logical_op(
            negated_precondition_exprs, OrOp
        )

        updated_postconditions = []
        is_ensures_clause_updated = False
        for clause in postconditions:
            if isinstance(clause, EnsuresClause):
                updated_ensures_expr = self._apply_logical_op(
                    [disjunction_of_negated_precondition_exprs, clause.expr], OrOp
                )
                clause.expr = updated_ensures_expr
                is_ensures_clause_updated = True
            updated_postconditions.append(clause.to_string())

        return (
            FunctionSpecification(preconditions=[], postconditions=updated_postconditions)
            if is_ensures_clause_updated
            else spec
        )

    def _apply_logical_op(self, exprs: list[CBMCAst], logical_op: type[AndOp | OrOp]) -> CBMCAst:
        """Return the result of applying a logical operation between each expr.

        Args:
            exprs (list[CBMCAst]): The exprs to which to apply the logical operation.
            logical_op (type[AndOp | OrOp]): The logical operation.

        Returns:
            CBMCAst: The result of applying the logical operation.
        """
        if not exprs:
            msg = f"{logical_op} cannot be applied to an empty list of expressions"
            raise ValueError(msg)
        result = exprs[0]
        for expr in exprs[1:]:
            result = logical_op(left=result, right=expr)
        return result
