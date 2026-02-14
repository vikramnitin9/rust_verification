"""Class for applying transformations to specifications."""

from translation.ast.cbmc_ast import AndOp, Assigns, CBMCAst, RequiresClause, ToAst
from translation.parser import Parser
from util import FunctionSpecification


class SpecTransformer:
    """Class for applying transformations to specifications.

    Attributes:
        (_parser): Parser[CBMCAst]: A parser for CBMC specifications.

    """

    _parser: Parser[CBMCAst] = Parser(
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
        conjunction_of_preconditions_exprs = self._make_conjunction_from(precondition_exprs)

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
        """TODO: Implement me.

        Args:
            spec (FunctionSpecification): _description_

        Raises:
            NotImplementedError: _description_

        Returns:
            FunctionSpecification: _description_
        """
        raise NotImplementedError("TODO")

    def _get_assigns_clauses(self, spec: FunctionSpecification) -> list[Assigns]:
        """Return the Assigns clauses in a specification.

        Args:
            spec (FunctionSpecification): The specification.

        Returns:
            list[Assigns]: The Assigns clauses in a specification.
        """
        parsed_postconditions = [self._parser.parse(clause) for clause in spec.postconditions]
        return [clause for clause in parsed_postconditions if isinstance(clause, Assigns)]

    def _make_conjunction_from(self, exprs: list[CBMCAst]) -> CBMCAst:
        """Return a conjunction (i.e., an AndOp) comprising the given expressions.

        Args:
            exprs (list[CBMCAst]): The expressions to construct a conjunction from.

        Returns:
            CBMCAst: The conjunction.
        """
        if len(exprs) == 1:
            return exprs[0]
        conjunction = AndOp(left=exprs.pop(), right=exprs.pop())
        andop = conjunction
        while exprs:
            andop = AndOp(left=exprs.pop(), right=andop)
        return andop
