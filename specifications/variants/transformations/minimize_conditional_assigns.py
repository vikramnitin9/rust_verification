"""Transformation where the condition in an assigns clause is minimized."""

from translation.ast.cbmc_ast import Assigns, CBMCAst, LogicalBinOp
from util import FunctionSpecification

from .specification_transformation import SpecificationTransformation


class MinimizeConditionalAssigns(SpecificationTransformation):
    """Transformation where the condition in an assigns clause is minimized."""

    def apply(self, specification: FunctionSpecification) -> list[FunctionSpecification]:
        """Return the result of applying this transformation to the given specification.

        Given a specification that has a postcondition such as:

                __CPROVER_assigns(a || b || c : result)

        Return specifications that are identical to the original, but with disjuncts removed
        one-by-one, i.e.,

                __CPROVER_assigns(a || b : result)
                __CPROVER_assigns(a : result)
                __CPROVER_assigns(result)

        Args:
            specification (FunctionSpecification): The specification to transform.

        Returns:
            list[FunctionSpecification]: The result of applying this transformation to the given
                specification.
        """
        _, postconditions = self._parse_specification(specification)
        assigns_clauses = [clause for clause in postconditions if isinstance(clause, Assigns)]

        if not assigns_clauses:
            return [specification]

        assigns_clause = assigns_clauses[0]

        # If there is no condition, nothing to minimize.
        if assigns_clause.condition is None:
            return [specification]

        preconditions = list(specification.preconditions)
        transformed_specs: list[FunctionSpecification] = []

        # Build the non-assigns postconditions (unchanged across variants).
        other_postconditions = [
            clause.to_string() for clause in postconditions if not isinstance(clause, Assigns)
        ]

        # If the condition is a LogicalBinOp, generate prefix variants.
        if isinstance(assigns_clause.condition, LogicalBinOp):
            prefixes = assigns_clause.condition.get_operand_prefixes()
            for prefix_condition in reversed(prefixes):
                new_assigns = Assigns(condition=prefix_condition, targets=assigns_clause.value)
                new_postconditions = [*other_postconditions, new_assigns.to_string()]
                transformed_specs.append(
                    FunctionSpecification(
                        preconditions=preconditions,
                        postconditions=new_postconditions,
                    )
                )

        # Always add a variant with no condition at all (just the assigns target).
        no_condition_assigns = Assigns(condition=None, targets=assigns_clause.targets)
        no_condition_postconditions = [*other_postconditions, no_condition_assigns.to_string()]
        transformed_specs.append(
            FunctionSpecification(
                preconditions=preconditions,
                postconditions=no_condition_postconditions,
            )
        )

        return transformed_specs

    def _get_operand_prefixes(self, logical_binop: LogicalBinOp) -> list[CBMCAst]:
        """Return the strict prefixes of the given logical binary operation.

        E.g., Given `a || b || c || d`, return `a`, `a || b`, `a || b || c`.

        Args:
            logical_binop (LogicalBinOp): The logical binary operation for which to return prefixes.

        Returns:
            list[CBMCAst]: The strict prefixes of the logical binary operation.
        """
        operands = logical_binop.get_operand_atoms()
        if len(operands) <= 1:
            return []
        variants: list[CBMCAst] = []
        for i in range(1, len(operands)):
            prefix = operands[:i]
            variants.append(logical_binop.apply(prefix))
        return variants
