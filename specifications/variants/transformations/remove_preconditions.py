"""Transformation where preconditions are removed, one-by-one."""

from translation.ast.cbmc_ast import (
    ToAst,
)
from translation.parser import Parser
from util import FunctionSpecification

from .specification_transformation import SpecificationTransformation


class RemovePreconditions(SpecificationTransformation):
    """Transformation where precondition expressions are removed one-by-one."""

    def __init__(self) -> None:
        """Create a new RemovePreconditions."""
        self._parser = Parser(
            path_to_grammar_defn="translation/grammar/cbmc.txt",
            start="cbmc_clause",
            transformer=ToAst(),
        )

    def apply(self, specification: FunctionSpecification) -> list[FunctionSpecification]:
        """Return the result of applying this transformation to the given specification.

        Remove the precondition(s) of this specification, one-by-one.

        For example, given a spec with preconditions [p0, p1], this function returns specs
        that have preconditions:
            * [p0]       (p1 removed)
            * [p1]       (p0 removed)
            * []         (all removed)
        While leaving the postconditions unchanged.

        Args:
            specification (FunctionSpecification): The specification to transform.

        Returns:
            list[FunctionSpecification]: The result of applying this transformation to the given
                specification.
        """
        precondition_asts, _ = self._parse_specification(specification)

        if not precondition_asts:
            return [specification]

        postconditions = list(specification.postconditions)
        transformed_specs: list[FunctionSpecification] = []

        # Generate a variant for each precondition removed individually, starting from the last.
        # Starting from the last is done because preconditions are generally order-dependent
        # (i.e., facts assumed in a prior postcondition may be used in the next).
        for i in reversed(range(len(precondition_asts))):
            preconditions_to_keep = [
                ast.to_string() for j, ast in enumerate(precondition_asts) if j != i
            ]
            transformed_specs.append(
                FunctionSpecification(
                    preconditions=preconditions_to_keep,
                    postconditions=postconditions,
                )
            )

        # Generate a variant with all preconditions removed (if not already covered).
        if len(precondition_asts) > 1:
            transformed_specs.append(
                FunctionSpecification(
                    preconditions=[],
                    postconditions=postconditions,
                )
            )

        return transformed_specs
