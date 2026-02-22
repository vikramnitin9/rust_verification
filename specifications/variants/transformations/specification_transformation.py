"""Represent a transformation of a specification."""

from abc import ABC, abstractmethod

from translation.ast.cbmc_ast import (
    CBMCAst,
)
from translation.parser import Parser
from util import FunctionSpecification


class SpecificationTransformation(ABC):
    """Represent a transformation of a specification.

    Attributes:
        parser (Parser[CBMCAst]): A parser for CBMC ASTs.
    """

    _parser: Parser[CBMCAst]

    @abstractmethod
    def apply(self, specification: FunctionSpecification) -> list[FunctionSpecification]:
        """Return the result(s) of applying this transformation to the given specification.

        Args:
            specification (FunctionSpecification): The specification to which to apply this
                transformation

        Returns:
            list[FunctionSpecification]: The result(s) of applying this specification to the given
                specification.
        """
        ...

    def _parse_specification(
        self, specification: FunctionSpecification
    ) -> tuple[list[CBMCAst], list[CBMCAst]]:
        """Return the given specification's pre and postcondition(s) as CBMC ASTs.

        Args:
            specification (FunctionSpecification): The specification to parse.

        Returns:
            tuple[list[CBMCAst], list[CBMCAst]]: The parsed pre and postcondition(s) of the given
                specification.
        """
        return (
            [self._parser.parse(clause) for clause in specification.preconditions],
            [self._parser.parse(clause) for clause in specification.postconditions],
        )
