"""Utility for performing mutation testing on C functions."""

import tree_sitter_c as tsc
from tree_sitter import Language, Parser, Tree

from util.c_function import CFunction
from util.mutant.mutant import Mutant

from .mutation_operator import (
    ArithmeticOperatorReplacement,
    ConstantReplacement,
    LogicalConnectorReplacement,
    RelationalOperatorReplacement,
    ReturnValueReplacement,
)

_C_LANGUAGE = Language(tsc.language())


class CMutator:
    """Generates first-order mutants of a C function for mutation testing.

    Uses tree-sitter to parse C source and applies mutation operators to produce first-order
    mutants.

    Attributes:
        _c_function (CFunction): The C function to mutate.
        _parser (Parser): The tree-sitter parser to parse the C function.
        _source_code (str): The source code of the C function as a string.
        _source_bytes (bytes): The source code of the C function as bytes.
        _tree (Tree): The tree-sitter Tree parsed from the C function source code.
    """

    _c_function: CFunction
    _parser: Parser
    _source_code: str
    _source_bytes: bytes
    _tree: Tree

    def __init__(self, c_function: CFunction) -> None:
        """Create a new CMutator.

        This function's source code is taken from `c_function.source_code` when
        it has been set (via `CFunction.set_source_code`); otherwise it is read
        from the original file via `CFunction.get_original_source_code()`.

        Args:
            c_function (CFunction): The C function to mutate.
        """
        self._c_function = c_function
        self._parser = Parser(_C_LANGUAGE)

        source = c_function.get_source_code()
        self._source_code = source
        self._source_bytes = source.encode("utf-8")
        self._tree = self._parser.parse(self._source_bytes)

    def get_source_code(self) -> str:
        """Return the source code being mutated.

        Returns:
            str: The source code being mutated.
        """
        return self._source_code

    def get_mutants(self) -> list[Mutant]:
        """Return all first-order mutants of this function.

        Mutants are produced by applying each enabled mutation operator. Order does not matter.

        Returns:
            list[Mutant]: Every generated mutant, one per mutation site and
                replacement candidate.
        """
        return [
            *self._apply_rvr(),
            *self._apply_ror(),
            *self._apply_aor(),
            *self._apply_crp(),
            *self._apply_lcr(),
        ]

    def _apply_aor(self) -> list[Mutant]:
        """Apply Arithmetic Operator Replacement (AOR) mutations.

        Finds all binary arithmetic operators in the source and replaces each
        with every other operator in its replacement set.

        Returns:
            list[Mutant]: All AOR mutants.
        """
        return ArithmeticOperatorReplacement().apply(self._tree, self._source_bytes)

    def _apply_ror(self) -> list[Mutant]:
        """Apply Relational Operator Replacement (ROR) mutations.

        Finds all relational operators in the source and replaces each with
        every other operator in its replacement set.

        Returns:
            list[Mutant]: All ROR mutants.
        """
        return RelationalOperatorReplacement().apply(self._tree, self._source_bytes)

    def _apply_lcr(self) -> list[Mutant]:
        """Apply Logical Connector Replacement (LCR) mutations.

        Replaces `&&` with `||` and vice versa.

        Returns:
            list[Mutant]: All LCR mutants.
        """
        return LogicalConnectorReplacement().apply(self._tree, self._source_bytes)

    def _apply_crp(self) -> list[Mutant]:
        """Apply Constant Replacement (CRP) mutations.

        For every integer literal in the source, produce mutants that replace
        it with `0`, `literal + 1`, and `literal - 1` (skipping cases
        where the replacement equals the original).

        It skips the 0 replacement when the literal is already 0.

        Returns:
            list[Mutant]: All CRP mutants.
        """
        return ConstantReplacement().apply(self._tree, self._source_bytes)

    def _apply_rvr(self) -> list[Mutant]:
        """Apply Return Value Replacement (RVR) mutations.

        For every `return` statement that returns a non-zero expression,
        produce a mutant that returns `0` instead.  `void` functions are
        skipped entirely because they cannot meaningfully return a value.

        Returns:
            list[Mutant]: All RVR mutants.
        """
        return ReturnValueReplacement(self._c_function).apply(self._tree, self._source_bytes)
