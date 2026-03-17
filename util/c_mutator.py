"""Utility for performing mutation testing on C functions."""

from dataclasses import dataclass
from enum import StrEnum

import tree_sitter_c as tsc
from tree_sitter import Language, Node, Parser

from .c_function import CFunction

_C_LANGUAGE = Language(tsc.language())

# All operators recognised by the operator-replacement mutations.
_ALL_OPERATOR_REPLACEMENTS: frozenset[str] = frozenset(
    {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "||"}
)


class MutationOperator(StrEnum):
    """Mutation operator categories applied during mutation testing.

    Each variant corresponds to a classical first-order mutation operator:

    - AOR: Arithmetic Operator Replacement
    - ROR: Relational Operator Replacement
    - LCR: Logical Connector Replacement
    - CRP: Constant Replacement (integer literals)
    - RVR: Return Value Replacement
    """

    AOR = "AOR"
    ROR = "ROR"
    LCR = "LCR"
    CRP = "CRP"
    RVR = "RVR"


@dataclass(frozen=True)
class Mutant:
    """A mutated version of a C function's source code.

    Each ``Mutant`` represents exactly one syntactic change from the original
    source (i.e., it is a *first-order* mutant).

    Attributes:
        source_code: The complete, mutated function source code.
        operator: The mutation operator that produced this mutant.
        description: A human-readable description of the applied mutation.
        line: The 1-indexed line number (within the function source) where the
            mutation was applied.
        original: The original text that was replaced.
        replacement: The text that replaced the original.
    """

    source_code: str
    operator: MutationOperator
    description: str
    line: int
    original: str
    replacement: str


class CMutator:
    """Generates first-order mutants of a C function for mutation testing.

    Uses tree-sitter to parse the C source and systematically applies mutation
    operators to produce mutated versions of the function.  Each mutant differs
    from the original by exactly one syntactic change.

    Supported mutation operators:

    +---------+----------------------------------+---------------------------------------------+
    | AOR     | Arithmetic Operator Replacement  | replaces ``+``, ``-``, ``*``, ``/``, ``%`` |
    +---------+----------------------------------+---------------------------------------------+
    | ROR     | Relational Operator Replacement  | replaces ``<``, ``<=``, ``>``, ``>=``,      |
    |         |                                  | ``==``, ``!=``                              |
    +---------+----------------------------------+---------------------------------------------+
    | LCR     | Logical Connector Replacement    | replaces ``&&`` and ``||``                  |
    +---------+----------------------------------+---------------------------------------------+
    | CRP     | Constant Replacement             | replaces integer literals with ``0``,       |
    |         |                                  | ``literal + 1``, and ``literal - 1``        |
    +---------+----------------------------------+---------------------------------------------+
    | RVR     | Return Value Replacement         | replaces the expression in every            |
    |         |                                  | ``return`` statement with ``0``             |
    +---------+----------------------------------+---------------------------------------------+

    Example::

        from util import CFunction
        from util.c_mutator import CMutator

        mutator = CMutator(c_function)
        for mutant in mutator.get_mutants():
            print(mutant.description)
            print(mutant.source_code)
    """

    # Maps each arithmetic operator to its candidate replacements.
    _AOR_REPLACEMENTS: dict[str, list[str]] = {
        "+": ["-", "*"],
        "-": ["+", "*"],
        "*": ["/", "+"],
        "/": ["*", "+"],
        "%": ["+", "*"],
    }

    # Maps each relational operator to its candidate replacements.
    _ROR_REPLACEMENTS: dict[str, list[str]] = {
        "<": ["<=", ">", ">=", "==", "!="],
        "<=": ["<", ">", ">=", "==", "!="],
        ">": ["<", "<=", ">=", "==", "!="],
        ">=": ["<", "<=", ">", "==", "!="],
        "==": ["!=", "<", ">"],
        "!=": ["=="],
    }

    # Maps each logical connector to its candidate replacements.
    _LCR_REPLACEMENTS: dict[str, list[str]] = {
        "&&": ["||"],
        "||": ["&&"],
    }

    def __init__(self, c_function: CFunction) -> None:
        """Create a new ``CMutator``.

        The function's source code is taken from ``c_function.source_code`` when
        it has been set (via ``CFunction.set_source_code``); otherwise it is read
        from the original file via ``CFunction.get_original_source_code()``.

        Args:
            c_function: The C function to mutate.
        """
        self._c_function = c_function
        self._parser: Parser = Parser(_C_LANGUAGE)

        source = (
            c_function.source_code
            if c_function.source_code
            else c_function.get_original_source_code()
        )
        self._source_code: str = source
        self._source_bytes: bytes = source.encode("utf-8")
        self._tree = self._parser.parse(self._source_bytes)

    # ------------------------------------------------------------------ #
    # Public interface                                                     #
    # ------------------------------------------------------------------ #

    @property
    def c_function(self) -> CFunction:
        """Return the C function being mutated."""
        return self._c_function

    @property
    def source_code(self) -> str:
        """Return the (possibly pre-processed) source code being mutated."""
        return self._source_code

    def get_mutants(self) -> list[Mutant]:
        """Return all first-order mutants of this function.

        Mutants are produced by applying each enabled mutation operator in
        order: AOR → ROR → LCR → CRP → RVR.

        Returns:
            list[Mutant]: Every generated mutant, one per mutation site and
                replacement candidate.
        """
        mutants: list[Mutant] = []
        mutants.extend(self._apply_aor())
        mutants.extend(self._apply_ror())
        mutants.extend(self._apply_lcr())
        mutants.extend(self._apply_crp())
        mutants.extend(self._apply_rvr())
        return mutants

    def get_mutants_by_operator(self) -> dict[MutationOperator, list[Mutant]]:
        """Return mutants grouped by their mutation operator.

        Returns:
            dict[MutationOperator, list[Mutant]]: A mapping from each
                ``MutationOperator`` to the list of mutants produced by that
                operator.  Operators that produced no mutants are included with
                an empty list.
        """
        return {
            MutationOperator.AOR: self._apply_aor(),
            MutationOperator.ROR: self._apply_ror(),
            MutationOperator.LCR: self._apply_lcr(),
            MutationOperator.CRP: self._apply_crp(),
            MutationOperator.RVR: self._apply_rvr(),
        }

    # ------------------------------------------------------------------ #
    # Mutation operator implementations                                    #
    # ------------------------------------------------------------------ #

    def _apply_aor(self) -> list[Mutant]:
        """Apply Arithmetic Operator Replacement (AOR) mutations.

        Finds all binary arithmetic operators in the source and replaces each
        with every other operator in its replacement set.

        Returns:
            list[Mutant]: All AOR mutants.
        """
        return self._apply_binary_operator_replacements(
            MutationOperator.AOR, self._AOR_REPLACEMENTS
        )

    def _apply_ror(self) -> list[Mutant]:
        """Apply Relational Operator Replacement (ROR) mutations.

        Finds all relational operators in the source and replaces each with
        every other operator in its replacement set.

        Returns:
            list[Mutant]: All ROR mutants.
        """
        return self._apply_binary_operator_replacements(
            MutationOperator.ROR, self._ROR_REPLACEMENTS
        )

    def _apply_lcr(self) -> list[Mutant]:
        """Apply Logical Connector Replacement (LCR) mutations.

        Replaces ``&&`` with ``||`` and vice-versa.

        Returns:
            list[Mutant]: All LCR mutants.
        """
        return self._apply_binary_operator_replacements(
            MutationOperator.LCR, self._LCR_REPLACEMENTS
        )

    def _apply_crp(self) -> list[Mutant]:
        """Apply Constant Replacement (CRP) mutations.

        For every integer literal in the source, produce mutants that replace
        it with ``0``, ``literal + 1``, and ``literal - 1`` (skipping cases
        where the replacement equals the original).

        Floating-point and non-decimal literals (e.g. ``1.0f``, ``0x1A``) that
        cannot be parsed as plain integers by ``int(text, 0)`` are treated as
        integers where possible; pure floats are skipped.

        Returns:
            list[Mutant]: All CRP mutants.
        """
        mutants: list[Mutant] = []
        for node in self._collect_nodes_by_type(self._tree.root_node, "number_literal"):
            original_text = self._node_text(node)
            try:
                # base=0 handles hex (0x…), octal (0…), and binary (0b…) literals.
                original_value = int(original_text, 0)
            except ValueError:
                continue  # Skip floating-point literals (e.g. 1.0, 2.5f).

            # Use a set to avoid emitting duplicate replacement values.
            # Example: for literal '1', both the "replace with 0" guard and
            # "original_value - 1" would otherwise add 0 twice.
            candidate_set: set[int] = {original_value + 1}
            if original_value != 0:
                candidate_set.add(0)
                candidate_set.add(original_value - 1)
            replacements = sorted(candidate_set)

            for replacement_value in replacements:
                replacement_text = str(replacement_value)
                mutated_src = self._replace_node(node, replacement_text)
                line = node.start_point[0] + 1
                mutants.append(
                    Mutant(
                        source_code=mutated_src,
                        operator=MutationOperator.CRP,
                        description=(
                            f"CRP: replaced constant '{original_text}' with "
                            f"'{replacement_text}' at line {line}"
                        ),
                        line=line,
                        original=original_text,
                        replacement=replacement_text,
                    )
                )
        return mutants

    def _apply_rvr(self) -> list[Mutant]:
        """Apply Return Value Replacement (RVR) mutations.

        For every ``return`` statement that returns a non-zero expression,
        produce a mutant that returns ``0`` instead.  ``void`` functions are
        skipped entirely because they cannot meaningfully return a value.

        Returns:
            list[Mutant]: All RVR mutants.
        """
        mutants: list[Mutant] = []
        if self._c_function.return_type == "void":
            return mutants

        for node in self._collect_nodes_by_type(self._tree.root_node, "return_statement"):
            # A return_statement's named children exclude the "return" keyword and ";".
            expr_node: Node | None = next(iter(node.named_children), None)
            if expr_node is None:
                continue  # bare `return;` — nothing to replace

            original_text = self._node_text(expr_node)
            if original_text == "0":
                continue  # already returns 0; no interesting mutation

            mutated_src = self._replace_node(expr_node, "0")
            line = expr_node.start_point[0] + 1
            mutants.append(
                Mutant(
                    source_code=mutated_src,
                    operator=MutationOperator.RVR,
                    description=(
                        f"RVR: replaced return value '{original_text}' with '0' at line {line}"
                    ),
                    line=line,
                    original=original_text,
                    replacement="0",
                )
            )
        return mutants

    # ------------------------------------------------------------------ #
    # Shared helper for operator-replacement mutations                     #
    # ------------------------------------------------------------------ #

    def _apply_binary_operator_replacements(
        self,
        operator: MutationOperator,
        replacement_map: dict[str, list[str]],
    ) -> list[Mutant]:
        """Generate operator-replacement mutants for all matching binary expressions.

        Args:
            operator: The ``MutationOperator`` label to attach to each mutant.
            replacement_map: Maps an operator symbol to a list of replacement
                symbols to substitute in its place.

        Returns:
            list[Mutant]: All mutants produced by the given replacement map.
        """
        mutants: list[Mutant] = []
        for node in self._collect_nodes_by_type(self._tree.root_node, "binary_expression"):
            op_node = self._get_operator_node(node)
            if op_node is None:
                continue
            op_text = self._node_text(op_node)
            for replacement in replacement_map.get(op_text, []):
                mutated_src = self._replace_node(op_node, replacement)
                line = op_node.start_point[0] + 1
                mutants.append(
                    Mutant(
                        source_code=mutated_src,
                        operator=operator,
                        description=(
                            f"{operator}: replaced '{op_text}' with '{replacement}' at line {line}"
                        ),
                        line=line,
                        original=op_text,
                        replacement=replacement,
                    )
                )
        return mutants

    # ------------------------------------------------------------------ #
    # Tree-sitter helpers                                                  #
    # ------------------------------------------------------------------ #

    def _collect_nodes_by_type(self, node: Node, node_type: str) -> list[Node]:
        """Recursively collect all descendant nodes (including *node*) of a given type.

        Args:
            node: The root of the sub-tree to search.
            node_type: The tree-sitter node type string to match (e.g.
                ``"binary_expression"`` or ``"number_literal"``).

        Returns:
            list[Node]: All matching nodes in pre-order.
        """
        result: list[Node] = []
        if node.type == node_type:
            result.append(node)
        for child in node.children:
            result.extend(self._collect_nodes_by_type(child, node_type))
        return result

    def _get_operator_node(self, binary_expr: Node) -> Node | None:
        """Return the anonymous operator child of a ``binary_expression`` node.

        In the tree-sitter C grammar, the operator within a ``binary_expression``
        is an *anonymous* (unnamed) child node whose text is the operator symbol.

        Args:
            binary_expr: A ``binary_expression`` node.

        Returns:
            Node | None: The operator node, or ``None`` if none is found.
        """
        for child in binary_expr.children:
            if not child.is_named:
                text = self._node_text(child)
                if text in _ALL_OPERATOR_REPLACEMENTS:
                    return child
        return None

    def _node_text(self, node: Node) -> str:
        """Return the original source text covered by *node*.

        Args:
            node: The tree-sitter node whose text to retrieve.

        Returns:
            str: The source text for the node.
        """
        return self._source_bytes[node.start_byte : node.end_byte].decode("utf-8")

    def _replace_node(self, node: Node, replacement: str) -> str:
        """Return a new source string with *node*'s text replaced by *replacement*.

        Args:
            node: The tree-sitter node to replace.
            replacement: The replacement text.

        Returns:
            str: The full source string with the substitution applied.
        """
        return (
            self._source_bytes[: node.start_byte]
            + replacement.encode("utf-8")
            + self._source_bytes[node.end_byte :]
        ).decode("utf-8")
