"""Represent a mutation operator for a C function implementation."""

from abc import ABC, abstractmethod
from collections.abc import Mapping
from types import MappingProxyType

from tree_sitter import Node, Tree

from util.c_function import CFunction
from util.tree_sitter_util import collect_nodes_by_type, node_text, replace_node

from .mutant import Mutant


class MutationOperator(ABC):
    """Mutation operator categories applied during mutation testing.

    Each subtype corresponds to a classical first-order mutation operator:

    - Arithmetic Operator Replacement
    - Relational Operator Replacement
    - Logical Connector Replacement
    - Constant Replacement (integer literals)
    - Return Value Replacement

    Supported mutation operators:

    +----------------------------------+---------------------------------------------+
    | Arithmetic Operator Replacement  | replaces `+`, `-`, `*`, `/`, `%`  |
    +----------------------------------+---------------------------------------------+
    | Relational Operator Replacement  | replaces `<`, `<=`, `>`, `>=`,      |
    |                                  | `==`, `!=`                              |
    +----------------------------------+---------------------------------------------+
    | Logical Connector Replacement    | replaces `&&` and `||`                  |
    +----------------------------------+---------------------------------------------+
    | Constant Replacement             | replaces integer literals with `0`,       |
    |                                  | `literal + 1`, and `literal - 1`        |
    +----------------------------------+---------------------------------------------+
    | Return Value Replacement         | replaces `return` expressions with `0`  |
    +----------------------------------+---------------------------------------------+

    """

    AOR = "AOR"
    ROR = "ROR"
    LCR = "LCR"
    CRP = "CRP"
    RVR = "RVR"

    @abstractmethod
    def apply(self, tree: Tree, source_bytes: bytes) -> list[Mutant]:
        """Return the mutants resulting from applying this mutation operator to the tree.

        Args:
            tree (Tree): The tree to which to apply this mutation operator.
            source_bytes (bytes): The source code as bytes, used for text extraction and
                replacement.

        Returns:
            list[Mutant]: The mutants resulting from applying this mutation operator to the tree.
        """
        ...

    @property
    @abstractmethod
    def name(self) -> str:
        """Return the name of this mutation operator.

        Returns:
            str: The name of this mutation operator.
        """
        ...


class BinaryMutationOperator(MutationOperator):
    """Represent a binary mutation operator.

    Attributes:
        _REPLACEMENTS (Mapping[str, list[str]]): A map from a binary operator (e.g., '+' or '-', to
            its replacement operators).

    """

    _REPLACEMENTS: Mapping[str, list[str]]

    def apply(self, tree: Tree, source_bytes: bytes) -> list[Mutant]:
        """Return all mutants from replacing binary operators using `_REPLACEMENTS`.

        Iterates over every `binary_expression` node in the tree, looks up the operator
        text in `_REPLACEMENTS`, and emits one mutant per replacement candidate.

        Args:
            tree (Tree): The parsed tree-sitter tree of the C source.
            source_bytes (bytes): The source code as bytes.

        Returns:
            list[Mutant]: All mutants produced by this operator's replacement map.
        """
        mutants: list[Mutant] = []
        for node in collect_nodes_by_type(tree.root_node, "binary_expression"):
            op_node = node.child_by_field_name("operator")
            if op_node is None:
                msg = f"Expected a binary expression '{node}' to have an 'operator' node"
                raise ValueError(msg)
            op_text = node_text(source_bytes, op_node)
            for replacement in self._REPLACEMENTS.get(op_text, []):
                mutated_src = replace_node(source_bytes, op_node, replacement)
                line = op_node.start_point[0] + 1
                mutants.append(
                    Mutant.create(
                        source_code=mutated_src,
                        operator=self.name,
                        line=line,
                        original=op_text,
                        replacement=replacement,
                    )
                )
        return mutants


class ArithmeticOperatorReplacement(BinaryMutationOperator):
    """Represent arithmetic operator replacement."""

    _REPLACEMENTS = MappingProxyType(
        {
            "+": ["-", "*"],
            "-": ["+", "*"],
            "*": ["/", "+"],
            "/": ["*", "+"],
            "%": ["+", "*"],
        }
    )

    @property
    def name(self) -> str:
        """Return the name of this mutation operator.

        Returns:
            str: The name of this mutation operator.
        """
        return MutationOperator.AOR


class RelationalOperatorReplacement(BinaryMutationOperator):
    """ROR: replaces relational operators with semantically meaningful alternatives.

    Ordering operators (`<`, `<=`, `>`, `>=`) are replaced with all other relational operators.
    Equality operators use a reduced set: `==` maps to `!=`, `<`, and `>` only; `!=` maps to
    `==` only. Replacements to supersets (e.g. `==` to `<=`) are omitted to avoid equivalent
    mutants.
    """

    _REPLACEMENTS = MappingProxyType(
        {
            "<": ["<=", ">", ">=", "==", "!="],
            "<=": ["<", ">", ">=", "==", "!="],
            ">": ["<", "<=", ">=", "==", "!="],
            ">=": ["<", "<=", ">", "==", "!="],
            "==": ["!=", "<", ">"],
            "!=": ["=="],
        }
    )

    @property
    def name(self) -> str:
        """Return the name of this mutation operator.

        Returns:
            str: The name of this mutation operator.
        """
        return MutationOperator.ROR


class LogicalConnectorReplacement(BinaryMutationOperator):
    """LCR: replaces `&&` with `||` and vice versa."""

    _REPLACEMENTS = MappingProxyType(
        {
            "&&": ["||"],
            "||": ["&&"],
        }
    )

    @property
    def name(self) -> str:
        """Return the name of this mutation operator.

        Returns:
            str: The name of this mutation operator.
        """
        return MutationOperator.LCR


class ConstantReplacement(MutationOperator):
    """CRP: replaces each integer literal with `0`, `literal + 1`, and `literal - 1`."""

    @property
    def name(self) -> str:
        """Return the name of this mutation operator.

        Returns:
            str: The name of this mutation operator.
        """
        return MutationOperator.CRP

    def apply(self, tree: Tree, source_bytes: bytes) -> list[Mutant]:
        """Return all CRP mutants by replacing integer literals with nearby values.

        For each integer literal, emits mutants for `0`, `literal + 1`, and `literal - 1`,
        skipping replacements equal to the original. The `0` replacement is also skipped
        when the literal is already `0`. Floating-point literals are skipped entirely.

        Args:
            tree (Tree): The parsed tree-sitter tree of the C source.
            source_bytes (bytes): The source code as bytes.

        Returns:
            list[Mutant]: All CRP mutants.
        """
        mutants: list[Mutant] = []
        for node in collect_nodes_by_type(tree.root_node, "number_literal"):
            original_text = node_text(source_bytes, node)
            try:
                # base=0 handles hex (0x...), octal (0...), and binary (0b...) literals.
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
            # Sets have no built-in iteration order; sorting ensures deterministic output.
            for replacement_value in sorted(candidate_set):
                replacement_text = str(replacement_value)
                mutated_src = replace_node(source_bytes, node, replacement_text)
                line = node.start_point[0] + 1
                mutants.append(
                    Mutant.create(
                        source_code=mutated_src,
                        operator=self.name,
                        line=line,
                        original=original_text,
                        replacement=replacement_text,
                    )
                )
        return mutants


class ReturnValueReplacement(MutationOperator):
    """RVR: replaces each non-zero return expression with `0`."""

    def __init__(self, c_function: CFunction) -> None:
        """Create a `ReturnValueReplacement` operator for the given function.

        Args:
            c_function (CFunction): The function being mutated. Its return type is used
                to skip `void` functions, which cannot meaningfully return a value.
        """
        self._return_type = c_function.return_type

    @property
    def name(self) -> str:
        """Return the name of this mutation operator.

        Returns:
            str: The name of this mutation operator.
        """
        return MutationOperator.RVR

    def apply(self, tree: Tree, source_bytes: bytes) -> list[Mutant]:
        """Return all RVR mutants by replacing return expressions with `0`.

        `void` functions produce no mutants. `return` statements that already
        return zero (including `0x0`, `00`, `0b0`, etc.), or bare `return;`
        statements, are also skipped.

        Args:
            tree (Tree): The parsed tree-sitter tree of the C source.
            source_bytes (bytes): The source code as bytes.

        Returns:
            list[Mutant]: All RVR mutants.
        """
        mutants: list[Mutant] = []
        if self._return_type == "void":
            return mutants
        for node in collect_nodes_by_type(tree.root_node, "return_statement"):
            # A return_statement's named children exclude the "return" keyword and ";".
            expr_node: Node | None = next(iter(node.named_children), None)
            if expr_node is None:
                continue  # bare `return;` — nothing to replace
            original_text = node_text(source_bytes, expr_node)
            if expr_node.type == "number_literal":
                try:
                    if int(original_text, 0) == 0:
                        continue  # already returns 0; no interesting mutation
                except ValueError:
                    pass  # non-integer literal (e.g. 0.0f) — don't skip
            elif original_text == "0":
                continue  # already returns 0; no interesting mutation
            mutated_src = replace_node(source_bytes, expr_node, "0")
            line = expr_node.start_point[0] + 1
            mutants.append(
                Mutant.create(
                    source_code=mutated_src,
                    operator=self.name,
                    line=line,
                    original=original_text,
                    replacement="0",
                )
            )
        return mutants
