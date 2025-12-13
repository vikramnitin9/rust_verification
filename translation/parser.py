"""Generic parsing utility class."""

from pathlib import Path
from typing import Generic, Protocol, TypeVar

from lark import Lark, Tree

T_co = TypeVar("T_co", covariant=True)


class TransformerT(Protocol[T_co]):
    """Represents a protocol requiring implementers to have a `transform` function."""

    def transform(self, tree: Tree) -> T_co:
        """Transform a Lark parse tree to an instance of `T_co` (usually an AST).

        Returns:
            T_co: An AST.
        """
        ...


class Parser(Generic[T_co]):  # noqa: UP046
    """Lark-based parser for grammars.

    See Lark documentation for details: https://lark-parser.readthedocs.io/en/stable/

    Attributes:
        parser (Lark): The Lark parser instance.
        transformer (TransformerT[T_co]): The transformer to convert raw Lark `Tree` values to
            user-defined ASTs (e.g., see `cbmc_ast.py`).
    """

    parser: Lark
    transformer: TransformerT[T_co]

    def __init__(self, path_to_grammar_defn: str, start: str, transformer: TransformerT[T_co]):
        """Create an instance of this Parser.

        Args:
            path_to_grammar_defn (str): The path to the grammar definition file, in Lark EBNF.
            start (str): The start rule for the grammar.
            transformer (TransformerT[T_co]): The transformer to convert Lark `Tree` values to
                user-defined ASTs (e.g., see `cbmc_ast.py`).
        """
        grammar_defn = Path(path_to_grammar_defn).read_text(encoding="utf-8")
        self.parser = Lark(
            grammar_defn,
            start=start,
            parser="lalr",
            lexer="contextual",
            cache=True,
            propagate_positions=True,
        )
        self.transformer = transformer

    def parse(self, text: str) -> T_co:
        """Return a user defined AST (T_co) parsed from the given text.

        Args:
            text (str): The text to parse.

        Returns:
            T_co: The parsed AST.
        """
        tree = self.parser.parse(text)
        return self.transformer.transform(tree)
