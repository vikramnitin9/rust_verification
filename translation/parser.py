from lark import Lark
from lark.visitors import Transformer

from pathlib import Path

from typing import TypeVar, Generic, cast

T = TypeVar("T")


class Parser(Generic[T]):
    """Generic parsing utility using Lark.

    See Lark documentation for details: https://lark-parser.readthedocs.io/en/stable/

    Attributes:
        parser (Lark): The Lark parser instance.
        transformer (Transformer): The Lark transformer to convert parse trees to ASTs.
    """

    parser: Lark
    transformer: Transformer

    def __init__(self, path_to_grammar_defn: str, start: str, transformer: Transformer):
        """Create an instance of this Parser.

        Args:
            path_to_grammar_defn (str): The path to the grammar definition file, in Lark EBNF.
            start (str): The start rule for the grammar.
            transformer (Transformer): The Lark transformer to convert parse trees to ASTs.
        """
        grammar_defn = Path(path_to_grammar_defn).read_text(encoding="utf-8")
        self.parser = Lark(grammar_defn, start=start, parser="lalr", lexer="contextual")
        self.transformer = transformer

    def parse(self, text: str) -> T:
        """Return an AST parsed from the given text.

        Args:
            text (str): The text to parse.

        Returns:
            T: The parsed AST.
        """
        tree = self.parser.parse(text)
        return cast(T, self.transformer.transform(tree))
