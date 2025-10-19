from lark import Lark
from lark.ast_utils import Ast as LarkAST
from lark.visitors import Transformer

from pathlib import Path


class Parser:
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
        grammar_defn = Path(path_to_grammar_defn).read_text()
        # Create parser without transformer so parse() always returns a Tree,
        # and we apply the transformer once below.
        self.parser = Lark(grammar_defn, start=start, parser="lalr")
        self.transformer = transformer

    def parse(self, text: str) -> LarkAST:
        """Return an AST parsed from the given text.

        Args:
            text (str): The text to parse.

        Returns:
            LarkAST: The parsed AST.
        """
        tree = self.parser.parse(text)
        return self.transformer.transform(tree)
