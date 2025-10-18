from lark import Lark
from lark.ast_utils import Ast as LarkAST
from lark.visitors import Transformer

from pathlib import Path


class Parser:
    def __init__(self, path_to_grammar_defn: str, start: str, transformer: Transformer):
        grammar_defn = Path(path_to_grammar_defn).read_text()
        # Create parser without transformer so parse() always returns a Tree,
        # and we apply the transformer once below.
        self.parser = Lark(grammar_defn, start=start, parser="lalr")
        self.transformer = transformer

    def parse(self, text: str) -> LarkAST:
        tree = self.parser.parse(text)
        return self.transformer.transform(tree)
