from lark import Lark

from pathlib import Path


class Parser:
    def __init__(self, path_to_grammar_defn: str, start: str):
        grammar_defn = Path(path_to_grammar_defn).read_text()
        self.parser = Lark(grammar_defn, start=start)
