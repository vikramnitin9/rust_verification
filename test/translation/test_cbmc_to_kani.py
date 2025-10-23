from translation import CBMCToKani
from translation import Parser, ToAst, CBMCAst

cbmc_parser: Parser[CBMCAst] = Parser(
    path_to_grammar_defn="translation/grammar/cbmc.txt",
    start="cbmc_clause",
    transformer=ToAst(),
)
translator = CBMCToKani(parser=cbmc_parser)


def test_empty_specs() -> None:
    assert translator.translate([]) == []
