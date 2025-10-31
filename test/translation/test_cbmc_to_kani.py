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


def test_requires_true_false() -> None:
    cbmc_specs = ["__CPROVER_requires(true)", "__CPROVER_requires(false)"]
    kani_specs = ["kani::requires(true)", "kani::requires(false)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_simple_boolean_comps() -> None:
    cbmc_specs = ["__CPROVER_requires(x > 0)"]
    kani_specs = ["kani::requires(x > 0)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_nested_boolean_exprs() -> None:
    cbmc_specs = ["__CPROVER_ensures(true || x > 0 && false)"]
    kani_specs = ["kani::ensures(true || x > 0 && false)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_ensures_result_simple() -> None:
    cbmc_specs = ["__CPROVER_ensures(__CPROVER_result > x)"]
    kani_specs = ["kani::ensures(|result| result > x)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_ensures_result_nested() -> None:
    cbmc_specs = ["__CPROVER_ensures(x >= 0 && __CPROVER_result > x)"]
    kani_specs = ["kani::ensures(|result| x >= 0 && result > x)"]
    assert translator.translate(cbmc_specs) == kani_specs

def test_array_condition() -> None:
    cbmc_specs = ["__CPROVER_requires(x > 0 && arr[x] > 0)", "__CPROVER_ensures(arr[__CPROVER_result] > 0)"]
    kani_specs = [
        "kani::requires(x > 0 && arr[x] > 0)",
        "kani::ensures(|result| arr[result] > 0)",
    ]
    assert translator.translate(cbmc_specs) == kani_specs

def test_forall() -> None:
    cbmc_specs = ["__CPROVER_requires(__CPROVER_exists { int i; (0 <= i && i < n) && arr[i] > 0 })"]
    kani_specs = ["kani::requires(kani::exists!(|i in (0, n)| arr[i] > 0))"]
    assert translator.translate(cbmc_specs) == kani_specs
