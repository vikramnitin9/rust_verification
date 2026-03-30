import pytest

from translation import CbmcAst, CbmcToKani, Parser, ToAst

cbmc_parser: Parser[CbmcAst] = Parser(
    path_to_grammar_defn="translation/grammar/cbmc.txt",
    start="cbmc_clause",
    transformer=ToAst(),
)
translator = CbmcToKani(parser=cbmc_parser)


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


def test_ensures_result_old() -> None:
    cbmc_specs = ["__CPROVER_ensures(__CPROVER_result == __CPROVER_old(*a))"]
    kani_specs = ["kani::ensures(|result| result == old(*a))"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_ensures_result_nested() -> None:
    cbmc_specs = ["__CPROVER_ensures(x >= 0 && __CPROVER_result > x)"]
    kani_specs = ["kani::ensures(|result| x >= 0 && result > x)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_array_condition() -> None:
    cbmc_specs = [
        "__CPROVER_requires(x > 0 && arr[x] > 0)",
        "__CPROVER_ensures(arr[__CPROVER_result] > 0)",
    ]
    kani_specs = [
        "kani::requires(x > 0 && arr[x] > 0)",
        "kani::ensures(|result| arr[result] > 0)",
    ]
    assert translator.translate(cbmc_specs) == kani_specs


def test_forall() -> None:
    cbmc_specs = [
        "__CPROVER_requires(__CPROVER_forall { int i; (0 <= i && i < n) ==> arr[i] > 0 })"
    ]
    kani_specs = ["kani::forall!(|i in (0, n)| arr[i] > 0)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_exists() -> None:
    cbmc_specs = [
        "__CPROVER_ensures(__CPROVER_exists { int i; (0 <= i && i < arr.size()) && arr[i] > 0 })"
    ]
    kani_specs = ["kani::exists!(|i in (0, arr.size())| arr[i] > 0)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_assigns() -> None:
    cbmc_specs = [
        "__CPROVER_assigns(*out)",
        "__CPROVER_assigns(*out1, *out2)",
    ]
    kani_specs = [
        "kani::modifies(*out)",
        "kani::modifies(*out1, *out2)",
    ]
    assert translator.translate(cbmc_specs) == kani_specs


def test_assigns_to_side_effectful_operation() -> None:
    cbmc_specs = [
        "__CPROVER_assigns(*side_effect())",
    ]
    with pytest.raises(ValueError):
        translator.translate(cbmc_specs)


def test_assigns_object_whole() -> None:
    cbmc_specs = [
        "__CPROVER_assigns(__CPROVER_object_whole(p))",
    ]
    kani_specs = [
        "kani::modifies(p)",
    ]
    assert translator.translate(cbmc_specs) == kani_specs


def test_assigns_object_whole_multiple() -> None:
    cbmc_specs = [
        "__CPROVER_assigns(__CPROVER_object_whole(p), __CPROVER_object_whole(q))",
    ]
    kani_specs = [
        "kani::modifies(p, q)",
    ]
    assert translator.translate(cbmc_specs) == kani_specs


def test_assigns_object_whole_mixed() -> None:
    cbmc_specs = [
        "__CPROVER_assigns(*out, __CPROVER_object_whole(buf))",
    ]
    kani_specs = [
        "kani::modifies(*out, buf)",
    ]
    assert translator.translate(cbmc_specs) == kani_specs


def test_frees_single() -> None:
    cbmc_specs = ["__CPROVER_frees(p)"]
    kani_specs = ["kani::frees(p)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_frees_multiple() -> None:
    cbmc_specs = ["__CPROVER_frees(arr1, arr2)"]
    kani_specs = ["kani::frees(arr1, arr2)"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_frees_empty() -> None:
    cbmc_specs = ["__CPROVER_frees()"]
    kani_specs = ["kani::frees()"]
    assert translator.translate(cbmc_specs) == kani_specs


def test_frees_conditional_unsupported() -> None:
    cbmc_specs = ["__CPROVER_frees(size > 0 && arr1: arr1)"]
    # Conditional frees raise TranslationError; translate() logs and drops them.
    assert translator.translate(cbmc_specs) == []


def test_frees_freeable_unsupported() -> None:
    cbmc_specs = ["__CPROVER_frees(__CPROVER_freeable(p))"]
    # __CPROVER_freeable has no Kani equivalent; translate() logs and drops it.
    assert translator.translate(cbmc_specs) == []
