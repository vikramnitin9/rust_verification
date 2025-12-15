from translation import KaniProofHarness
from util import FunctionSpecification
from util.rust import RustFunction, RustTypeWrapper


def test_kani_proof_harness_no_mut():
    harness = KaniProofHarness(
        RustFunction(
            name="add",
            param_to_type={
                "a": RustTypeWrapper("i32", is_reference=False),
                "b": RustTypeWrapper("i32", is_reference=False),
            },
        ),
        spec=FunctionSpecification(
            preconditions=["kani::requires(a < i32::MAX && b < i32::MAX)"], postconditions=[]
        ),
    )
    assert (
        str(harness)
        == """#[cfg(kani)]\n#[kani::proof]\nfn check_add() {\n    let a: i32 = kani::any();\n    let b: i32 = kani::any();\n\n    if a < i32::MAX && b < i32::MAX {\n        add(a, b);\n    }\n}"""
    )


def test_kani_proof_harness_nested_parens_preconds():
    harness = KaniProofHarness(
        RustFunction(
            name="add",
            param_to_type={
                "a": RustTypeWrapper("i32", is_reference=False),
                "b": RustTypeWrapper("i32", is_reference=False),
            },
        ),
        spec=FunctionSpecification(
            preconditions=["kani::requires((a < i32::MAX) && (b < i32::MAX))"], postconditions=[]
        ),
    )
    assert (
        str(harness)
        == """#[cfg(kani)]\n#[kani::proof]\nfn check_add() {\n    let a: i32 = kani::any();\n    let b: i32 = kani::any();\n\n    if (a < i32::MAX) && (b < i32::MAX) {\n        add(a, b);\n    }\n}"""
    )


def test_kani_proof_harness_swap():
    harness = KaniProofHarness(
        RustFunction(
            name="swap",
            param_to_type={
                "a": RustTypeWrapper("i32", is_reference=True, is_mutable=True),
                "b": RustTypeWrapper("i32", is_reference=True, is_mutable=True),
            },
        ),
        # [ensures(|result| *a == old(*b) && *b == old(*a))] [modifies(a, b)]
        spec=FunctionSpecification(preconditions=[], postconditions=["kani::ensures(|result| *a == old(*b) && *b == old(*all))","kani::modifies(a, b)"]),
    )
    assert (
        str(harness)
        == """#[cfg(kani)]\n#[kani::proof]\nfn check_swap() {\n    let mut a: i32 = kani::any();\n    let mut b: i32 = kani::any();\n\n    if true {\n        swap(&mut a, &mut b);\n    }\n}"""
    )


# TODO: additional test cases.
