from translation import KaniProofHarness
from util.rust import RustFunction, RustTypeWrapper

from types import MappingProxyType


def test_kani_proof_harness_no_mut():
    harness = KaniProofHarness(
        RustFunction(
            name="add",
            param_to_type=MappingProxyType(
                {
                    "a": RustTypeWrapper("i32", is_reference=False),
                    "b": RustTypeWrapper("i32", is_reference=False),
                }
            ),
        )
    )
    assert (
        str(harness)
        == """#[cfg(kani)]\n#[kani::proof]\nfn check_add() {\n    let a: i32 = kani::any();\n    let b: i32 = kani::any();\n\n    add(a, b)\n}"""
    )


def test_kani_proof_harness_swap():
    harness = KaniProofHarness(
        RustFunction(
            name="swap",
            param_to_type=MappingProxyType(
                {
                    "a": RustTypeWrapper("i32", is_reference=True, is_mutable=True),
                    "b": RustTypeWrapper("i32", is_reference=True, is_mutable=True),
                }
            ),
        )
    )
    assert (
        str(harness)
        == """#[cfg(kani)]\n#[kani::proof]\nfn check_swap() {\n    let mut a: i32 = kani::any();\n    let mut b: i32 = kani::any();\n\n    swap(&mut a, &mut b)\n}"""
    )


# TODO: additional test cases.
