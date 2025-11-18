from translation import KaniProofHarness
from util import ParsecFunction

def test_kani_proof_harness_swap():
    harness = KaniProofHarness(ParsecFunction({
            "name": "swap",
            "num_args": 2,
            "returnType": "void",
            "signature": "void swap(int* a, int* b)",
            "filename": "data/qsort.c",
            "startLine": 999,
            "endLine": 9999,
            'argNames': ['a', 'b'],
            'argTypes': ['int *', 'int *'],
            "startCol": 1,
            "endCol": 25,
            "callees": [],
        }))
    assert str(harness) == """#[cfg(kani)]\n#[kani::proof]\nfn check_swap() {\n    let mut a: i32 = kani::any();\n    let mut b: i32 = kani::any();\n\n    swap(&mut a, &mut b)\n}"""

# TODO: additional test cases.