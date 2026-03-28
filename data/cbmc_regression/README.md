# Description of Contents

This repository contains examples of already-specified C code from
    [CBMC's regression testing suite](https://github.com/diffblue/cbmc/tree/develop/regression).
The examples in this directory were filtered from the original testing suite with the following
    criteria:

- Tests for CBMC _contracts_ (e.g., `cbmc/regression/contracts`).
- Tests that comprise _legal_ contracts (i.e., tests that assert that verification succeeds).

Each subfolder contains the following files:

- `main.c`: The original test file from the testing suite (methods may have been re-ordered to
    avoid forward references).
- `test.desc`: A file containing a high-level test description.
- `main_masked.c`: Identical to `main.c`, but with all `__CPROVER` annotations removed. This is the
    file input to our tool for specification generation.
- `main_generated.c`: Our tool's output (i.e., the generated specs).
