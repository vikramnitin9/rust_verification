goto-cc -o swap.goto qsort_specs.c --function swap
goto-instrument --partial-loops --unwind 5 --enforce-contract swap swap.goto swap-checking-contracts.goto
cbmc --partial-loops --unwind 5 swap-checking-contracts.goto --function swap