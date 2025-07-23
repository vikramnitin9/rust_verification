# First we verify that the swap function satisfies its contracts
# Compile to a goto file (intermediate representation)
goto-cc -o swap.goto qsort_specs.c --function swap
# Instrument the goto code to unwind loops
goto-instrument --partial-loops --unwind 5 swap.goto swap.goto
# Add checks to enforce contracts
goto-instrument --enforce-contract swap swap.goto checking-swap-contracts.goto
# Verify the contracts that we added through instrumentation in the previous step
cbmc checking-swap-contracts.goto --function swap

# Assuming the above verification is successful,
# we can replace the swap function with its contract while verifying the other functions
goto-cc -o partition.goto qsort_specs.c --function partition
goto-instrument --replace-call-with-contract swap partition.goto partition.goto
goto-instrument --partial-loops --unwind 5 partition.goto partition.goto
goto-instrument --enforce-contract partition partition.goto checking-partition-contracts.goto
cbmc checking-partition-contracts.goto --function partition