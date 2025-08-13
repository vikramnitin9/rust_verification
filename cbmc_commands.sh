# First we verify that the swap function satisfies its contracts
# Compile to a goto file (intermediate representation)
rm -f *.goto
goto-cc -o swap.goto data/qsort.c --function swap
# Add checks to enforce contracts
goto-instrument --enforce-contract swap swap.goto checking-swap-contracts.goto
# Verify the contracts that we added through instrumentation in the previous step
cbmc checking-swap-contracts.goto --function swap --depth 100

# Assuming the above verification is successful,
# we can replace the swap function with its contract while verifying the other functions
rm -f *.goto
goto-cc -o partition.goto data/qsort.c --function partition
goto-instrument --partial-loops --unwind 5 partition.goto partition.goto
goto-instrument --replace-call-with-contract swap partition.goto partition.goto
goto-instrument --enforce-contract partition partition.goto checking-partition-contracts.goto
cbmc checking-partition-contracts.goto --function partition --depth 100

# Assuming the above verification is successful,
# we can replace both partition and swap functions with their contracts while verifying the other functions
rm -f *.goto
goto-cc -o quicksort.goto data/qsort.c --function quickSort
goto-instrument --partial-loops --unwind 5 quicksort.goto quicksort.goto
goto-instrument --replace-call-with-contract partition quicksort.goto quicksort.goto
# We have to use --enforce-contract-rec because quickSort is recursive
goto-instrument --dfcc quickSort --enforce-contract-rec quickSort quicksort.goto checking-quicksort-contracts.goto
cbmc checking-quicksort-contracts.goto --function quickSort --depth 100