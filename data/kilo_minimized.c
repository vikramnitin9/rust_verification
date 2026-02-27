#include <stdlib.h>
#include <ctype.h>

// To verify this, run: goto-cc -o is_separator.goto data/stubs.c data/kilo_minimized.c --function is_separator && goto-instrument --partial-loops --unwind 5 is_separator.goto is_separator.goto && goto-instrument  --enforce-contract is_separator is_separator.goto checking-is_separator-contracts.goto && cbmc checking-is_separator-contracts.goto --function is_separator --depth 100
// From the running Docker container.
int is_separator(int c)
{
    return c == '\0' || isspace(c) || strchr(",.()+-/*=~%[];",c) != NULL;
}
