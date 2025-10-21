#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

void swapA(int* a, int* b)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
__CPROVER_ensures(*a == __CPROVER_old(*b))
__CPROVER_ensures(*b == __CPROVER_old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}

void swapB(int* a, int* b)
__CPROVER_requires(
    __CPROVER_is_fresh(a, sizeof(int)))
__CPROVER_ensures(
    *b == __CPROVER_old(*a)
)
{
    int t = *a;
    *a = *b;
    *b = t;
}

void swap(int* a, int* b)
{
    int t = *a;
    *a = *b;
    *b = t;
}

void swapC(int* a, int* b)
__CPROVER_requires(
    __CPROVER_is_fresh(
        a, sizeof(int
        )
    )
)

__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(int)))
__CPROVER_ensures(
    *a == __CPROVER_old(*b))
__CPROVER_ensures(
    *b == 
    __CPROVER_old(*a))
{
    int t = *a;
    *a = *b;
    *b = t;
}