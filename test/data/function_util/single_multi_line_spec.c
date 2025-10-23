void swap(int* a, int* b)
__CPROVER_requires(
    __CPROVER_is_fresh(a, sizeof(int))
)
{
    int t = *a;
    *a = *b;
    *b = t;
}