void assigns_ptr(int *x)
__CPROVER_requires(__CPROVER_is_fresh(x, sizeof(*x)))
__CPROVER_ensures(*x == 200)
__CPROVER_assigns(*x)
{
  *x = 200;
}

void uses_assigns(int a[], int i, int len)
__CPROVER_requires(len > 0)
__CPROVER_requires(i >= 0)
__CPROVER_requires(i < len)
__CPROVER_requires(__CPROVER_is_fresh(a, len * sizeof(int)))
__CPROVER_ensures(a[i] == 200)
__CPROVER_assigns(a[i])
{
  int *ptr = &(a[i]);
  assigns_ptr(ptr);
}

int main()
{
  int arr[10];
  int i;
  __CPROVER_assume(0 <= i && i < 10);
  uses_assigns(arr, i, 10);
  return 0;
}
