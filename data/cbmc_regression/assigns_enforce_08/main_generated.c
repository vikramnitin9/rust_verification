void f2(int** y)
__CPROVER_requires(__CPROVER_is_fresh(y, sizeof(int*)))
__CPROVER_requires(__CPROVER_is_fresh(*y, sizeof(int)))
__CPROVER_ensures(**y == 5)
__CPROVER_assigns(**y)
{
  **y = 5;
}

void f1(int *x)
__CPROVER_requires(__CPROVER_is_fresh(x, sizeof(*x)))
__CPROVER_ensures(*x == 5)
__CPROVER_assigns(*x)
{
  int *a = x;
  f2(&a);
}

int main()
{
  int n = 3;
  f1(&n);

  return 0;
}
