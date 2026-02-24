void f2(int** y)
{
  **y = 5;
}

void f1(int *x)
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
