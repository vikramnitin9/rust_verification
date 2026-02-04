int factorial_iter(int n)
__CPROVER_requires(n >= 0)
__CPROVER_requires(n <= 12)
__CPROVER_ensures(__CPROVER_return_value >= 1)
__CPROVER_ensures(__CPROVER_return_value <= 479001600)
{
    int result = 1;
    if (n == 0) {
      return result;
    }
    for (int i = 1; i <= n; i++) {
      result *= i;
    }
    return result;
}