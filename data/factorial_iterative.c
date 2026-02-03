int factorial_iter(int n)
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

