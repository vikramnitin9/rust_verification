#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

int add_v1(int a, int b)
__CPROVER_requires(a >= 0 && a < INT_MAX / 2)
__CPROVER_requires(b >= 0 && b < INT_MAX / 2)
__CPROVER_requires(a + b < INT_MAX)
{
  return a + b;
}

// int add_v1(int a, int b)
// {
//   return a + b;
// }

// int add_v1(int a, int b)
// {
//   return a + b;
// }

// int add_v1(int a, int b)
// {
//   return a + b;
// }
