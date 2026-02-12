#include <stdlib.h>
#include <limits.h>
void f3(int *x3, int *y3, int *z3)
__CPROVER_requires(__CPROVER_is_fresh(x3, sizeof(*x3)))
__CPROVER_requires(__CPROVER_is_fresh(y3, sizeof(*y3)))
__CPROVER_requires(__CPROVER_is_fresh(z3, sizeof(*z3)))
__CPROVER_requires(*x3 < INT_MAX)
__CPROVER_requires(*y3 < INT_MAX)
__CPROVER_requires(*z3 < INT_MAX)
__CPROVER_ensures(*x3 == __CPROVER_old(*x3) + 1)
__CPROVER_ensures(*y3 == __CPROVER_old(*y3) + 1)
__CPROVER_ensures(*z3 == __CPROVER_old(*z3) + 1)
__CPROVER_assigns(*x3, *y3, *z3)
{
  *x3 = *x3 + 1;
  *y3 = *y3 + 1;
  *z3 = *z3 + 1;
}

void f2(int *x2, int *y2, int *z2)
__CPROVER_requires(__CPROVER_is_fresh(x2, sizeof(*x2)))
__CPROVER_requires(__CPROVER_is_fresh(y2, sizeof(*y2)))
__CPROVER_requires(__CPROVER_is_fresh(z2, sizeof(*z2)))
__CPROVER_requires(*x2 < INT_MAX)
__CPROVER_requires(*y2 < INT_MAX)
__CPROVER_requires(*z2 < INT_MAX)
__CPROVER_ensures(*x2 == __CPROVER_old(*x2) + 1)
__CPROVER_ensures(*y2 == __CPROVER_old(*y2) + 1)
__CPROVER_ensures(*z2 == __CPROVER_old(*z2) + 1)
__CPROVER_assigns(*x2, *y2, *z2)
{
  f3(x2, y2, z2);
}

void f1(int *x1, int *y1, int *z1)
__CPROVER_requires(__CPROVER_is_fresh(x1, sizeof(*x1)))
__CPROVER_requires(__CPROVER_is_fresh(y1, sizeof(*y1)))
__CPROVER_requires(__CPROVER_is_fresh(z1, sizeof(*z1)))
__CPROVER_requires(*x1 < INT_MAX)
__CPROVER_requires(*y1 < INT_MAX)
__CPROVER_requires(*z1 < INT_MAX)
__CPROVER_ensures(*x1 == __CPROVER_old(*x1) + 1)
__CPROVER_ensures(*y1 == __CPROVER_old(*y1) + 1)
__CPROVER_ensures(*z1 == __CPROVER_old(*z1) + 1)
__CPROVER_assigns(*x1, *y1, *z1)
{
  f2(x1, y1, z1);
}

int main()
{
  int p = 1;
  int q = 2;
  int r = 3;

  for(int i = 0; i < 3; ++i)
  {
    if(i == 0)
    {
      f1(&p, &q, &r);
    }
    if(i == 1)
    {
      f2(&p, &q, &r);
    }
    if(i == 2)
    {
      f3(&p, &q, &r);
    }
  }

  return 0;
}
