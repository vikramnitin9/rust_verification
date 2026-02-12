#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

struct pair
{
  uint8_t *buf;
  size_t size;
};

struct pair_of_pairs
{
  struct pair *p;
};

void f1(struct pair *p)
__CPROVER_requires(p != NULL)
__CPROVER_requires(p->buf != NULL)
__CPROVER_requires(__CPROVER_is_fresh(p, sizeof(*p)))
__CPROVER_requires(__CPROVER_is_fresh(p->buf, 1))
__CPROVER_ensures(p->buf[0] == 0)
__CPROVER_assigns(p->buf[0])
{
  if(p && p->buf)
    p->buf[0] = 0;
}

void f2(struct pair_of_pairs *pp)
__CPROVER_requires(pp != NULL)
__CPROVER_requires(pp->p != NULL)
__CPROVER_requires(pp->p->buf != NULL)
__CPROVER_requires(__CPROVER_is_fresh(pp, sizeof(*pp)))
__CPROVER_requires(__CPROVER_is_fresh(pp->p, sizeof(*(pp->p))))
__CPROVER_requires(__CPROVER_is_fresh(pp->p->buf, sizeof(*(pp->p->buf))))
__CPROVER_assigns(pp->p->buf[0])
__CPROVER_ensures(pp->p->buf[0] == 0)
{
  if(pp && pp->p && pp->p->buf)
    pp->p->buf[0] = 0;
}

int main()
{
  struct pair *p = malloc(sizeof(*p));
  if(p)
    p->buf = malloc(100 * sizeof(uint8_t));
  f1(p);

  struct pair_of_pairs *pp = malloc(sizeof(*pp));
  if(pp)
  {
    pp->p = malloc(sizeof(*(pp->p)));
    if(pp->p)
      pp->p->buf = malloc(100 * sizeof(uint8_t));
  }
  f2(pp);

  return 0;
}
