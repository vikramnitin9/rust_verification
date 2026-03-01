/* FUNCTION: err */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

void avocado_err(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  avocado_abort();
}

/* FUNCTION: errx */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

void avocado_errx(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  avocado_abort();
}

/* FUNCTION: warn */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

void avocado_warn(const char *fmt, ...)
{
  (void)*fmt;
}

/* FUNCTION: warnx */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

void avocado_warnx(const char *fmt, ...)
{
  (void)*fmt;
}
