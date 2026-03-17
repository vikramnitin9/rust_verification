/* FUNCTION: err */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

void _avocado_err(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  _avocado_abort();
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

void _avocado_errx(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  _avocado_abort();
}

/* FUNCTION: warn */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

void _avocado_warn(const char *fmt, ...)
{
  (void)*fmt;
}

/* FUNCTION: warnx */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

void _avocado_warnx(const char *fmt, ...)
{
  (void)*fmt;
}
