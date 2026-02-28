
/* FUNCTION: longjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

void avocado_longjmp(jmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assert(0, "longjmp requires instrumentation");
  __CPROVER_assume(0);
#ifdef LIBRARY_CHECK
  __builtin_unreachable();
#endif
}

/* FUNCTION: _longjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

void avocado__longjmp(jmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assert(0, "_longjmp requires instrumentation");
  __CPROVER_assume(0);
#ifdef LIBRARY_CHECK
  __builtin_unreachable();
#endif
}

/* FUNCTION: siglongjmp */

#ifndef _WIN32

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

void avocado_siglongjmp(sigjmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assert(0, "siglongjmp requires instrumentation");
  __CPROVER_assume(0);
#ifdef LIBRARY_CHECK
  __builtin_unreachable();
#endif
}

#endif

/* FUNCTION: setjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

#undef setjmp

int avocado_setjmp(jmp_buf env)
{
  (void)env;
  // returns via longjmp require instrumentation; only such returns would
  // return a non-zero value
  return 0;
}

/* FUNCTION: _setjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

int avocado__setjmp(jmp_buf env)
{
  (void)env;
  // returns via longjmp require instrumentation; only such returns would
  // return a non-zero value
  return 0;
}

/* FUNCTION: sigsetjmp */

#ifndef _WIN32

#ifndef __CPROVER_SETJMP_H_INCLUDED
#  include <setjmp.h>
#  define __CPROVER_SETJMP_H_INCLUDED
#endif

#undef sigsetjmp

int avocado_sigsetjmp(sigjmp_buf env, int savesigs)
{
  (void)env;
  (void)savesigs;
  // returns via siglongjmp require instrumentation; only such returns would
  // return a non-zero value
  return 0;
}

#endif

/* FUNCTION: __sigsetjmp */

#ifndef _WIN32

#ifndef __CPROVER_SETJMP_H_INCLUDED
#  include <setjmp.h>
#  define __CPROVER_SETJMP_H_INCLUDED
#endif

int avocado___sigsetjmp(sigjmp_buf env, int savesigs)
{
  (void)env;
  (void)savesigs;
  // returns via siglongjmp require instrumentation; only such returns would
  // return a non-zero value
  return 0;
}

#endif
