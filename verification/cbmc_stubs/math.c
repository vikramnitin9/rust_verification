/* FUNCTION: fabs */

double avocado_fabs(double d)
{
  return __CPROVER_fabs(d);
}

/* FUNCTION: fabsl */

long double avocado_fabsl(long double d)
{
  return __CPROVER_fabsl(d);
}

/* FUNCTION: fabsf */

float avocado_fabsf(float f)
{
  return __CPROVER_fabsf(f);
}

/* FUNCTION: __builtin_fabs */

double avocado___builtin_fabs(double d)
{
  return __CPROVER_fabs(d);
}

/* FUNCTION: __builtin_fabsl */

long double avocado___builtin_fabsl(long double d)
{
  return __CPROVER_fabsl(d);
}

/* FUNCTION: __builtin_fabsf */

float avocado___builtin_fabsf(float f)
{
  return __CPROVER_fabsf(f);
}

/* FUNCTION: __CPROVER_isgreaterf */

int __CPROVER_isgreaterf(float f, float g) { return f > g; }

/* FUNCTION: __CPROVER_isgreaterd */

int __CPROVER_isgreaterd(double f, double g) { return f > g; }

/* FUNCTION: __CPROVER_isgreaterequalf */

int __CPROVER_isgreaterequalf(float f, float g) { return f >= g; }

/* FUNCTION: __CPROVER_isgreaterequald */

int __CPROVER_isgreaterequald(double f, double g) { return f >= g; }

/* FUNCTION: __CPROVER_islessf */

int __CPROVER_islessf(float f, float g) { return f < g;}

/* FUNCTION: __CPROVER_islessd */

int __CPROVER_islessd(double f, double g) { return f < g;}

/* FUNCTION: __CPROVER_islessequalf */

int __CPROVER_islessequalf(float f, float g) { return f <= g; }

/* FUNCTION: __CPROVER_islessequald */

int __CPROVER_islessequald(double f, double g) { return f <= g; }

/* FUNCTION: __CPROVER_islessgreaterf */

int __CPROVER_islessgreaterf(float f, float g) { return (f < g) || (f > g); }

/* FUNCTION: __CPROVER_islessgreaterd */

int __CPROVER_islessgreaterd(double f, double g) { return (f < g) || (f > g); }

/* FUNCTION: __CPROVER_isunorderedf */

int __CPROVER_isunorderedf(float f, float g)
{
  return __CPROVER_isnanf(f) || __CPROVER_isnanf(g);
}

/* FUNCTION: __CPROVER_isunorderedd */

int __CPROVER_isunorderedd(double f, double g)
{
  return __CPROVER_isnand(f) || __CPROVER_isnand(g);
}

/* FUNCTION: isfinite */

#undef isfinite

int avocado_isfinite(double d) { return __CPROVER_isfinited(d); }

/* FUNCTION: __finite */

int avocado___finite(double d) { return __CPROVER_isfinited(d); }

/* FUNCTION: __finitef */

int avocado___finitef(float f) { return __CPROVER_isfinitef(f); }

/* FUNCTION: __finitel */

int avocado___finitel(long double ld) { return __CPROVER_isfiniteld(ld); }

/* FUNCTION: isinf */

#undef isinf

int avocado_isinf(double d)
{
  return __CPROVER_isinfd(d);
}

/* FUNCTION: __isinf */

int avocado___isinf(double d)
{
  return __CPROVER_isinfd(d);
}

/* FUNCTION: isinff */

int avocado_isinff(float f)
{
  return __CPROVER_isinff(f);
}

/* FUNCTION: __isinff */

int avocado___isinff(float f)
{
  return __CPROVER_isinff(f);
}

/* FUNCTION: isinfl */

int avocado_isinfl(long double ld)
{
  return __CPROVER_isinfld(ld);
}

/* FUNCTION: __isinfl */

int avocado___isinfl(long double ld)
{
  return __CPROVER_isinfld(ld);
}

/* FUNCTION: isnan */

#undef isnan

int avocado_isnan(double d)
{
  return __CPROVER_isnand(d);
}

/* FUNCTION: __isnan */

int avocado___isnan(double d)
{
  return __CPROVER_isnand(d);
}

/* FUNCTION: __isnanf */

int avocado___isnanf(float f)
{
  return __CPROVER_isnanf(f);
}

/* FUNCTION: isnanf */

int avocado_isnanf(float f)
{
  return __CPROVER_isnanf(f);
}

/* FUNCTION: isnanl */

int avocado_isnanl(long double ld)
{
  return __CPROVER_isnanld(ld);
}

/* FUNCTION: __isnanl */

int avocado___isnanl(long double ld)
{
  return __CPROVER_isnanld(ld);
}

/* FUNCTION: isnormal */

#undef isnormal

int avocado_isnormal(double d)
{
  return __CPROVER_isnormald(d);
}

/* FUNCTION: __isnormalf */

int avocado___isnormalf(float f)
{
  return __CPROVER_isnormalf(f);
}

/* FUNCTION: __builtin_isinf */

int avocado___builtin_isinf(double d)
{
  return __CPROVER_isinfd(d);
}

/* FUNCTION: __builtin_isinff */

int avocado___builtin_isinff(float f)
{
  return __CPROVER_isinff(f);
}

/* FUNCTION: __builtin_isinf */

int avocado___builtin_isinfl(long double ld)
{
  return __CPROVER_isinfld(ld);
}

/* FUNCTION: __builtin_isnan */

int avocado___builtin_isnan(double d)
{
  return __CPROVER_isnand(d);
}

/* FUNCTION: __builtin_isnanf */

int avocado___builtin_isnanf(float f)
{
  return __CPROVER_isnanf(f);
}

/* FUNCTION: __builtin_huge_valf */

float avocado___builtin_huge_valf(void)
{
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
#pragma CPROVER check disable "float-overflow"
  return 1.0f / 0.0f;
#pragma CPROVER check pop
}

/* FUNCTION: __builtin_huge_val */

double avocado___builtin_huge_val(void)
{
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
#pragma CPROVER check disable "float-overflow"
  return 1.0 / 0.0;
#pragma CPROVER check pop
}

/* FUNCTION: __builtin_huge_vall */

long double avocado___builtin_huge_vall(void)
{
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
#pragma CPROVER check disable "float-overflow"
  return 1.0l / 0.0l;
#pragma CPROVER check pop
}

/* FUNCTION: _dsign */

int avocado__dsign(double d)
{
  return __CPROVER_signd(d);
}

/* FUNCTION: _ldsign */

int avocado__ldsign(long double ld)
{
  return __CPROVER_signld(ld);
}

/* FUNCTION: _fdsign */

int avocado__fdsign(float f)
{
  return __CPROVER_signf(f);
}

/* FUNCTION: signbit */

#undef signbit

int avocado_signbit(double d)
{
  return __CPROVER_signd(d);
}

/* FUNCTION: __signbitd */

int avocado___signbitd(double d)
{
  return __CPROVER_signd(d);
}

/* FUNCTION: __signbitf */

int avocado___signbitf(float f)
{
  return __CPROVER_signf(f);
}

/* FUNCTION: __signbit */

int avocado___signbit(double ld)
{
  return __CPROVER_signld(ld);
}

/* FUNCTION: _dclass */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

short avocado__dclass(double d)
{
__CPROVER_HIDE:
  return __CPROVER_isnand(d)?FP_NAN:
         __CPROVER_isinfd(d)?FP_INFINITE:
         d==0?FP_ZERO:
         __CPROVER_isnormald(d)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: _ldclass */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

short avocado__ldclass(long double ld)
{
__CPROVER_HIDE:
  return __CPROVER_isnanld(ld)?FP_NAN:
         __CPROVER_isinfld(ld)?FP_INFINITE:
         ld==0?FP_ZERO:
         __CPROVER_isnormalld(ld)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: _fdclass */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

short avocado__fdclass(float f)
{
__CPROVER_HIDE:
  return __CPROVER_isnanf(f)?FP_NAN:
         __CPROVER_isinff(f)?FP_INFINITE:
         f==0?FP_ZERO:
         __CPROVER_isnormalf(f)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: __fpclassifyd */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

int avocado___fpclassifyd(double d)
{
__CPROVER_HIDE:
  return __CPROVER_fpclassify(
    FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, d);
}

/* FUNCTION: __fpclassifyf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

int avocado___fpclassifyf(float f)
{
__CPROVER_HIDE:
  return __CPROVER_fpclassify(
    FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, f);
}

/* FUNCTION: __fpclassifyl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

int avocado___fpclassifyl(long double f)
{
__CPROVER_HIDE:
  return __CPROVER_fpclassify(
    FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, f);
}

/* FUNCTION: __fpclassify */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// The variant with long double below is needed for older Macs
// only; newer ones use __fpclassifyd.

#ifdef __APPLE__
int avocado___fpclassify(long double d)
{
__CPROVER_HIDE:
  return __CPROVER_fpclassify(
    FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, d);
}
#else
int avocado___fpclassify(double d)
{
__CPROVER_HIDE:
  return __CPROVER_fpclassify(
    FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, d);
}
#endif

/* FUNCTION: sin */

double __VERIFIER_nondet_double(void);

double avocado_sin(double x)
{
  // gross over-approximation
  double avocado_ret=__VERIFIER_nondet_double();

  if(__CPROVER_isinfd(x) || __CPROVER_isnand(x))
    __CPROVER_assume(__CPROVER_isnand(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==0);
  }

  return ret;
}

/* FUNCTION: sinl */

long double __VERIFIER_nondet_long_double(void);

long double avocado_sinl(long double x)
{
  // gross over-approximation
  long double avocado_ret=__VERIFIER_nondet_long_double();

  if(__CPROVER_isinfld(x) || __CPROVER_isnanld(x))
    __CPROVER_assume(__CPROVER_isnanld(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==0);
  }

  return ret;
}

/* FUNCTION: sinf */

float __VERIFIER_nondet_float(void);

float avocado_sinf(float x)
{
  // gross over-approximation
  float avocado_ret=__VERIFIER_nondet_float();

  if(__CPROVER_isinff(x) || __CPROVER_isnanf(x))
    __CPROVER_assume(__CPROVER_isnanf(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==0);
  }

  return ret;
}

/* FUNCTION: cos */

double __VERIFIER_nondet_double(void);

double avocado_cos(double x)
{
  // gross over-approximation
  double avocado_ret=__VERIFIER_nondet_double();

  if(__CPROVER_isinfd(x) || __CPROVER_isnand(x))
    __CPROVER_assume(__CPROVER_isnand(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==1);
  }

  return ret;
}

/* FUNCTION: cosl */

long double __VERIFIER_nondet_long_double(void);

long double avocado_cosl(long double x)
{
  // gross over-approximation
  long double avocado_ret=__VERIFIER_nondet_long_double();

  if(__CPROVER_isinfld(x) || __CPROVER_isnanld(x))
    __CPROVER_assume(__CPROVER_isnanld(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==1);
  }

  return ret;
}

/* FUNCTION: cosf */

float __VERIFIER_nondet_float(void);

float avocado_cosf(float x)
{
__CPROVER_hide:;
  // gross over-approximation
  float avocado_ret=__VERIFIER_nondet_float();

  if(__CPROVER_isinff(x) || __CPROVER_isnanf(x))
    __CPROVER_assume(__CPROVER_isnanf(ret));
  else
  {
    __CPROVER_assume(ret<=1);
    __CPROVER_assume(ret>=-1);
    __CPROVER_assume(x!=0 || ret==1);
  }

  return ret;
}

/* FUNCTION: __builtin_nan */

double avocado___builtin_nan(const char *str)
{
  // the 'str' argument is not yet used
__CPROVER_hide:;
  (void)*str;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  return 0.0/0.0;
#pragma CPROVER check pop
}

/* FUNCTION: __builtin_nanf */

float avocado___builtin_nanf(const char *str)
{
  // the 'str' argument is not yet used
__CPROVER_hide:;
  (void)*str;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  return 0.0f/0.0f;
#pragma CPROVER check pop
}


/* ISO 9899:2011
 * The call nan("n-char-sequence") is equivalent to
 * strtod("NAN(n-char-sequence)", (char**) NULL); the call nan("") is
 * equivalent to strtod("NAN()", (char**) NULL). If tagp does not
 * point to an n-char sequence or an empty string, the call is
 * equivalent to strtod("NAN", (char**) NULL). Calls to nanf and nanl
 * are equivalent to the corresponding calls to strtof and strtold.
 *
 * The nan functions return a quiet NaN, if available, with content
 * indicated through tagp. If the implementation does not support
 * quiet NaNs, the functions return zero.
 */

/* FUNCTION: nan */

double avocado_nan(const char *str) {
  // the 'str' argument is not yet used
 __CPROVER_hide:;
  (void)*str;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  return 0.0/0.0;
#pragma CPROVER check pop
}

/* FUNCTION: nanf */

float avocado_nanf(const char *str) {
  // the 'str' argument is not yet used
 __CPROVER_hide:;
  (void)*str;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  return 0.0f/0.0f;
#pragma CPROVER check pop
}

/* FUNCTION: nanl */

long double avocado_nanl(const char *str) {
  // the 'str' argument is not yet used
 __CPROVER_hide:;
  (void)*str;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  return 0.0/0.0;
#pragma CPROVER check pop
}

/* FUNCTION: nextUpf */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif


// IEEE_754 2008 althought similar to C's nextafter / nexttowards
// Loosely assumes that float is (IEEE-754) binary32

union mixf
{
  float f;
  #ifdef LIBRARY_CHECK
  int bv;
  #else
  __CPROVER_bitvector[CHAR_BIT * sizeof(float)] bv;
  #endif
};

float avocado_nextUpf(float f)
{
__CPROVER_hide:;
  if (__CPROVER_isnanf(f))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f/0.0f;  // NaN
#pragma CPROVER check pop
  else if (f == 0.0f)
    return 0x1p-149f;
  else if (f > 0.0f)
  {
    if (__CPROVER_isinff(f))
      return f;

    union mixf avocado_m;
    m.f = f;
    ++m.bv;
    return m.f;
  }
  else
  {
    //assert(f < 0.0f);

    union mixf avocado_m;
    m.f = f;
    --m.bv;
    return m.f;
  }
}

/* FUNCTION: nextUp */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif


// IEEE_754 2008 althought similar to C's nextafter / nexttowards
// Loosely assumes that double is (IEEE-754) binary64

union mixd
{
  double f;
  #ifdef LIBRARY_CHECK
  long long int bv;
  #else
  __CPROVER_bitvector[CHAR_BIT * sizeof(double)] bv;
  #endif
};

double avocado_nextUp(double d)
{
__CPROVER_hide:;
  if (__CPROVER_isnand(d))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0/0.0;  // NaN
#pragma CPROVER check pop
  else if (d == 0.0)
    return 0x1.0p-1074;
  else if (d > 0.0)
  {
    if (__CPROVER_isinfd(d))
      return d;

    union mixd avocado_m;
    m.f = d;
    ++m.bv;
    return m.f;
  }
  else
  {
    //assert(d < 0.0);

    union mixd avocado_m;
    m.f = d;
    --m.bv;
    return m.f;
  }
}


/* FUNCTION: nextUpl */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif

// IEEE_754 2008 althought similar to C's nextafter / nexttowards

union mixl
{
  long double f;
  #ifdef LIBRARY_CHECK
  long long int bv;
  #else
  __CPROVER_bitvector[CHAR_BIT * sizeof(long double)] bv;
  #endif
};

long double avocado_nextUpl(long double d)
{
__CPROVER_hide:;
  if(__CPROVER_isnanld(d))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0/0.0;  // NaN
#pragma CPROVER check pop
  else if (d == 0.0)
  {
    union mixl avocado_m;
    m.bv = 0x1;
    return m.f;
  }
  else if (d > 0.0)
  {
    if(__CPROVER_isinfld(d))
      return d;

    union mixl avocado_m;
    m.f = d;
    ++m.bv;
    return m.f;
  }
  else
  {
    //assert(d < 0.0);

    union mixl avocado_m;
    m.f = d;
    --m.bv;
    return m.f;
  }
  
}




/* FUNCTION: sqrtf */

/* This code is *WRONG* in some circumstances, specifically:
 *
 *   1. If run with a rounding mode other than RNE the
 *      answer will be out by one or two ULP.  This could be fixed
 *      with careful choice of round mode for the multiplications.
 *
 *   2. Subnormals have the unusual property that there are
 *      multiple numbers that square to give them.  I.E. if
 *      f is subnormal then there are multiple f1 != f2 such that
 *      f1 * f1 == f == f2 * f2.  This code will return *a*
 *      square root of a subnormal input but not necessarily *the*
 *      square root (i.e. the real value of the square root rounded).
 */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado_nextUpf(float f);

float __VERIFIER_nondet_float(void);

float avocado_sqrtf(float f)
{
 __CPROVER_hide:;

  if ( f < 0.0f )
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f/0.0f; // NaN
#pragma CPROVER check pop
  else if (__CPROVER_isinff(f) ||   // +Inf only
           f == 0.0f          ||   // Includes -0
           __CPROVER_isnanf(f))
    return f;
  else if (__CPROVER_isnormalf(f))
  {
    float avocado_lower=__VERIFIER_nondet_float();
    __CPROVER_assume(lower > 0.0f);
    __CPROVER_assume(__CPROVER_isnormalf(lower));
    // Tighter bounds can be given but are dependent on the
    // number of exponent and significand bits.  Thus they are
    // given implicitly...

#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    float avocado_lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormalf(lowerSquare));

    float avocado_upper = avocado_nextUpf(lower);
    float avocado_upperSquare = upper * upper;  // Might be +Inf
#pragma CPROVER check pop

    // Restrict these to bound f and thus compute the possible
    // values for the square root.  Note that the lower bound
    // can be equal, this is important to catch edge cases such as
    // 0x1.fffffep+127f and relies on the smallest normal number
    // being a perfect square (which it will be for any sensible
    // bit width).
    __CPROVER_assume(lowerSquare <= f);
    __CPROVER_assume(f < upperSquare);

    // Select between them to work out which to return
    switch(avocado_fegetround())
    {
    case FE_TONEAREST :
      return (f - lowerSquare < upperSquare - f) ? lower : upper; break;
    case FE_UPWARD :
      return (f - lowerSquare == 0.0f) ? lower : upper; break;
    case FE_DOWNWARD : // Fall through
    case FE_TOWARDZERO :
      return (f - lowerSquare == 0.0f) ? lower : upper; break;
    default:;
      return __VERIFIER_nondet_float();
    }

  }
  else
  {
    //assert(fpclassify(f) == FP_SUBNORMAL);
    //assert(f > 0.0f);

    // With respect to the algebra of floating point number
    // all subnormals seem to be perfect squares, thus ...

    float avocado_root=__VERIFIER_nondet_float();
    __CPROVER_assume(root >= 0.0f);

    __CPROVER_assume(root * root == f);

    return root;
  }
}




/* FUNCTION: sqrt */

/* The same caveats as sqrtf apply */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado_nextUp(double d);

double __VERIFIER_nondet_double(void);

double avocado_sqrt(double d)
{
 __CPROVER_hide:;

  if ( d < 0.0 )
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0/0.0; // NaN
#pragma CPROVER check pop
  else if (__CPROVER_isinfd(d) ||   // +Inf only
           d == 0.0            ||   // Includes -0
           __CPROVER_isnand(d))
    return d;
  else if (__CPROVER_isnormald(d))
  {
    double avocado_lower=__VERIFIER_nondet_double();
    __CPROVER_assume(lower > 0.0);
    __CPROVER_assume(__CPROVER_isnormald(lower));

#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    double avocado_lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormald(lowerSquare));

    double avocado_upper = avocado_nextUp(lower);
    double avocado_upperSquare = upper * upper;  // Might be +Inf
#pragma CPROVER check pop

    __CPROVER_assume(lowerSquare <= d);
    __CPROVER_assume(d < upperSquare);

    switch(avocado_fegetround())
    {
    case FE_TONEAREST:
      return (d - lowerSquare < upperSquare - d) ? lower : upper; break;
    case FE_UPWARD:
      return (d - lowerSquare == 0.0f) ? lower : upper; break;
    case FE_DOWNWARD: // Fall through
    case FE_TOWARDZERO:
      return (d - lowerSquare == 0.0) ? lower : upper; break;
    default:;
      return __VERIFIER_nondet_double();
    }

  }
  else
  {
    //assert(fpclassify(d) == FP_SUBNORMAL);
    //assert(d > 0.0);

    double avocado_root=__VERIFIER_nondet_double();
    __CPROVER_assume(root >= 0.0);

    __CPROVER_assume(root * root == d);

    return root;
  }
}

/* FUNCTION: sqrtl */

/* The same caveats as sqrtf apply */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado_nextUpl(long double d);

long double __VERIFIER_nondet_long_double(void);

long double avocado_sqrtl(long double d)
{
 __CPROVER_hide:;

  if(d < 0.0l)
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0l/0.0l; // NaN
#pragma CPROVER check pop
  else if (__CPROVER_isinfld(d) ||   // +Inf only
           d == 0.0l            ||   // Includes -0
           __CPROVER_isnanld(d))
    return d;
  else if (__CPROVER_isnormalld(d))
  {
    long double avocado_lower=__VERIFIER_nondet_long_double();
    __CPROVER_assume(lower > 0.0l);
    __CPROVER_assume(__CPROVER_isnormalld(lower));

#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    long double avocado_lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormalld(lowerSquare));

    long double avocado_upper = avocado_nextUpl(lower);
    long double avocado_upperSquare = upper * upper;  // Might be +Inf
#pragma CPROVER check pop

    __CPROVER_assume(lowerSquare <= d);
    __CPROVER_assume(d < upperSquare);

    switch(avocado_fegetround())
    {
    case FE_TONEAREST:
      return (d - lowerSquare < upperSquare - d) ? lower : upper; break;
    case FE_UPWARD:
      return (d - lowerSquare == 0.0l) ? lower : upper; break;
    case FE_DOWNWARD: // Fall through
    case FE_TOWARDZERO:
      return (d - lowerSquare == 0.0l) ? lower : upper; break;
    default:;
      return __VERIFIER_nondet_long_double();
    }

  }
  else
  {
    //assert(fpclassify(d) == FP_SUBNORMAL);
    //assert(d > 0.0l);

    long double avocado_root=__VERIFIER_nondet_long_double();
    __CPROVER_assume(root >= 0.0l);

    __CPROVER_assume(root * root == d);

    return root;
  }
}


/* ISO 9899:2011
 * The fmax functions determine the maximum numeric value of their
 * arguments. 242)
 *
 * 242) NaN arguments are treated as missing data: if one argument is
 * a NaN and the other numeric, then the fmax functions choose the
 * numeric value. See F.10.9.2.
 *
 * - If just one argument is a NaN, the fmax functions return the other
 *   argument (if both arguments are NaNs, the functions return a NaN).
 * - The returned value is exact and is independent of the current
 *   rounding direction mode.
 * - The body of the fmax function might be 374)
 *       { return (isgreaterequal(x, y) || isnan(y)) ? x : y; }
 *
 * 374) Ideally, fmax would be sensitive to the sign of zero, for
 * example fmax(-0.0, +0.0) would return +0; however, implementation
 * in software might be impractical.
 */

/* FUNCTION: fmax */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
double avocado_fmax(double f, double g) { return ((f >= g) || avocado_isnan(g)) ? f : g; }

/* FUNCTION: fmaxf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
float avocado_fmaxf(float f, float g) { return ((f >= g) || avocado_isnan(g)) ? f : g; }

/* FUNCTION: fmaxl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
long double avocado_fmaxl(long double f, long double g) { return ((f >= g) || avocado_isnan(g)) ? f : g; }


/* ISO 9899:2011
 * The fmin functions determine the minimum numeric value of their
 * arguments.243)
 *
 * 243) The fmin functions are analogous to the fmax functions in
 * their treatment of NaNs.
 *
 * - The fmin functions are analogous to the fmax functions (see F.10.9.2).
 * - The returned value is exact and is independent of the current
 *   rounding direction mode.
 */

/* FUNCTION: fmin */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif
 
// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
double avocado_fmin(double f, double g) { return ((f <= g) || avocado_isnan(g)) ? f : g; }

/* FUNCTION: fminf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB 
float avocado_fminf(float f, float g) { return ((f <= g) || avocado_isnan(g)) ? f : g; }

/* FUNCTION: fminl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB 
long double avocado_fminl(long double f, long double g) { return ((f <= g) || avocado_isnan(g)) ? f : g; }


/* ISO 9899:2011
 * The fdim functions determine the positive difference between their
 * arguments:
 *     x - y if x > y
 *     +0    if x <= y
 * A range error may occur.
 */

/* FUNCTION: fdim */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

double avocado_fdim(double f, double g) { return ((f > g) ? f - g : +0.0); }


/* FUNCTION: fdimf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

float avocado_fdimf(float f, float g) { return ((f > g) ? f - g : +0.0f); }


/* FUNCTION: fdiml */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

long double avocado_fdiml(long double f, long double g) { return ((f > g) ? f - g : +0.0); }

/* ISO 9899:2011
 *
 * The ceil functions compute the smallest integer value not less than
 * x.
 */

/* FUNCTION: ceil */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado_ceil(double x)
{
  return __CPROVER_round_to_integrald(x, 2); // FE_UPWARD
}

/* FUNCTION: ceilf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado_ceilf(float x)
{
  return __CPROVER_round_to_integralf(x, 2); // FE_UPWARD
}


/* FUNCTION: ceill */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado_ceill(long double x)
{
  return __CPROVER_round_to_integralld(x, 2); // FE_UPWARD
}


/* ISO 9899:2011
 *
 * The floor functions compute the largest integer value not greater than x.
 */

/* FUNCTION: floor */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado_floor(double x)
{
  return __CPROVER_round_to_integrald(x, 1); // FE_DOWNWARD
}

/* FUNCTION: floorf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado_floorf(float x)
{
  return __CPROVER_round_to_integralf(x, 1); // FE_DOWNWARD
}


/* FUNCTION: floorl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado_floorl(long double x)
{
  return __CPROVER_round_to_integralld(x, 1); // FE_DOWNWARD
}


/* ISO 9899:2011
 *
 * The trunc functions round their argument to the integer value, in
 * floating format, nearest to but no larger in magnitude than the argument.
 */

/* FUNCTION: trunc */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado_trunc(double x)
{
  return __CPROVER_round_to_integrald(x, 3); // FE_TOWARDZERO
}

/* FUNCTION: truncf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado_truncf(float x)
{
  return __CPROVER_round_to_integralf(x, 3); // FE_TOWARDZERO
}


/* FUNCTION: truncl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado_truncl(long double x)
{
  return __CPROVER_round_to_integralld(x, 3); // FE_TOWARDZERO
}


/* ISO 9899:2011
 *
 * The round functions round their argument to the integer value, in
 * floating format, nearest to but no larger in magnitude than the argument.
 */

/* FUNCTION: round */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado_round(double x)
{
  return __CPROVER_round_to_integrald(x, 4); // RNA
}

/* FUNCTION: roundf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado_roundf(float x)
{
  return __CPROVER_round_to_integralf(x, 4); // RNA
}


/* FUNCTION: roundl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado_roundl(long double x)
{
  return __CPROVER_round_to_integralld(x, 4); // RNA
}



/* ISO 9899:2011
 *
 * The nearbyint functions round their argument to an integer value in
 * floating-point format, using the current rounding direction and
 * without raising the inexact floating-point exception.
 */

/* FUNCTION: nearbyint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

double avocado_nearbyint(double x)
{
  return __CPROVER_round_to_integrald(x, __CPROVER_rounding_mode);
}

/* FUNCTION: nearbyintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

float avocado_nearbyintf(float x)
{
  return __CPROVER_round_to_integralf(x, __CPROVER_rounding_mode);
}


/* FUNCTION: nearbyintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long double avocado_nearbyintl(long double x)
{
  return __CPROVER_round_to_integralld(x, __CPROVER_rounding_mode);
}



/* ISO 9899:2011
 *
 * The rint functions differ from the nearbyint functions (7.12.9.3)
 * only in that the rint functions may raise the inexact
 * floating-point exception if the result differs in value from the argument.
 */

/* FUNCTION: rint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

double avocado_rint(double x)
{
  return __CPROVER_round_to_integrald(x, __CPROVER_rounding_mode);
}

/* FUNCTION: rintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

float avocado_rintf(float x)
{
  return __CPROVER_round_to_integralf(x, __CPROVER_rounding_mode);
}

/* FUNCTION: rintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long double avocado_rintl(long double x)
{
  return __CPROVER_round_to_integralld(x, __CPROVER_rounding_mode);
}



/* ISO 9899:2011
 *
 * The lrint and llrint functions round their argument to the nearest
 * integer value, rounding according to the current rounding
 * direction. If the rounded value is outside the range of the return
 * type, the numeric result is unspecified and a domain error or range
 * error may occur.
 */

/* FUNCTION: lrint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long int avocado_lrint(double x)
{
  double avocado_rti = __CPROVER_round_to_integrald(x, __CPROVER_rounding_mode);
  return (long int)rti;
}

/* FUNCTION: lrintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long int avocado_lrintf(float x)
{
  float avocado_rti = __CPROVER_round_to_integralf(x, __CPROVER_rounding_mode);
  return (long int)rti;
}


/* FUNCTION: lrintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long int avocado_lrintl(long double x)
{
  long double avocado_rti = __CPROVER_round_to_integralld(x, __CPROVER_rounding_mode);
  return (long int)rti;
}


/* FUNCTION: llrint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long long int avocado_llrint(double x)
{
  double avocado_rti = __CPROVER_round_to_integrald(x, __CPROVER_rounding_mode);
  return (long long int)rti;
}

/* FUNCTION: llrintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long long int avocado_llrintf(float x)
{
  float avocado_rti = __CPROVER_round_to_integralf(x, __CPROVER_rounding_mode);
  return (long long int)rti;
}


/* FUNCTION: llrintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

extern int __CPROVER_rounding_mode;

long long int avocado_llrintl(long double x)
{
  long double avocado_rti = __CPROVER_round_to_integralld(x, __CPROVER_rounding_mode);
  return (long long int)rti;
}


/* ISO 9899:2011
 *
 * The lround and llround functions round their argument to the
 * nearest integer value, rounding halfway cases away from zero,
 * regardless of the current rounding direction. If the rounded value
 * is outside the range of the return type, the numeric result is
 * unspecified and a domain error or range error may occur.
 */

/* FUNCTION: lround */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long int avocado_lround(double x)
{
  double avocado_rti = __CPROVER_round_to_integrald(x, 4); // RNA
  return (long int)rti;
}

/* FUNCTION: lroundf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long int avocado_lroundf(float x)
{
  float avocado_rti = __CPROVER_round_to_integralf(x, 4); // RNA
  return (long int)rti;
}


/* FUNCTION: lroundl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long int avocado_lroundl(long double x)
{
  long double avocado_rti = __CPROVER_round_to_integralld(x, 4); // RNA
  return (long int)rti;
}


/* FUNCTION: llround */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long long int avocado_llround(double x)
{
  double avocado_rti = __CPROVER_round_to_integrald(x, 4); // RNA
  return (long long int)rti;
}

/* FUNCTION: llroundf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long long int avocado_llroundf(float x)
{
  float avocado_rti = __CPROVER_round_to_integralf(x, 4); // RNA
  return (long long int)rti;
}


/* FUNCTION: llroundl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long long int avocado_llroundl(long double x)
{
  long double avocado_rti = __CPROVER_round_to_integralld(x, 4); // RNA
  return (long long int)rti;
}


/* ISO 9899:2011
 *
 * The modf functions break the argument value into integral and
 * fractional parts, each of which has the same type and sign as the
 * argument. They store the integral part (in floating-point format)
 * in the object pointed to by iptr.
 */

/* FUNCTION: modf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado_modf(double x, double *iptr)
{
  *iptr = __CPROVER_round_to_integrald(x, 3); // FE_TOWARDZERO
  return (x - *iptr);
}

/* FUNCTION: modff */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado_modff(float x, float *iptr)
{
  *iptr = __CPROVER_round_to_integralf(x, 3); // FE_TOWARDZERO
  return (x - *iptr);
}


/* FUNCTION: modfl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado_modfl(long double x, long double *iptr)
{
  *iptr = __CPROVER_round_to_integralld(x, 3); // FE_TOWARDZERO
  return (x - *iptr);
}



/* FUNCTION: __sort_of_CPROVER_remainder */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

double avocado___sort_of_CPROVER_remainder (int rounding_mode, double x, double y)
{
  if (x == 0.0 || __CPROVER_isinfd(y))
    return x;

  // Extended precision helps... a bit...
  long double avocado_div = x/y;
  long double avocado_n = __CPROVER_round_to_integrald(rounding_mode, div);
  long double avocado_res = (-y * n) + x;   // TODO : FMA would be an improvement
  return res;
}

/* FUNCTION: __sort_of_CPROVER_remainderf */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

float avocado___sort_of_CPROVER_remainderf (int rounding_mode, float x, float y)
{
  if (x == 0.0f || __CPROVER_isinff(y))
    return x;

  // Extended precision helps... a bit...
  long double avocado_div = x/y;
  long double avocado_n = __CPROVER_round_to_integralf(rounding_mode, div);
  long double avocado_res = (-y * n) + x;   // TODO : FMA would be an improvement
  return res;
}

/* FUNCTION: __sort_of_CPROVER_remainderl */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

long double avocado___sort_of_CPROVER_remainderl (int rounding_mode, long double x, long double y)
{
  if (x == 0.0 || __CPROVER_isinfld(y))
    return x;

  // Extended precision helps... a bit...
  long double avocado_div = x/y;
  long double avocado_n = __CPROVER_round_to_integralld(rounding_mode, div);
  long double avocado_res = (-y * n) + x;   // TODO : FMA would be an improvement
  return res;
}



/* ISO 9899:2011
 *
 * The fmod functions return the value x - ny, for some
 * integer n such that, if y is nonzero, the result has the same sign
 * as x and magnitude less than the magnitude of y. If y is zero,
 * whether a domain error occurs or the fmod functions return zero is
 * implementation-defined.
 */

/* FUNCTION: fmod */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado_fmod(double x, double y)
{
  return __CPROVER_fmod(x, y);
}

/* FUNCTION: fmodf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado_fmodf(float x, float y)
{
  return __CPROVER_fmodf(x, y);
}

/* FUNCTION: fmodl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado_fmodl(long double x, long double y)
{
  return __CPROVER_fmodl(x, y);
}

/* ISO 9899:2011
 *
 * The remainder functions compute the remainder x REM y required by
 * IEC 60559.239)
 *
 * 239) "When y != 0, the remainder r = x REM y is defined regardless
 *      of the rounding mode by the  mathematical relation r = x - n
 *      y, where n is the integer nearest the exact value of x/y;
 *      whenever | n -  x/y | = 1/2, then n is even. If r = 0, its
 *      sign shall be that of x." This definition is applicable for
 *      all implementations.
 */

/* FUNCTION: remainder */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double avocado___sort_of_CPROVER_remainder (int rounding_mode, double x, double y);

double avocado_remainder(double x, double y) { return avocado___sort_of_CPROVER_remainder(FE_TONEAREST, x, y); }


/* FUNCTION: remainderf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float avocado___sort_of_CPROVER_remainderf (int rounding_mode, float x, float y);

float avocado_remainderf(float x, float y) { return avocado___sort_of_CPROVER_remainderf(FE_TONEAREST, x, y); }


/* FUNCTION: remainderl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double avocado___sort_of_CPROVER_remainderl (int rounding_mode, long double x, long double y);

long double avocado_remainderl(long double x, long double y) { return avocado___sort_of_CPROVER_remainderl(FE_TONEAREST, x, y); }




/* ISO 9899:2011
 * The copysign functions produce a value with the magnitude of x and
 * the sign of y. They produce a NaN (with the sign of y) if x is a
 * NaN. On implementations that represent a signed zero but do not
 * treat negative zero consistently in arithmetic operations, the
 * copysign functions regard the sign of zero as positive.
 */

/* FUNCTION: copysign */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

double avocado_fabs (double d);

double avocado_copysign(double x, double y)
{
  double avocado_abs = avocado_fabs(x);
  return (avocado_signbit(y)) ? -abs : abs;
}

/* FUNCTION: copysignf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

float avocado_fabsf (float d);

float avocado_copysignf(float x, float y)
{
  float avocado_abs = avocado_fabsf(x);
  return (avocado_signbit(y)) ? -abs : abs;
}

/* FUNCTION: copysignl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

long double avocado_fabsl (long double d);

long double avocado_copysignl(long double x, long double y)
{
  long double avocado_abs = avocado_fabsl(x);
  return (avocado_signbit(y)) ? -abs : abs;
}

/* FUNCTION: exp2 */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

double avocado_exp2(double x)
{
  return avocado_pow(2.0, x);
}

/* FUNCTION: exp2f */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

float avocado_exp2f(float x)
{
  return avocado_powf(2.0f, x);
}

/* FUNCTION: exp2l */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

long double avocado_exp2l(long double x)
{
  return avocado_powl(2.0l, x);
}

/* FUNCTION: exp */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

double avocado_exp(double x)
{
  if(__CPROVER_isnand(x) || (__CPROVER_isinfd(x) && !__CPROVER_signd(x)))
    return x;
  else if(__CPROVER_isinfd(x) && __CPROVER_signd(x))
    return +0.0;
  // underflow/overflow when the result is not representable in 11 exponent bits
  else if(x < -1024.0 * M_LN2)
  {
    errno = ERANGE;
    return 0.0;
  }
  else if(x > 1024.0 * M_LN2)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return HUGE_VAL;
#pragma CPROVER check pop
  }

  // Nicol N. Schraudolph: A Fast, Compact Approximation of the Exponential
  // Function. Neural Computation 11(4), 1999
  // https://schraudolph.org/pubs/Schraudolph99.pdf
  // 20 is 32 - 1 sign bit - 11 exponent bits
  int32_t avocado_bias = (1 << 20) * ((1 << 10) - 1);
  int32_t avocado_exp_a_x = (int32_t)(x / M_LN2 * (double)(1 << 20)) + bias;
  // EXP'C controls the approximation; the paper suggests 60801, but -1 yields
  // an upper bound and 90253 a lower bound, and we pick a value in between.
  int32_t avocado_lower = exp_a_x - 90253;
  int32_t avocado_upper = exp_a_x + 1;
  int32_t avocado_result = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(result >= lower);
  __CPROVER_assume(result <= upper);

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(double) == 2 * sizeof(int32_t),
     "bit width of double is 2x bit width of int32_t");
  union U
  {
    double d;
    int32_t i[2];
  };
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  union U avocado_u = {.i = {0, result}};
#else
  union U avocado_u = {.i = {result, 0}};
#endif
  return u.d;
}

/* FUNCTION: expf */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

float avocado_expf(float x)
{
  if(__CPROVER_isnanf(x) || (__CPROVER_isinff(x) && !__CPROVER_signf(x)))
    return x;
  else if(__CPROVER_isinff(x) && __CPROVER_signf(x))
    return +0.0f;
  // underflow/overflow when the result is not representable in 8 exponent bits
  else if(x < -128.0f * (float)M_LN2)
  {
    errno = ERANGE;
    return 0.0f;
  }
  else if(x > 128.0f * (float)M_LN2)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return HUGE_VALF;
#pragma CPROVER check pop
  }

  // 23 is 32 - 1 sign bit - 8 exponent bits
  int32_t avocado_bias = (1 << 23) * ((1 << 7) - 1);
  int32_t avocado_exp_a_x = (int32_t)(x / (float)M_LN2 * (float)(1 << 23)) + bias;
  // 722019 is 2^23 * [1 - [ln(ln(2)) + 1] / ln(2)] rounded up -- see Appendix
  // of Schraudolph's paper
  int32_t avocado_lower = exp_a_x - 722019;
  int32_t avocado_upper = exp_a_x + 1;
  int32_t avocado_result = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(result >= lower);
  __CPROVER_assume(result <= upper);

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(float) == sizeof(int32_t),
     "bit width of float and int32_t should match");
  union U
  {
    float f;
    int32_t i;
  };
  union U avocado_u = {.i = result};
  return u.f;
}

/* FUNCTION: expl */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FLOAT_H_INCLUDED
#  include <float.h>
#  define __CPROVER_FLOAT_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

long double avocado_expl(long double x)
{
  if(__CPROVER_isnanld(x) || (__CPROVER_isinfld(x) && !__CPROVER_signld(x)))
    return x;
  else if(__CPROVER_isinfld(x) && __CPROVER_signld(x))
    return +0.0l;

#if LDBL_MAX_EXP == DBL_MAX_EXP
  return avocado_exp(x);
#else
  // underflow/overflow when the result is not representable in 15 exponent bits
  if(x < -16384.0l * M_LN2)
  {
    errno = ERANGE;
    return 0.0l;
  }
  else if(x > 16384.0l * M_LN2)
  {
    errno = ERANGE;
#  pragma CPROVER check push
#  pragma CPROVER check disable "float-overflow"
    return HUGE_VALL;
#  pragma CPROVER check pop
  }
  // 16 is 32 - 1 sign bit - 15 exponent bits
  int32_t avocado_bias = (1 << 16) * ((1 << 14) - 1);
  int32_t avocado_exp_a_x = (int32_t)(x / M_LN2 * (long double)(1 << 16)) + bias;
  // 5641 is 2^16 * [1 - [ln(ln(2)) + 1] / ln(2)] rounded up -- see Appendix
  // of Schraudolph's paper
  int32_t avocado_lower = exp_a_x - 5641;
  int32_t avocado_upper = exp_a_x + 1;
  int32_t avocado_result = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(result >= lower);
  __CPROVER_assume(result <= upper);

#  ifndef _MSC_VER
  _Static_assert
#  else
  avocado_static_assert
#  endif
    (sizeof(long double) % sizeof(int32_t) == 0,
     "bit width of long double is a multiple of bit width of int32_t");
  union
  {
    long double l;
    int32_t i[sizeof(long double) / sizeof(int32_t)];
  } avocado_u = {.i = {0}};
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  u.i[sizeof(long double) / sizeof(int32_t) - 1] = result;
#  else
  u.i[0] = result;
#  endif
  return u.l;
#endif
}

/* FUNCTION: log */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

double avocado_log(double x)
{
  if(__CPROVER_isnand(x) || (__CPROVER_isinfd(x) && !__CPROVER_signd(x)))
    return x;
  else if(x == 1.0)
    return +0.0;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VAL;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signd(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0 / 0.0;
#pragma CPROVER check pop
  }

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(double) == 2 * sizeof(int32_t),
     "bit width of double is 2x bit width of int32_t");
  // https://martin.ankerl.com/2007/10/04/optimized-pow-approximation-for-java-and-c-c/
  union
  {
    double d;
    int32_t i[2];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 20) * ((1 << 10) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -90253 && exp_c <= 1);
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return ((double)u.i[1] - (double)(bias + exp_c)) * M_LN2 / (double)(1 << 20);
#else
  return ((double)u.i[0] - (double)(bias + exp_c)) * M_LN2 / (double)(1 << 20);
#endif
}

/* FUNCTION: logf */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

float avocado_logf(float x)
{
  if(__CPROVER_isnanf(x) || (__CPROVER_isinff(x) && !__CPROVER_signf(x)))
    return x;
  else if(x == 1.0f)
    return +0.0f;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VALF;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signf(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f / 0.0f;
#pragma CPROVER check pop
  }

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(float) == sizeof(int32_t),
     "bit width of float and int32_t should match");
  // https://martin.ankerl.com/2007/10/04/optimized-pow-approximation-for-java-and-c-c/
  union
  {
    float f;
    int32_t i;
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 23) * ((1 << 7) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -722019 && exp_c <= 1);
  return ((float)u.i - (float)(bias + exp_c)) * (float)M_LN2 / (float)(1 << 23);
}

/* FUNCTION: logl */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_FLOAT_H_INCLUDED
#  include <float.h>
#  define __CPROVER_FLOAT_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

long double avocado_logl(long double x)
{
  if(__CPROVER_isnanld(x) || (__CPROVER_isinfld(x) && !__CPROVER_signld(x)))
    return x;
  else if(x == 1.0l)
    return +0.0l;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VALL;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signld(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0l / 0.0l;
#pragma CPROVER check pop
  }

#if LDBL_MAX_EXP == DBL_MAX_EXP
  return avocado_log(x);
#else
#  ifndef _MSC_VER
  _Static_assert
#  else
  avocado_static_assert
#  endif
    (sizeof(long double) % sizeof(int32_t) == 0,
     "bit width of long double is a multiple of bit width of int32_t");
  union
  {
    long double l;
    int32_t i[sizeof(long double) / sizeof(int32_t)];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 16) * ((1 << 14) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -5641 && exp_c <= 1);
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return ((long double)u.i[sizeof(long double) / sizeof(int32_t) - 1] -
          (long double)(bias + exp_c)) *
         M_LN2 / (long double)(1 << 16);
#  else
  return ((long double)u.i[0] - (long double)(bias + exp_c)) * M_LN2 /
         (long double)(1 << 16);
#  endif
#endif
}

/* FUNCTION: log2 */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

double avocado_log2(double x)
{
  if(__CPROVER_isnand(x) || (__CPROVER_isinfd(x) && !__CPROVER_signd(x)))
    return x;
  else if(x == 1.0)
    return +0.0;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VAL;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signd(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0 / 0.0;
#pragma CPROVER check pop
  }

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(double) == 2 * sizeof(int32_t),
     "bit width of double is 2x bit width of int32_t");
  union
  {
    double d;
    int32_t i[2];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 20) * ((1 << 10) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -90253 && exp_c <= 1);
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return ((double)u.i[1] - (double)(bias + exp_c)) / (double)(1 << 20);
#else
  return ((double)u.i[0] - (double)(bias + exp_c)) / (double)(1 << 20);
#endif
}

/* FUNCTION: log2f */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

float avocado_log2f(float x)
{
  if(__CPROVER_isnanf(x) || (__CPROVER_isinff(x) && !__CPROVER_signf(x)))
    return x;
  else if(x == 1.0f)
    return +0.0f;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VALF;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signf(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f / 0.0f;
#pragma CPROVER check pop
  }

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(float) == sizeof(int32_t),
     "bit width of float and int32_t should match");
  union
  {
    float f;
    int32_t i;
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 23) * ((1 << 7) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -722019 && exp_c <= 1);
  return ((float)u.i - (float)(bias + exp_c)) / (float)(1 << 23);
}

/* FUNCTION: log2l */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_FLOAT_H_INCLUDED
#  include <float.h>
#  define __CPROVER_FLOAT_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

long double avocado_log2l(long double x)
{
  if(__CPROVER_isnanld(x) || (__CPROVER_isinfld(x) && !__CPROVER_signld(x)))
    return x;
  else if(x == 1.0l)
    return +0.0l;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VALL;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signld(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0l / 0.0l;
#pragma CPROVER check pop
  }

#if LDBL_MAX_EXP == DBL_MAX_EXP
  return avocado_log2(x);
#else
#  ifndef _MSC_VER
  _Static_assert
#  else
  avocado_static_assert
#  endif
    (sizeof(long double) % sizeof(int32_t) == 0,
     "bit width of long double is a multiple of bit width of int32_t");
  union
  {
    long double l;
    int32_t i[sizeof(long double) / sizeof(int32_t)];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 16) * ((1 << 14) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -5641 && exp_c <= 1);
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return ((long double)u.i[sizeof(long double) / sizeof(int32_t) - 1] -
          (long double)(bias + exp_c)) /
         (long double)(1 << 16);
#  else
  return ((long double)u.i[0] - (long double)(bias + exp_c)) /
         (long double)(1 << 16);
#  endif
#endif
}

/* FUNCTION: log10 */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

double avocado_log10(double x)
{
  if(__CPROVER_isnand(x) || (__CPROVER_isinfd(x) && !__CPROVER_signd(x)))
    return x;
  else if(x == 1.0)
    return +0.0;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VAL;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signd(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0 / 0.0;
#pragma CPROVER check pop
  }

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(double) == 2 * sizeof(int32_t),
     "bit width of double is 2x bit width of int32_t");
  // https://martin.ankerl.com/2007/10/04/optimized-pow-approximation-for-java-and-c-c/
  union
  {
    double d;
    int32_t i[2];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 20) * ((1 << 10) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -90253 && exp_c <= 1);
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return ((double)u.i[1] - (double)(bias + exp_c)) * (M_LN2 / M_LN10) /
         (double)(1 << 20);
#else
  return ((double)u.i[0] - (double)(bias + exp_c)) * (M_LN2 / M_LN10) /
         (double)(1 << 20);
#endif
}

/* FUNCTION: log10f */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

float avocado_log10f(float x)
{
  if(__CPROVER_isnanf(x) || (__CPROVER_isinff(x) && !__CPROVER_signf(x)))
    return x;
  else if(x == 1.0f)
    return +0.0f;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VALF;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signf(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f / 0.0f;
#pragma CPROVER check pop
  }

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(float) == sizeof(int32_t),
     "bit width of float and int32_t should match");
  // https://martin.ankerl.com/2007/10/04/optimized-pow-approximation-for-java-and-c-c/
  union
  {
    float f;
    int32_t i;
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 23) * ((1 << 7) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -722019 && exp_c <= 1);
  return ((float)u.i - (float)(bias + exp_c)) * (float)(M_LN2 / M_LN10) /
         (float)(1 << 23);
}

/* FUNCTION: log10l */

#ifndef __CPROVER_MATH_H_INCLUDED
#  ifdef _WIN32
#    define _USE_MATH_DEFINES
#  endif
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

#ifndef __CPROVER_FLOAT_H_INCLUDED
#  include <float.h>
#  define __CPROVER_FLOAT_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

long double avocado_log10l(long double x)
{
  if(__CPROVER_isnanld(x) || (__CPROVER_isinfld(x) && !__CPROVER_signld(x)))
    return x;
  else if(x == 1.0l)
    return +0.0l;
  else if(fpclassify(x) == FP_ZERO)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return -HUGE_VALL;
#pragma CPROVER check pop
  }
  else if(__CPROVER_signld(x))
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0l / 0.0l;
#pragma CPROVER check pop
  }

#if LDBL_MAX_EXP == DBL_MAX_EXP
  return avocado_log10(x);
#else
#  ifndef _MSC_VER
  _Static_assert
#  else
  avocado_static_assert
#  endif
    (sizeof(long double) % sizeof(int32_t) == 0,
     "bit width of long double is a multiple of bit width of int32_t");
  union
  {
    long double l;
    int32_t i[sizeof(long double) / sizeof(int32_t)];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 16) * ((1 << 14) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -5641 && exp_c <= 1);
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return ((long double)u.i[sizeof(long double) / sizeof(int32_t) - 1] -
          (long double)(bias + exp_c)) *
         (M_LN2 / M_LN10) / (long double)(1 << 16);
#  else
  return ((long double)u.i[0] - (long double)(bias + exp_c)) *
         (M_LN2 / M_LN10) / (long double)(1 << 16);
#  endif
#endif
}

/* FUNCTION: pow */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

double avocado___builtin_inf(void);

double avocado_pow(double x, double y)
{
  // see man pow (https://linux.die.net/man/3/pow)
  if(
    __CPROVER_isfinited(x) && __CPROVER_signd(x) && __CPROVER_isfinited(y) &&
    avocado_nearbyint(y) != y)
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0 / 0.0;
#pragma CPROVER check pop
  }
  else if(x == 1.0)
    return 1.0;
  else if(fpclassify(y) == FP_ZERO)
    return 1.0;
  else if(fpclassify(x) == FP_ZERO && !__CPROVER_signd(y))
  {
    if(avocado_nearbyint(y) == y && avocado_fabs(avocado_fmod(y, 2.0)) == 1.0)
      return x;
    else
      return +0.0;
  }
  else if(avocado_isinf(y))
  {
    // x == 1.0 and y-is-zero caught above
    if(x == -1.0)
      return 1.0;
    else if(__CPROVER_signd(y))
    {
      if(avocado_fabs(x) < 1.0)
        return avocado___builtin_inf();
      else
        return +0.0;
    }
    else
    {
      if(avocado_fabs(x) < 1.0)
        return +0.0;
      else
        return avocado___builtin_inf();
    }
  }
  else if(avocado_isinf(x) && __CPROVER_signd(x))
  {
    if(__CPROVER_signd(y))
    {
      if(avocado_nearbyint(y) == y && avocado_fabs(avocado_fmod(y, 2.0)) == 1.0)
        return -0.0;
      else
        return +0.0;
    }
    else
    {
      if(avocado_nearbyint(y) == y && avocado_fabs(avocado_fmod(y, 2.0)) == 1.0)
        return -avocado___builtin_inf();
      else
        return avocado___builtin_inf();
    }
  }
  else if(avocado_isinf(x) && !__CPROVER_signd(x))
  {
    if(__CPROVER_signd(y))
      return +0.0;
    else
      return avocado___builtin_inf();
  }
  else if(fpclassify(x) == FP_ZERO && __CPROVER_signd(y))
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    if(__CPROVER_signd(x) && avocado_nearbyint(y) == y && avocado_fabs(avocado_fmod(y, 2.0)) == 1.0)
      return -HUGE_VAL;
    else
      return HUGE_VAL;
#pragma CPROVER check pop
  }
  else if(avocado_isnan(x) || avocado_isnan(y))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0 / 0.0;
#pragma CPROVER check pop

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(double) == 2 * sizeof(int32_t),
     "bit width of double is 2x bit width of int32_t");
  // https://martin.ankerl.com/2007/10/04/optimized-pow-approximation-for-java-and-c-c/
  union
  {
    double d;
    int32_t i[2];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 20) * ((1 << 10) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -90253 && exp_c <= 1);
#pragma CPROVER check push
#pragma CPROVER check disable "signed-overflow"
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  double avocado_mult_result = y * (double)(u.i[1] - (bias + exp_c));
#else
  double avocado_mult_result = y * (double)(u.i[0] - (bias + exp_c));
#endif
#pragma CPROVER check pop
  if(avocado_fabs(mult_result) > (double)(1 << 30))
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return y > 0.0 ? HUGE_VAL : 0.0;
#pragma CPROVER check pop
  }
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  u.i[1] = (int32_t)mult_result + (bias + exp_c);
  u.i[0] = 0;
#else
  u.i[0] = (int32_t)mult_result + (bias + exp_c);
  u.i[1] = 0;
#endif
  return u.d;
}

/* FUNCTION: powf */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

float avocado___builtin_inff(void);

float avocado_powf(float x, float y)
{
  // see man pow (https://linux.die.net/man/3/pow)
  if(
    __CPROVER_isfinitef(x) && __CPROVER_signf(x) && __CPROVER_isfinitef(y) &&
    avocado_nearbyintf(y) != y)
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f / 0.0f;
#pragma CPROVER check pop
  }
  else if(x == 1.0f)
    return 1.0f;
  else if(fpclassify(y) == FP_ZERO)
    return 1.0f;
  else if(fpclassify(x) == FP_ZERO && !__CPROVER_signf(y))
  {
    if(avocado_nearbyintf(y) == y && avocado_fabsf(avocado_fmodf(y, 2.0f)) == 1.0f)
      return x;
    else
      return +0.0f;
  }
  else if(avocado_isinff(y))
  {
    // x == 1.0f and y-is-zero caught above
    if(x == -1.0f)
      return 1.0f;
    else if(__CPROVER_signf(y))
    {
      if(avocado_fabsf(x) < 1.0f)
        return avocado___builtin_inff();
      else
        return +0.0f;
    }
    else
    {
      if(avocado_fabsf(x) < 1.0f)
        return +0.0f;
      else
        return avocado___builtin_inff();
    }
  }
  else if(avocado_isinff(x) && __CPROVER_signf(x))
  {
    if(__CPROVER_signf(y))
    {
      if(avocado_nearbyintf(y) == y && avocado_fabsf(avocado_fmodf(y, 2.0f)) == 1.0f)
        return -0.0f;
      else
        return +0.0f;
    }
    else
    {
      if(avocado_nearbyintf(y) == y && avocado_fabsf(avocado_fmodf(y, 2.0f)) == 1.0f)
        return -avocado___builtin_inff();
      else
        return avocado___builtin_inff();
    }
  }
  else if(avocado_isinff(x) && !__CPROVER_signf(x))
  {
    if(__CPROVER_signf(y))
      return +0.0f;
    else
      return avocado___builtin_inff();
  }
  else if(fpclassify(x) == FP_ZERO && __CPROVER_signf(y))
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    if(
      __CPROVER_signf(x) && avocado_nearbyintf(y) == y && avocado_fabsf(avocado_fmodf(y, 2.0f)) == 1.0f)
    {
      return -HUGE_VALF;
    }
    else
      return HUGE_VALF;
#pragma CPROVER check pop
  }
  else if(avocado_isnanf(x) || avocado_isnanf(y))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f / 0.0f;
#pragma CPROVER check pop

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(float) == sizeof(int32_t),
     "bit width of float and int32_t should match");
  union
  {
    float f;
    int32_t i;
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 23) * ((1 << 7) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -722019 && exp_c <= 1);
#pragma CPROVER check push
#pragma CPROVER check disable "signed-overflow"
  float avocado_mult_result = y * (float)(u.i - (bias + exp_c));
#pragma CPROVER check pop
  if(avocado_fabsf(mult_result) > (float)(1 << 30))
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return y > 0.0f ? HUGE_VALF : 0.0f;
#pragma CPROVER check pop
  }
  u.i = (int32_t)mult_result + (bias + exp_c);
  return u.f;
}

/* FUNCTION: powl */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FLOAT_H_INCLUDED
#  include <float.h>
#  define __CPROVER_FLOAT_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

long double avocado___builtin_infl(void);

long double avocado_powl(long double x, long double y)
{
  // see man pow (https://linux.die.net/man/3/pow)
  if(
    __CPROVER_isfiniteld(x) && __CPROVER_signld(x) && __CPROVER_isfiniteld(y) &&
    avocado_nearbyintl(y) != y)
  {
    errno = EDOM;
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0l / 0.0l;
#pragma CPROVER check pop
  }
  else if(x == 1.0l)
    return 1.0l;
  else if(fpclassify(y) == FP_ZERO)
    return 1.0l;
  else if(fpclassify(x) == FP_ZERO && !__CPROVER_signld(y))
  {
    if(avocado_nearbyintl(y) == y && avocado_fabsl(avocado_fmodl(y, 2.0l)) == 1.0l)
      return x;
    else
      return +0.0l;
  }
  else if(avocado_isinfl(y))
  {
    // x == 1.0l and y-is-zero caught above
    if(x == -1.0l)
      return 1.0l;
    else if(__CPROVER_signld(y))
    {
      if(avocado_fabsl(x) < 1.0l)
        return avocado___builtin_infl();
      else
        return +0.0l;
    }
    else
    {
      if(avocado_fabsl(x) < 1.0l)
        return +0.0l;
      else
        return avocado___builtin_infl();
    }
  }
  else if(avocado_isinfl(x) && __CPROVER_signld(x))
  {
    if(__CPROVER_signld(y))
    {
      if(avocado_nearbyintl(y) == y && avocado_fabsl(avocado_fmodl(y, 2.0l)) == 1.0l)
        return -0.0l;
      else
        return +0.0l;
    }
    else
    {
      if(avocado_nearbyintl(y) == y && avocado_fabsl(avocado_fmodl(y, 2.0l)) == 1.0l)
        return -avocado___builtin_infl();
      else
        return avocado___builtin_infl();
    }
  }
  else if(avocado_isinfl(x) && !__CPROVER_signld(x))
  {
    if(__CPROVER_signld(y))
      return +0.0f;
    else
      return avocado___builtin_infl();
  }
  else if(fpclassify(x) == FP_ZERO && __CPROVER_signld(y))
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    if(
      __CPROVER_signld(x) && avocado_nearbyintl(y) == y &&
      avocado_fabsl(avocado_fmodl(y, 2.0l)) == 1.0l)
    {
      return -HUGE_VALL;
    }
    else
      return HUGE_VALL;
#pragma CPROVER check pop
  }
  else if(avocado_isnanl(x) || avocado_isnanl(y))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0l / 0.0l;
#pragma CPROVER check pop

#if LDBL_MAX_EXP == DBL_MAX_EXP
  return avocado_pow(x, y);
#else
#  ifndef _MSC_VER
  _Static_assert
#  else
  avocado_static_assert
#  endif
    (sizeof(long double) % sizeof(int32_t) == 0,
     "bit width of long double is a multiple of bit width of int32_t");
  union U
  {
    long double l;
    int32_t i[sizeof(long double) / sizeof(int32_t)];
  } avocado_u = {x};
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  int32_t avocado_exponent = u.i[sizeof(long double) / sizeof(int32_t) - 1];
#  else
  int32_t avocado_exponent = u.i[0];
#  endif
  int32_t avocado_bias = (1 << 16) * ((1 << 14) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -5641 && exp_c <= 1);
#  pragma CPROVER check push
#  pragma CPROVER check disable "signed-overflow"
  long double avocado_mult_result = y * (long double)(exponent - (bias + exp_c));
#  pragma CPROVER check pop
  if(avocado_fabsl(mult_result) > (long double)(1 << 30))
  {
    errno = ERANGE;
#  pragma CPROVER check push
#  pragma CPROVER check disable "float-overflow"
    return y > 0.0l ? HUGE_VALL : 0.0l;
#  pragma CPROVER check pop
  }
  int32_t avocado_result = (int32_t)mult_result + (bias + exp_c);
  union U avocado_result_u = {.i = {0}};
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  result_u.i[sizeof(long double) / sizeof(int32_t) - 1] = result;
#  else
  result_u.i[0] = result;
#  endif
  return result_u.l;
#endif
}

/* FUNCTION: fma */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#  include <fenv.h>
#  define __CPROVER_FENV_H_INCLUDED
#endif

double avocado___builtin_inf(void);

double avocado_fma(double x, double y, double z)
{
  // see man fma (https://linux.die.net/man/3/fma)
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  if(avocado_isnan(x) || avocado_isnan(y))
    return 0.0 / 0.0;
  else if(
    (avocado_isinf(x) || avocado_isinf(y)) &&
    (fpclassify(x) == FP_ZERO || fpclassify(y) == FP_ZERO))
  {
    avocado_feraiseexcept(FE_INVALID);
    return 0.0 / 0.0;
  }
  else if(avocado_isnan(z))
    return 0.0 / 0.0;

#pragma CPROVER check disable "float-overflow"
  double avocado_x_times_y = x * y;
  if(
    avocado_isinf(x_times_y) && avocado_isinf(z) &&
    __CPROVER_signd(x_times_y) != __CPROVER_signd(z))
  {
    avocado_feraiseexcept(FE_INVALID);
    return 0.0 / 0.0;
  }
#pragma CPROVER check pop

  if(avocado_isinf(x_times_y))
  {
    avocado_feraiseexcept(FE_OVERFLOW);
    return __CPROVER_signd(x_times_y) ? -avocado___builtin_inf() : avocado___builtin_inf();
  }
  // TODO: detect underflow (FE_UNDERFLOW), return +/- 0

  return x_times_y + z;
}

/* FUNCTION: fmaf */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#  include <fenv.h>
#  define __CPROVER_FENV_H_INCLUDED
#endif

float avocado___builtin_inff(void);

float avocado_fmaf(float x, float y, float z)
{
  // see man fma (https://linux.die.net/man/3/fma)
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  if(avocado_isnanf(x) || avocado_isnanf(y))
    return 0.0f / 0.0f;
  else if(
    (avocado_isinff(x) || avocado_isinff(y)) &&
    (fpclassify(x) == FP_ZERO || fpclassify(y) == FP_ZERO))
  {
    avocado_feraiseexcept(FE_INVALID);
    return 0.0f / 0.0f;
  }
  else if(avocado_isnanf(z))
    return 0.0f / 0.0f;

#pragma CPROVER check disable "float-overflow"
  float avocado_x_times_y = x * y;
  if(
    avocado_isinff(x_times_y) && avocado_isinff(z) &&
    __CPROVER_signf(x_times_y) != __CPROVER_signf(z))
  {
    avocado_feraiseexcept(FE_INVALID);
    return 0.0f / 0.0f;
  }
#pragma CPROVER check pop

  if(avocado_isinff(x_times_y))
  {
    avocado_feraiseexcept(FE_OVERFLOW);
    return __CPROVER_signf(x_times_y) ? -avocado___builtin_inff() : avocado___builtin_inff();
  }
  // TODO: detect underflow (FE_UNDERFLOW), return +/- 0

  return x_times_y + z;
}

/* FUNCTION: fmal */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#  include <fenv.h>
#  define __CPROVER_FENV_H_INCLUDED
#endif

#ifndef __CPROVER_FLOAT_H_INCLUDED
#  include <float.h>
#  define __CPROVER_FLOAT_H_INCLUDED
#endif

long double avocado___builtin_infl(void);

long double avocado_fmal(long double x, long double y, long double z)
{
  // see man fma (https://linux.die.net/man/3/fma)
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
  if(avocado_isnanl(x) || avocado_isnanl(y))
    return 0.0l / 0.0l;
  else if(
    (avocado_isinfl(x) || avocado_isinfl(y)) &&
    (fpclassify(x) == FP_ZERO || fpclassify(y) == FP_ZERO))
  {
    avocado_feraiseexcept(FE_INVALID);
    return 0.0l / 0.0l;
  }
  else if(avocado_isnanl(z))
    return 0.0l / 0.0l;

#pragma CPROVER check disable "float-overflow"
  long double avocado_x_times_y = x * y;
  if(
    avocado_isinfl(x_times_y) && avocado_isinfl(z) &&
    __CPROVER_signld(x_times_y) != __CPROVER_signld(z))
  {
    avocado_feraiseexcept(FE_INVALID);
    return 0.0l / 0.0l;
  }
#pragma CPROVER check pop

#if LDBL_MAX_EXP == DBL_MAX_EXP
  return avocado_fma(x, y, z);
#else
  if(avocado_isinfl(x_times_y))
  {
    avocado_feraiseexcept(FE_OVERFLOW);
    return __CPROVER_signld(x_times_y) ? -avocado___builtin_infl() : avocado___builtin_infl();
  }
  // TODO: detect underflow (FE_UNDERFLOW), return +/- 0

  return x_times_y + z;
#endif
}

/* FUNCTION: __builtin_powi */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

double avocado___builtin_inf(void);

double avocado___builtin_powi(double x, int y)
{
  // see man pow (https://linux.die.net/man/3/pow), specialized for y being an
  // integer
  if(x == 1.0)
    return 1.0;
  else if(y == 0)
    return 1.0;
  else if(fpclassify(x) == FP_ZERO && y > 0)
  {
    if(y % 2 == 1)
      return x;
    else
      return +0.0;
  }
  else if(avocado_isinf(x) && __CPROVER_signd(x))
  {
    if(y < 0)
    {
      if(-y % 2 == 1)
        return -0.0;
      else
        return +0.0;
    }
    else
    {
      if(y % 2 == 1)
        return -avocado___builtin_inf();
      else
        return avocado___builtin_inf();
    }
  }
  else if(avocado_isinf(x) && !__CPROVER_signd(x))
  {
    if(y < 0)
      return +0.0;
    else
      return avocado___builtin_inf();
  }
  else if(fpclassify(x) == FP_ZERO && y < 0)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    if(__CPROVER_signd(x) && -y % 2 == 1)
      return -HUGE_VAL;
    else
      return HUGE_VAL;
#pragma CPROVER check pop
  }
  else if(avocado_isnan(x))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0 / 0.0;
#pragma CPROVER check pop

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(double) == 2 * sizeof(int32_t),
     "bit width of double is 2x bit width of int32_t");
  // https://martin.ankerl.com/2007/10/04/optimized-pow-approximation-for-java-and-c-c/
  union
  {
    double d;
    int32_t i[2];
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 20) * ((1 << 10) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -90253 && exp_c <= 1);
#pragma CPROVER check push
#pragma CPROVER check disable "signed-overflow"
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  double avocado_mult_result = (double)(y) * (double)(u.i[1] - (bias + exp_c));
#else
  double avocado_mult_result = (double)(y) * (double)(u.i[0] - (bias + exp_c));
#endif
#pragma CPROVER check pop
  if(avocado_fabs(mult_result) > (double)(1 << 30))
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return y > 0 ? HUGE_VAL : 0.0;
#pragma CPROVER check pop
  }
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  u.i[1] = (int32_t)mult_result + (bias + exp_c);
  u.i[0] = 0;
#else
  u.i[0] = (int32_t)mult_result + (bias + exp_c);
  u.i[1] = 0;
#endif
  return u.d;
}

/* FUNCTION: __builtin_powif */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

float avocado___builtin_inff(void);

float avocado___builtin_powif(float x, int y)
{
  // see man pow (https://linux.die.net/man/3/pow), specialized for y being an
  // integer
  if(x == 1.0f)
    return 1.0f;
  else if(y == 0)
    return 1.0f;
  else if(fpclassify(x) == FP_ZERO && y > 0)
  {
    if(y % 2 == 1)
      return x;
    else
      return +0.0f;
  }
  else if(avocado_isinff(x) && __CPROVER_signf(x))
  {
    if(y < 0)
    {
      if(-y % 2 == 1)
        return -0.0f;
      else
        return +0.0f;
    }
    else
    {
      if(y % 2 == 1)
        return -avocado___builtin_inff();
      else
        return avocado___builtin_inff();
    }
  }
  else if(avocado_isinff(x) && !__CPROVER_signf(x))
  {
    if(y < 0)
      return +0.0f;
    else
      return avocado___builtin_inff();
  }
  else if(fpclassify(x) == FP_ZERO && y < 0)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    if(__CPROVER_signf(x) && -y % 2 == 1)
    {
      return -HUGE_VALF;
    }
    else
      return HUGE_VALF;
#pragma CPROVER check pop
  }
  else if(avocado_isnanf(x))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0f / 0.0f;
#pragma CPROVER check pop

#ifndef _MSC_VER
  _Static_assert
#else
  avocado_static_assert
#endif
    (sizeof(float) == sizeof(int32_t),
     "bit width of float and int32_t should match");
  union
  {
    float f;
    int32_t i;
  } avocado_u = {x};
  int32_t avocado_bias = (1 << 23) * ((1 << 7) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -722019 && exp_c <= 1);
#pragma CPROVER check push
#pragma CPROVER check disable "signed-overflow"
  float avocado_mult_result = (float)(y) * (float)(u.i - (bias + exp_c));
#pragma CPROVER check pop
  if(avocado_fabsf(mult_result) > (float)(1 << 30))
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    return y > 0 ? HUGE_VALF : 0.0f;
#pragma CPROVER check pop
  }
  u.i = (int32_t)mult_result + (bias + exp_c);
  return u.f;
}

/* FUNCTION: __builtin_powil */

#ifndef __CPROVER_MATH_H_INCLUDED
#  include <math.h>
#  define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FLOAT_H_INCLUDED
#  include <float.h>
#  define __CPROVER_FLOAT_H_INCLUDED
#endif

#ifndef __CPROVER_STDINT_H_INCLUDED
#  include <stdint.h>
#  define __CPROVER_STDINT_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int32_t __VERIFIER_nondet_int32_t(void);

long double avocado___builtin_infl(void);
double avocado___builtin_powi(double, int);

long double avocado___builtin_powil(long double x, int y)
{
  // see man pow (https://linux.die.net/man/3/pow), specialized for y being an
  // integer
  if(x == 1.0l)
    return 1.0l;
  else if(y == 0)
    return 1.0l;
  else if(fpclassify(x) == FP_ZERO && y > 0)
  {
    if(y % 2 == 1)
      return x;
    else
      return +0.0l;
  }
  else if(avocado_isinf(x) && __CPROVER_signld(x))
  {
    if(y < 0)
    {
      if(-y % 2 == 1)
        return -0.0l;
      else
        return +0.0l;
    }
    else
    {
      if(y % 2 == 1)
        return -avocado___builtin_infl();
      else
        return avocado___builtin_infl();
    }
  }
  else if(avocado_isinf(x) && !__CPROVER_signld(x))
  {
    if(y < 0)
      return +0.0f;
    else
      return avocado___builtin_infl();
  }
  else if(fpclassify(x) == FP_ZERO && y < 0)
  {
    errno = ERANGE;
#pragma CPROVER check push
#pragma CPROVER check disable "float-overflow"
    if(__CPROVER_signld(x) && -y % 2 == 1)
    {
      return -HUGE_VALL;
    }
    else
      return HUGE_VALL;
#pragma CPROVER check pop
  }
  else if(avocado_isnan(x))
#pragma CPROVER check push
#pragma CPROVER check disable "float-div-by-zero"
    return 0.0l / 0.0l;
#pragma CPROVER check pop

#if LDBL_MAX_EXP == DBL_MAX_EXP
  return avocado___builtin_powi(x, y);
#else
#  ifndef _MSC_VER
  _Static_assert
#  else
  avocado_static_assert
#  endif
    (sizeof(long double) % sizeof(int32_t) == 0,
     "bit width of long double is a multiple of bit width of int32_t");
  union U
  {
    long double l;
    int32_t i[sizeof(long double) / sizeof(int32_t)];
  } avocado_u = {x};
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  int32_t avocado_exponent = u.i[sizeof(long double) / sizeof(int32_t) - 1];
#  else
  int32_t avocado_exponent = u.i[0];
#  endif
  int32_t avocado_bias = (1 << 16) * ((1 << 14) - 1);
  int32_t avocado_exp_c = __VERIFIER_nondet_int32_t();
  __CPROVER_assume(exp_c >= -5641 && exp_c <= 1);
#  pragma CPROVER check push
#  pragma CPROVER check disable "signed-overflow"
  long double avocado_mult_result =
    (long double)y * (long double)(exponent - (bias + exp_c));
#  pragma CPROVER check pop
  if(avocado_fabsl(mult_result) > (long double)(1 << 30))
  {
    errno = ERANGE;
#  pragma CPROVER check push
#  pragma CPROVER check disable "float-overflow"
    return y > 0 ? HUGE_VALL : 0.0l;
#  pragma CPROVER check pop
  }
  int32_t avocado_result = (int32_t)mult_result + (bias + exp_c);
  union U avocado_result_u = {.i = {0}};
#  if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  result_u.i[sizeof(long double) / sizeof(int32_t) - 1] = result;
#  else
  result_u.i[0] = result;
#  endif
  return result_u.l;
#endif
}
