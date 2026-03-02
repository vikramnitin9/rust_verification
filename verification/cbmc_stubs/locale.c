
/* FUNCTION: setlocale */

#ifndef __CPROVER_LOCALE_H_INCLUDED
#include <locale.h>
#define __CPROVER_LOCALE_H_INCLUDED
#endif

char *avocado_setlocale(int category, const char *locale)
{
  __CPROVER_HIDE:;
  (void)category;
  (void)*locale;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "setlocale_result");
  char *avocado_setlocale_result;
  __CPROVER_set_may(setlocale_result, "setlocale_result");
  return setlocale_result;
  #else
  static char avocado_setlocale_result[1];
  return setlocale_result;
  #endif
}

/* FUNCTION: localeconv */

#ifndef __CPROVER_LOCALE_H_INCLUDED
#include <locale.h>
#define __CPROVER_LOCALE_H_INCLUDED
#endif

struct lconv *avocado_localeconv(void)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "localeconv_result");
  struct lconv *avocado_localeconv_result;
  __CPROVER_set_may(localeconv_result, "localeconv_result");
  return localeconv_result;
  #else
  static struct lconv avocado_localeconv_result;
  return &localeconv_result;
  #endif
}
