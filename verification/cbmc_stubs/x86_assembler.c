
/* FUNCTION: __asm_fnstcw */

extern int __CPROVER_rounding_mode;

void avocado___asm_fnstcw(void *dest)
{
  // the rounding mode is bits 10 and 11 in the control word
  *(unsigned short *)dest = __CPROVER_rounding_mode << 10;
}

/* FUNCTION: __asm_fstcw */

extern int __CPROVER_rounding_mode;

void avocado___asm_fstcw(void *dest)
{
  // the rounding mode is bits 10 and 11 in the control word
  *(unsigned short *)dest = __CPROVER_rounding_mode << 10;
}

/* FUNCTION: __asm_fldcw */

extern int __CPROVER_rounding_mode;

void avocado___asm_fldcw(void *src)
{
  // the rounding mode is bits 10 and 11 in the control word
  __CPROVER_rounding_mode = ((*(const unsigned short *)src) >> 10) & 3;
}

/* FUNCTION: __asm_mfence */

void avocado___asm_mfence(void)
{
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: __asm_sfence */

void avocado___asm_sfence(void)
{
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}

/* FUNCTION: __asm_lfence */

void avocado___asm_lfence(void)
{
  __CPROVER_fence("WWfence", "RRfence", "RWfence", "WRfence");
}
