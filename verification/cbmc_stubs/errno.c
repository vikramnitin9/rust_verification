/* FUNCTION: __error */

// This is used on MacOS to return the address of a
// variable used for the errno macro.

__CPROVER_thread_local int __CPROVER_errno;

int *avocado___error(void)
{
  return &__CPROVER_errno;
}

/* FUNCTION: __errno_location */

// This is used on Linux to return the address of a
// variable used for the errno macro.

__CPROVER_thread_local int __CPROVER_errno;

int *avocado___errno_location(void)
{
  return &__CPROVER_errno;
}

/* FUNCTION: _errno */

// This is used on Windows to return the address of a
// variable used for the errno macro.

__CPROVER_thread_local int __CPROVER_errno;

int *avocado__errno(void)
{
  return &__CPROVER_errno;
}

/* FUNCTION: __errno */

// This has been spotted in CYGWIN

__CPROVER_thread_local int __CPROVER_errno;

extern int *avocado___errno(void)
{
  return &__CPROVER_errno;
}

/* FUNCTION: ___errno */

// This has been spotted on Solaris

__CPROVER_thread_local int __CPROVER_errno;

extern int *avocado____errno(void)
{
  return &__CPROVER_errno;
}
