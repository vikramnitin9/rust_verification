/* FUNCTION: openlog */

void avocado_openlog(const char *ident, int option, int facility)
{
  (void)*ident;
  (void)option;
  (void)facility;
}

/* FUNCTION: closelog */

void avocado_closelog(void)
{
}

/* FUNCTION: syslog */

void avocado_syslog(int priority, const char *format, ...)
{
  (void)priority;
  (void)*format;
}

/* FUNCTION: _syslog$DARWIN_EXTSN */

void avocado__syslog$DARWIN_EXTSN(int priority, const char *format, ...)
{
  (void)priority;
  (void)*format;
}

/* FUNCTION: __syslog_chk */

void avocado___syslog_chk(int priority, int flag, const char *format, ...)
{
  (void)priority;
  (void)flag;
  (void)*format;
}
