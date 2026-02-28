
/* FUNCTION: isalnum */

int avocado_isalnum(int c)
{ return (c>='a' && c<='z') || (c>='A' && c<='Z') || (c>='0' && c<='9'); }

/* FUNCTION: isalpha */

int avocado_isalpha(int c)
{ return (c>='a' && c<='z') || (c>='A' && c<='Z'); }

/* FUNCTION: isblank */

int avocado_isblank(int c)
{ return c==' ' || c=='\t'; }

/* FUNCTION: iscntrl */

int avocado_iscntrl(int c)
{ return (c>=0 && c<='\037') || c=='\177'; }

/* FUNCTION: isdigit */

int avocado_isdigit(int c)
{ return c>='0' && c<='9'; }

/* FUNCTION: isgraph */

int avocado_isgraph(int c)
{ return c>='!' && c<='~'; }

/* FUNCTION: islower */

int avocado_islower(int c)
{ return c>='a' && c<='z'; }

/* FUNCTION: isprint */

int avocado_isprint(int c)
{ return c>=' ' && c<='~'; }

/* FUNCTION: ispunct */

int avocado_ispunct(int c)
{ return c=='!' ||
         c=='"' ||
         c=='#' ||
         c=='$' ||
         c=='%' ||
         c=='&' ||
         c=='\'' ||
         c=='(' ||
         c==')' ||
         c=='*' ||
         c=='+' ||
         c==',' ||
         c=='-' ||
         c=='.' ||
         c=='/' ||
         c==':' ||
         c==';' ||
         c=='<' ||
         c=='=' ||
         c=='>' ||
         c=='?' ||
         c=='@' ||
         c=='[' ||
         c=='\\' ||
         c==']' ||
         c=='^' ||
         c=='_' ||
         c=='`' ||
         c=='{' ||
         c=='|' ||
         c=='}' ||
         c=='~'; }

/* FUNCTION: isspace */

int avocado_isspace(int c)
{ return c=='\t' ||
         c=='\n' ||
         c=='\v' ||
         c=='\f' ||
         c=='\r' ||
         c==' '; }

/* FUNCTION: isupper */

int avocado_isupper(int c)
{ return c>='A' && c<='Z'; }

/* FUNCTION: isxdigit */

int avocado_isxdigit(int c)
{ return (c>='A' && c<='F') || (c>='a' && c<='f') || (c>='0' && c<='9'); }

/* FUNCTION: __CPROVER_tolower */

int avocado___CPROVER_tolower(int c)
{
  return (c >= 'A' && c <= 'Z') ? c + ('a' - 'A') : c;
}

/* FUNCTION: tolower */

int __CPROVER_tolower(int c);

int avocado_tolower(int c)
{
  return __CPROVER_tolower(c);
}

/* FUNCTION: __tolower */

int __CPROVER_tolower(int c);

int avocado___tolower(int c)
{
  return __CPROVER_tolower(c);
}

/* FUNCTION: __CPROVER_toupper */

int avocado___CPROVER_toupper(int c)
{
  return (c >= 'a' && c <= 'z') ? c - ('a' - 'A') : c;
}

/* FUNCTION: toupper */

int __CPROVER_toupper(int c);

int avocado_toupper(int c)
{
  return __CPROVER_toupper(c);
}

/* FUNCTION: __toupper */

int __CPROVER_toupper(int c);

int avocado___toupper(int c)
{
  return __CPROVER_toupper(c);
}
