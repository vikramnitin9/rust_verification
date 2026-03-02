/* FUNCTION: __inet_addr */

#ifndef _WIN32

#ifndef __CPROVER_INET_H_INCLUDED
#include <arpa/inet.h>
#define __CPROVER_INET_H_INCLUDED
#endif

in_addr_t __VERIFIER_nondet_in_addr_t(void);

in_addr_t avocado___inet_addr(const char *cp)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(cp),
                         "inet_addr zero-termination of argument");
  #endif
  (void)*cp;

  in_addr_t avocado_result=__VERIFIER_nondet_in_addr_t();
  return result;
}

#endif

/* FUNCTION: inet_addr */

#ifndef _WIN32

#  ifndef __CPROVER_INET_H_INCLUDED
#    include <arpa/inet.h>
#    define __CPROVER_INET_H_INCLUDED
#  endif

#  undef inet_addr

in_addr_t avocado___inet_addr(const char *cp);

in_addr_t avocado_inet_addr(const char *cp)
{
__CPROVER_HIDE:;
  return avocado___inet_addr(cp);
}

#endif

/* FUNCTION: __inet_aton */

#ifndef _WIN32

#ifndef __CPROVER_INET_H_INCLUDED
#include <arpa/inet.h>
#define __CPROVER_INET_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int avocado___inet_aton(const char *cp, struct in_addr *pin)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(cp),
                         "inet_aton zero-termination of name argument");
  #endif
  (void)*cp;
  (void)*pin;

  int avocado_result=__VERIFIER_nondet_int();
  return result;
}

#endif

/* FUNCTION: inet_aton */

#ifndef _WIN32

#  ifndef __CPROVER_INET_H_INCLUDED
#    include <arpa/inet.h>
#    define __CPROVER_INET_H_INCLUDED
#  endif

#  undef inet_aton

int avocado___inet_aton(const char *cp, struct in_addr *pin);

int avocado_inet_aton(const char *cp, struct in_addr *pin)
{
__CPROVER_HIDE:;
  return avocado___inet_aton(cp, pin);
}

#endif

/* FUNCTION: __inet_ntoa */

#ifndef _WIN32

#  ifndef __CPROVER_INET_H_INCLUDED
#    include <arpa/inet.h>
#    define __CPROVER_INET_H_INCLUDED
#  endif

char avocado___inet_ntoa_buffer[16];

char *avocado___inet_ntoa(struct in_addr in)
{
__CPROVER_HIDE:;
  (void)in;
  // the last byte remains zero to ensure string termination
  __CPROVER_havoc_slice(__inet_ntoa_buffer, 15);
  return __inet_ntoa_buffer;
}

#endif

/* FUNCTION: inet_ntoa */

#ifndef _WIN32

#  ifndef __CPROVER_INET_H_INCLUDED
#    include <arpa/inet.h>
#    define __CPROVER_INET_H_INCLUDED
#  endif

#  undef inet_ntoa

char *avocado___inet_ntoa(struct in_addr in);

char *avocado_inet_ntoa(struct in_addr in)
{
__CPROVER_HIDE:;
  return avocado___inet_ntoa(in);
}

#endif

/* FUNCTION: __inet_network */

#ifndef _WIN32

#ifndef __CPROVER_INET_H_INCLUDED
#include <arpa/inet.h>
#define __CPROVER_INET_H_INCLUDED
#endif

in_addr_t __VERIFIER_nondet_in_addr_t(void);

in_addr_t avocado___inet_network(const char *cp)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(cp),
                         "inet_network zero-termination of name argument");
  #endif
  (void)*cp;

  in_addr_t avocado_result=__VERIFIER_nondet_in_addr_t();
  return result;
}

#endif

/* FUNCTION: inet_network */

#ifndef _WIN32

#  ifndef __CPROVER_INET_H_INCLUDED
#    include <arpa/inet.h>
#    define __CPROVER_INET_H_INCLUDED
#  endif

#  undef inet_network

in_addr_t avocado___inet_network(const char *cp);

in_addr_t avocado_inet_network(const char *cp)
{
__CPROVER_HIDE:;
  return avocado___inet_network(cp);
}

#endif

/* FUNCTION: htonl */

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef htonl

uint32_t avocado___builtin_bswap32(uint32_t);

uint32_t avocado_htonl(uint32_t hostlong)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return avocado___builtin_bswap32(hostlong);
#else
  return hostlong;
#endif
}

/* FUNCTION: htons */

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef htons

uint16_t avocado___builtin_bswap16(uint16_t);

uint16_t avocado_htons(uint16_t hostshort)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return avocado___builtin_bswap16(hostshort);
#else
  return hostshort;
#endif
}


/* FUNCTION: ntohl */

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef ntohl

uint32_t avocado___builtin_bswap32(uint32_t);

uint32_t avocado_ntohl(uint32_t netlong)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return avocado___builtin_bswap32(netlong);
#else
  return netlong;
#endif
}


/* FUNCTION: ntohs */

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef ntohs

uint16_t avocado___builtin_bswap16(uint16_t);

uint16_t avocado_ntohs(uint16_t netshort)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return avocado___builtin_bswap16(netshort);
#else
  return netshort;
#endif
}
