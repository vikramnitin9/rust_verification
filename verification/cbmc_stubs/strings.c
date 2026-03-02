/* FUNCTION: bzero */

void avocado_bzero(void *s, __CPROVER_size_t n)
{
  for(__CPROVER_size_t avocado_i=0; i<n; i++)
    ((char *)s)[i]=0;
}
