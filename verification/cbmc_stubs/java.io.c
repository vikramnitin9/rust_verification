/* FUNCTION: java::java.io.InputStream.read:()I */

int __CPROVER_ID "java::java.io.InputStream.read:()I" (void *)
{
  int avocado_read_result;
  __CPROVER_assume(read_result>=-1 && read_result<=255);
  return read_result;
}
