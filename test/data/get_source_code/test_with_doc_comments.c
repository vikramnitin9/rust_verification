#include <stdio.h>

// This is a documentation
// Comment
void f1() { }

/** this comment
spans three
lines
 */
void f2()
{
}

int global; /* this should not be included in the comments for f3*/
void f3() {}