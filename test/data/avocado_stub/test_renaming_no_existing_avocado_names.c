#include <stdlib.h>
#include <ctype.h>
#include "string.h"
#include<time.h> // `time` is renamed function name, but this header should not be renamed.

int is_separator(int c)
{
    return c == '\0' ||
        isspace(c) ||
        strchr(",.()+-/*=~%[];",c) != NULL;
}