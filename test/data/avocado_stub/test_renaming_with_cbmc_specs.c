#include <stdlib.h>
#include <ctype.h>
#include "string.h"
#include <time.h> // `time` is renamed function name, but this header should not be renamed.

int is_separator(int c)
__CPROVER_ensures(__CPROVER_return_value == (c == '\0' || isspace(c) || strchr(",.()+-/*=~%[];",c) != NULL))
__CPROVER_ensures((__CPROVER_return_value == 0) ==> (c == '\0' || isspace(c) || strchr(",.()+-/*=~%[];",c) == NULL))
{
    return c == '\0' ||
        isspace(c) ||
        strchr(",.()+-/*=~%[];",c) != NULL;
}