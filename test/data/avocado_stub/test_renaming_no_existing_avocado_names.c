#include <stdlib.h>
#include <ctype.h>

int is_separator(int c)
{
    return c == '\0' ||
        isspace(c) ||
        strchr(",.()+-/*=~%[];",c) != NULL;
}