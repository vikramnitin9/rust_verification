#include <stdlib.h>
#include <ctype.h>

int is_separator(int c)
{
    return c == '\0' ||
        avocado_isspace(c) ||
        avocado_strchr(",.()+-/*=~%[];",c) != NULL;
}