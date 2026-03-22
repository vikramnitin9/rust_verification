#include <stdlib.h>
#include <ctype.h>

int is_separator(int c)
{
    return c == '\0' ||
        _avocado_isspace(c) ||
        _avocado_strchr(",.()+-/*=~%[];",c) != NULL;
}