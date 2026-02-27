#include <ctype.h>

const unsigned short int **__ctype_b_loc(void) {
    static const unsigned short int table[384] = { /* ... add minimal character data ... */ };
    static const unsigned short int *table_ptr = table + 128; // Adjust for signed char
    return &table_ptr;
}