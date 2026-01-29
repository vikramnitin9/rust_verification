#include <limits.h>
#include <stdlib.h>

int divide(int numerator, int denominator)
__CPROVER_requires(!(numerator == INT_MIN && denominator == -1))
__CPROVER_ensures(
    (denominator == 0) ==> (__CPROVER_return_value == INT_MAX)
)
__CPROVER_ensures(
    denominator != 0 ==>
      (__CPROVER_return_value * denominator <= numerator &&
       (__CPROVER_return_value + 1) * denominator > numerator)
)
{
    if (denominator == 0)
    {
        return INT_MAX;
    }

    return numerator / denominator;
}
