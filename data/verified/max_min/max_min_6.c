#include <stdio.h>
#include <limits.h>

struct Pair {
    int min;
    int max;
};

struct Pair get_min_max(int arr[], int n)
__CPROVER_requires(__CPROVER_is_fresh(arr, n * sizeof(int)))
__CPROVER_requires(n > 0)
__CPROVER_ensures(__CPROVER_return_value.min <= __CPROVER_return_value.max)
__CPROVER_ensures(__CPROVER_forall { int i; (0 <= i && i < n) ==> (arr[i] >= __CPROVER_return_value.min && arr[i] <= __CPROVER_return_value.max) })
{
    struct Pair min_max;

    if (n == 1)
    {
        min_max.min = arr[0];
        min_max.max = arr[0];
    }
    else
    {
        int curr_min = INT_MAX;
        int curr_max = INT_MIN;
        for (int i = 0; i < n; i++)
        {
            curr_min = curr_min <= arr[i] ? curr_min : arr[i];
            curr_max = curr_max >= arr[i] ? curr_max : arr[i];
        }
        min_max.min = curr_min;
        min_max.max = curr_max;

    }
    return min_max;
}