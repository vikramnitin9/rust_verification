#include <stdio.h>
#include <limits.h>
#include <stddef.h>

int max(int arr[], int low, int high)
__CPROVER_requires(arr != NULL)
__CPROVER_requires(low >= 0)
__CPROVER_requires(high >= low)

/* arr[low..high] must be writable */
__CPROVER_requires(
  __CPROVER_rw_ok(arr + low, (high - low + 1) * sizeof(int))
)

/* return value bounds */
__CPROVER_ensures(__CPROVER_return_value >= low)
__CPROVER_ensures(__CPROVER_return_value <= high)

/* pivot correctness */
__CPROVER_ensures(
  arr[__CPROVER_return_value] == __CPROVER_old(arr[high])
)

/* partition property: left side <= pivot */
__CPROVER_ensures(
  __CPROVER_forall {
    int j;
    low <= j && j < __CPROVER_return_value
      ==> arr[j] <= arr[__CPROVER_return_value]
  }
)

/* partition property: right side > pivot */
__CPROVER_ensures(
  __CPROVER_forall {
    int k;
    __CPROVER_return_value < k && k <= high
      ==> arr[k] > arr[__CPROVER_return_value]
  }
)

/* CBMC does NOT allow ranged assigns */
__CPROVER_assigns(arr)
{
    int pivot = arr[high];
    int i = low - 1;

    for (int j = low; j <= high - 1; j++) {
        if (arr[j] <= pivot) {
            i++;
            swap(&arr[i], &arr[j]);
        }
    }

    swap(&arr[i + 1], &arr[high]);
    return i + 1;
}
