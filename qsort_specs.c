#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stddef.h>
#include <limits.h>

// Function that swaps the integer values pointed to by a and b
void swap(int* a, int* b)
__CPROVER_requires(__CPROVER_r_ok(a) && __CPROVER_r_ok(b) && \
    __CPROVER_w_ok(a) && __CPROVER_w_ok(b))
__CPROVER_ensures(*a == __CPROVER_old(*b) && *b == __CPROVER_old(*a))
__CPROVER_assigns(*a, *b)
{
    int t = *a;
    *a = *b;
    *b = t;
}

// Divides the array into two partitions
int partition (int arr[], int low, int high)
__CPROVER_requires(arr != NULL && \
    low >= 0 && high >= 0 && low <= high && high < INT_MAX && \
    __CPROVER_is_fresh(arr, sizeof(int) * (high + 1)))
__CPROVER_ensures(__CPROVER_return_value >= low && __CPROVER_return_value <= high)
__CPROVER_assigns(arr)
{
    int pivot = arr[high]; // Choose the last element as the pivot
    int i = low - 1; // Temporary pivot index

    for (int j = low; j <= high - 1; j++) {
        // If the current element is less than or equal to the pivot
        if (arr[j] <= pivot) {
            // Move the temporary pivot index forward
            i++;
            // Swap the current element with the element at the temporary pivot index
            swap(&arr[i], &arr[j]);
        }
    }
    // Swap the pivot with the last element
    swap(&arr[i + 1], &arr[high]);
    return i + 1; // the pivot index
}

// Sorts (a portion of) an array, divides it into partitions, then sorts those
void quickSort(int arr[], int low, int high)
__CPROVER_requires(arr != NULL && \
    low >= 0 && high >= 0 && low <= high && high < INT_MAX && \
    __CPROVER_is_fresh(arr, sizeof(int) * (high + 1)))
__CPROVER_ensures(
  __CPROVER_forall{int i; (low <= i && i < high) ==> arr[i] <= arr[i + 1]}
)
__CPROVER_assigns(arr)
{
    // Ensure indices are in correct order
    if (low < high) {
        // Partition array and get the pivot index
        int i = partition(arr, low, high);
        // Sort the two partitions
        quickSort(arr, low, i - 1); // Left side of pivot
        quickSort(arr, i + 1, high); // Right side of pivot
    }
}
