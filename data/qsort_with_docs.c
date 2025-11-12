#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

/**
 * Swap consumes two pointers and switches their values.
 * I.e., given a pointer 'a' and a pointer 'b', 'a' should point
 * to the original value of 'b', and 'b' should point to the original value of 'b'.
 *
 * @param a int* A pointer to an integer.
 * @param b int* A pointer to an integer.
 */
void swap(int* a, int* b)
{
    int t = *a;
    *a = *b;
    *b = t;
}


/**
 * Partition will reorder a given array such that all elements
 * of it below a certain value (i.e., the pivot value) will be to
 * its left, and all elements above a certain value will be to its right.
 *
 * low and high should not overflow.
 *
 * @param arr[] The array to re-order.
 * @param low The starting index of the subarray to re-order.
 * @param high The pivot index.
 *
 * @return The pivot index.
 */
int partition (int arr[], int low, int high)
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


void quickSort(int arr[], int low, int high)
{
    
    if (low < high) {
        
        int i = partition(arr, low, high);
        
        quickSort(arr, low, i - 1); 
        quickSort(arr, i + 1, high); 
    }
}