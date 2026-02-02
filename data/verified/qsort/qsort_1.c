#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

void swap(int* a, int* b)
__CPROVER_requires(__CPROVER_is_fresh(a, sizeof(*a)))
__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(*b)))
__CPROVER_ensures(*a == __CPROVER_old(*b))
__CPROVER_ensures(*b == __CPROVER_old(*a))
__CPROVER_assigns(*a, *b)
{
    int t = *a;
    *a = *b;
    *b = t;
}


int partition (int arr[], int low, int high)
__CPROVER_requires(low >= 0)
__CPROVER_requires(high >= low)
__CPROVER_requires(high <= INT_MAX / sizeof(*arr))
__CPROVER_requires(__CPROVER_is_fresh(arr, (high + 1) * sizeof(*arr)))
__CPROVER_ensures(__CPROVER_return_value >= low)
__CPROVER_ensures(__CPROVER_return_value <= high)
__CPROVER_ensures(arr[__CPROVER_return_value] == __CPROVER_old(arr[high]))
__CPROVER_assigns(__CPROVER_object_whole(arr))
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