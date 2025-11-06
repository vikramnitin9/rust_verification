int partition(int arr[], int low, int high)
__CPROVER_requires(low >= 0 && high >= low)
__CPROVER_requires(__CPROVER_is_fresh(arr, (high + 1) * sizeof(int)))
__CPROVER_ensures(__CPROVER_return_value >= low && __CPROVER_return_value <= high)
__CPROVER_ensures(
  __CPROVER_forall {
    int k;
    (low <= k && k < __CPROVER_return_value) ==> (arr[k] <= arr[__CPROVER_return_value])
  }
)
__CPROVER_ensures(
  __CPROVER_forall {
    int m;
    (__CPROVER_return_value < m && m <= high) ==> (arr[m] > arr[__CPROVER_return_value])
  }
)
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