extern crate kani;
use kani::{requires, ensures, modifies};

// __CPROVER_requires(a != NULL && b != NULL)
// __CPROVER_ensures(*a == __CPROVER_old(*b) && *b == __CPROVER_old(*a))
// __CPROVER_assigns(*a, *b)
// #[requires(a != NULL && b != NULL)]
#[ensures(|result| *a == old(*b) && *b == old(*a))]
#[modifies(a, b)]
fn swap(a: &mut i32, b: &mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

#[kani::proof_for_contract(swap)]
fn check_swap() {
    let mut a: i32 = kani::any();
    let mut b: i32 = kani::any();
    swap(&mut a, &mut b);
}

fn partition(arr: &mut [i32], low: usize, high: usize) -> usize {
    let pivot = arr[high];
    let mut i = if low == 0 { 0 } else { low - 1 };

    for j in low..high {
        if arr[j] <= pivot {
            if i < low - 1 {
                i = low - 1;
            }
            i += 1;
            arr.swap(i, j);
        }
    }
    arr.swap(i + 1, high);
    i + 1
}

fn quickSort(arr: &mut [i32], low: usize, high: usize) {
    if low < high {
        let pi = partition(arr, low, high);
        if pi > 0 {
            quickSort(arr, low, pi - 1);
        }
        quickSort(arr, pi + 1, high);
    }
}

fn main() {
    println!("Hello, world!");
}