# Memory Predicates

## Table of Contents

* [The \_\_CPROVER\_pointer\_equals predicate](#the-__cprover_pointer_equals-predicate)
* [The \_\_CPROVER\_is\_fresh predicate](#the-__cprover_is_fresh-predicate)
* [The \_\_CPROVER\_pointer\_in\_range\_dfcc predicate](#the-__cprover_pointer_in_range_dfcc-predicate)

  * [Syntax](#syntax)
* [Using memory predicates in disjunctions](#using-memory-predicates-in-disjunctions)
* [Writing your own memory predicates](#writing-your-own-memory-predicates)

  * [Limitations](#limitations)

---

The built-in predicates discussed in this section are used to describe pointer properties in *requires clauses* and *ensures clauses*.

At a basic level, the predicates allow you to specify:

* Pointers to fresh objects (`__CPROVER_is_fresh(p, size)`),
* Aliased pointers (`__CPROVER_pointer_equals(p, q)`),
* Pointer ranges (`__CPROVER_pointer_in_range_dfcc(lb, p, ub)`).

They must be used in `requires` or `ensures` clauses—using them outside results in a verification error.

These predicates can be composed using conjunctions, implications, or disjunctions, but a `requires` or `ensures` clause must not assert multiple predicates on the same pointer simultaneously.

You can also define custom predicates to describe structures like lists, buffers, etc.

---

## The `__CPROVER_pointer_equals` predicate

This predicate checks for pointer validity and equality.

```c
bool __CPROVER_pointer_equals(void *p, void *q);
```

It returns:

* `true` if and only if:

  * `p` is either `NULL` or valid,
  * `q` is either `NULL` or valid,
  * `p == q`.

### Contract checking behavior

#### `--enforce-contract`

* In a `requires` clause: checks `q` is valid or `NULL`, then assigns `p = q`.
* In an `ensures` clause: checks `p` and `q` are valid or `NULL`, and `p == q`.

#### `--replace-call-with-contract`

* In a `requires` clause: checks both `p` and `q` are valid or `NULL`, and `p == q`.
* In an `ensures` clause: checks `q` is valid or `NULL`, then assigns `p = q`.

---

## The `__CPROVER_is_fresh` predicate

This checks pointer validity and separation.

```c
bool __CPROVER_is_fresh(void *p, size_t size);
```

Holds if:

* `p` points to a valid object with at least `size` bytes,
* The object is distinct from other objects referenced via `__CPROVER_is_fresh`.

### Contract checking behavior

#### `--enforce-contract`

* In `requires`: acts like `p = malloc(size)` nondeterministically.
* In `ensures`: checks validity and separation from all others.

#### `--replace-call-with-contract`

* In `requires`: checks pointer validity and separation.
* In `ensures`: acts like `p = malloc(size)`.

---

## The `__CPROVER_pointer_in_range_dfcc` predicate

### Syntax

```c
bool __CPROVER_pointer_in_range_dfcc(void *lb, void *p, void *ub);
```

Holds if:

* `lb`, `p`, and `ub` are valid and in the same object,
* `lb <= p && p <= ub`.

### Contract checking behavior

#### `--enforce-contract`

* In `requires`: checks `lb`, `ub` valid and assigns `p` nondeterministically between them.
* In `ensures`: checks validity and that `p` is within bounds.

#### `--replace-call-with-contract`

* In `requires`: checks validity and bounds.
* In `ensures`: assigns `p` nondeterministically within bounds.

---

## Using memory predicates in disjunctions

Predicates can describe conditional pointer validity using implications (`==>`):

```c
int foo(int *array, size_t len)
  __CPROVER_requires(
    (len < INT_MAX/sizeof(int) && len > 0)
    ==> __CPROVER_is_fresh(array, len * sizeof(int)))
{
  ...
}
```

Or alternatives:

```c
void foo(int *a, size_t len_a, int *b, size_t len_b, int **out)
  __CPROVER_requires(__CPROVER_is_fresh(a, len_a * sizeof(int)))
  __CPROVER_requires(__CPROVER_is_fresh(b, len_b * sizeof(int)))
  __CPROVER_requires(__CPROVER_is_fresh(out, sizeof(int *)))
  __CPROVER_assigns(*out)
  __CPROVER_requires(len_a >= len_b ==> __CPROVER_pointer_equals(*out, a))
  __CPROVER_requires(len_a < len_b ==> __CPROVER_pointer_equals(*out, b))
{
  ...
}
```

Or nondeterministic pointer choices:

```c
void foo(int *a, int *b, int **out)
  __CPROVER_requires(__CPROVER_is_fresh(a, 1))
  __CPROVER_requires(__CPROVER_is_fresh(b, 1))
  __CPROVER_requires(__CPROVER_is_fresh(out, sizeof(int *)))
  __CPROVER_assigns(*out)
  __CPROVER_requires(
    __CPROVER_pointer_equals(*out, a) || __CPROVER_pointer_equals(*out, b))
{
  ...
}
```

---

## Writing your own memory predicates

You can build higher-level predicates from the built-in ones:

```c
typedef struct buffer_t {
  size_t size;
  char *arr;
  char *cursor;
} buffer_t;

typedef struct double_buffer_t {
  buffer_t *first;
  buffer_t *second;
} double_buffer_t;

bool is_sized_array(char *arr, size_t size) {
  return __CPROVER_is_fresh(arr, size);
}

bool is_buffer(buffer_t *b) {
  return __CPROVER_is_fresh(b, sizeof(*b)) &&
         (0 < b->size && b->size <= 10) &&
         is_sized_array(b->arr, b->size);
}

bool is_double_buffer(double_buffer_t *b) {
  return __CPROVER_is_fresh(b, sizeof(*b)) &&
         is_buffer(b->first) &&
         is_buffer(b->second);
}
```

### Inductive structure example

```c
typedef struct list_t {
  int value;
  struct list_t *next;
} list_t;

bool value_in_range(int lb, int value, int ub) {
  return lb <= value && value <= ub;
}

bool is_list(list_t *l, size_t len) {
  if(len == 0)
    return __CPROVER_pointer_equals(l, NULL);
  else if (__CPROVER_pointer_equals(l, NULL))
    return true;
  else
    return __CPROVER_is_fresh(l, sizeof(*l)) &&
           value_in_range(-10, l->value, 10) &&
           is_list(l->next, len - 1);
}
```

And in a function contract:

```c
int foo(list_t *l, double_buffer_t *b)
  __CPROVER_requires(is_list(l, 3))
  __CPROVER_requires(is_double_buffer(b))
  __CPROVER_ensures(-28 <= __CPROVER_return_value && __CPROVER_return_value <= 50)
{
  return l->value + l->next->value + l->next->next->value +
         b->first->size + b->second->size;
}
```

Internally, CBMC turns user-defined predicates into:

* Nondeterministic allocators (assumption contexts),
* Validators for pointer validity and aliasing (assertion contexts).

---

### Limitations

* User-defined predicates must **terminate**.

  * Use a `len` bound to control recursion depth.
  * E.g., `is_list`, `is_double_buffer`.
* **Mutually-recursive** predicates are not currently supported.