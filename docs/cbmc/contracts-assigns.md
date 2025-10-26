# Assigns Clauses

## Table of Contents

- [Syntax](#syntax)
  - [Lvalue targets](#lvalue-targets)
  - [Object slice targets](#object-slice-targets)
  - [Function parameters](#function-parameters)
  - [Inductive data structures](#inductive-data-structures)
- [Semantics](#semantics)
  - [Contract Enforcement](#contract-enforcement)
  - [Contract Replacement](#contract-replacement)
- [Loop Assigns Inference](#loop-assigns-inference)
  - [Limitation](#limitation)
- [Additional Resources](#additional-resources)

---

## Syntax

An *assigns* clause allows the user to specify a set of locations that may be assigned to by a function or the body of a loop:

```c
__CPROVER_assigns(targets)
```

Where `targets` has the following syntax:

```text
targets           ::= cond-target-group (';' cond-target-group)* ';'?
cond-target-group ::= (condition ':')? target (',' target)*
target            ::= lvalue-expr
                    | __CPROVER_typed_target(lvalue-expr)
                    | __CPROVER_object_whole(ptr-expr)
                    | __CPROVER_object_from(ptr-expr)
                    | __CPROVER_object_upto(ptr-expr, uint-expr)
```

The set of locations writable by a function is the union of the sets of locations specified by its assigns clauses, or the empty set if no *assigns* clause is specified.

While, in general, an *assigns* clause could be interpreted with either *writes* or *modifies* semantics, this design is based on the former.

### Lvalue targets

Lvalue expressions designate memory locations directly and are included as targets.

### Object slice targets

Each target listed in an assigns clause defines a *conditionally assignable range* of bytes represented by the following triple:

```c
struct {
  void *start_address;
  size_t size;
  bool is_writable;
}
```

Where:

- `start_address` is the start address of the range of bytes,
- `size` is the size of the range in number of bytes,
- `is_writable` is true iff the target's `condition` holds and `__CPROVER_w_ok(start_address, size)` holds at the program location where the clause is interpreted: right before function invocation for function contracts and at loop entry for loops.

### Function parameters

For a function contract, the memory locations storing function parameters are considered as being local to the function and are hence always assignable.

For a loop contract, the parameters of the enclosing function are not considered local to the loop and must be explicitly added to the loop to become assignable.

### Inductive data structures

Inductive data structures are not supported yet in assigns clauses.

---

## Semantics

### Contract Enforcement

In order to determine whether a function (or loop) complies with the *assigns* clause of the contract, the body of the function (or loop) is instrumented with assertion statements before each statement which may write to memory (e.g., an assignment). These assertions check that the location about to be assigned to is among the targets specified by the *assigns* clauses.

**Example**:

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
/* Writable Set */
__CPROVER_assigns(*out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  *out = result;
  return 0;
}
```

### Contract Replacement

Assuming the *assigns* clause of the contract correctly captures the set of locations assigned to by a function (checked during *contract enforcement*), CBMC will use the contract’s `requires` and `ensures` clauses and its *assigns clause* to generate a sound abstraction of the function behaviour from the contract.

Given the contract:

```c
int f(params)
__CPROVER_requires(R);
__CPROVER_assigns(A);
__CPROVER_ensures(E);
{
  ...
}
```

Function calls `f(args)` get replaced with a sequence of instructions equivalent to:

```c
// check preconditions
assert(R);

// havoc the assigns targets
havoc(A);

// assume postconditions
assume(E);
```

---

## Loop Assigns Inference

The inference algorithm consists of three stages:

1. Function inlining,
2. Collecting assigns targets with local-may-alias analysis,
3. Assigns targets widening.

We do the function inlining first so that we can infer those assigns targets hidden in the function call.

**Example**:

In the `test_loop_assigns_inference` example, there are five assignments in the loop:

1. `n = &i` → assign target: `n` (loop local, excluded)
2. `*n++` → assign target: `*n` → alias `&i` → `i` is included
3. `k = i + 1` → target: `k` (loop local, excluded)
4. `j = i` → target: `j` → included
5. `b[j] = 1` → target: `b[j]` → included

Finally, `b[j]` is widened to `__CPROVER_object_whole(b)` as its index `j` is non-constant.

### Limitation

The main limitation of the inference algorithm is that the local-may-alias analysis is field insensitive. For example:

```c
ptr = box.ptr;
*ptr = 5;
```

We cannot determine that `ptr` aliases `box.ptr`, and will fail to infer the assigns target `__CPROVER_object_whole(box.ptr)`.

However, this does not result in unsoundness. CBMC will report assignability-checks failure when the inferred assigns clauses are not accurate.

---

## Additional Resources

- Function Contracts
  - Requires and Ensures Clauses
  - Assigns Clauses
  - Frees Clauses
- Loop Contracts
  - Loop Invariant Clauses
  - Decreases Clauses
  - Assigns Clauses
  - Frees Clauses
- Memory Predicates
- Function Pointer Predicates
- History Variables
- Quantifiers
