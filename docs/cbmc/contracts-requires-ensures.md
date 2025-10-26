
# Requires and Ensures Clauses

## Table of Contents
- [Syntax](#syntax)
- [Semantics](#semantics)
  - [Enforcement](#enforcement)
  - [Replacement](#replacement)
- [Additional Resources](#additional-resources)

---

## Syntax

```c
__CPROVER_requires(bool cond)
```

A *requires* clause specifies a precondition for a function, i.e., a property that must hold to properly execute the function. Developers may see the *requires* clauses of a function as obligations on the caller when invoking the function. The precondition of a function is the conjunction of the *requires* clauses, or `true` if none are specified.

```c
__CPROVER_ensures(bool cond)
```

An *ensures* clause specifies a postcondition for a function, i.e., a property over arguments or global variables that the function guarantees at the end of the operation. Developers may see the *ensures* clauses of a function as the obligations of that function to the caller. The postcondition of a function is the conjunction of the *ensures* clauses, or `true` if none are specified.

Both *requires* clauses and *ensures* clauses take a Boolean expression over the arguments of a function and/or global variables. The expression can include calls to CBMC built-in functions, to memory predicates, or to function pointer predicates. User-defined functions can also be called inside *requires* clauses as long as they are deterministic and do not have any side-effects. In addition, *ensures* clauses also accept history variables and the special built-in symbol `__CPROVER_return_value`.

---

## Semantics

The semantics of *ensures* and *requires* clauses can be understood in two contexts: **enforcement** and **replacement**. Consider the following implementation of the `sum` function:

```c
int sum(const uint32_t a, const uint32_t b, uint32_t* out)
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
__CPROVER_ensures(
  __CPROVER_return_value == SUCCESS || __CPROVER_return_value == FAILURE)
__CPROVER_ensures(
  (__CPROVER_return_value == SUCCESS) ==> (*out == (a + b)))
__CPROVER_assigns(*out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}
```

### Enforcement

To check if *requires* and *ensures* clauses are a sound abstraction of a function `f`, CBMC performs:

1. All arguments and global variables are considered non-deterministic.
2. All preconditions from `__CPROVER_requires` are assumed.
3. The function implementation is invoked.
4. All postconditions from `__CPROVER_ensures` are asserted.

Example of instrumented `sum`:

```c
int __CPROVER_contracts_original_sum(const uint32_t a, const uint32_t b, uint32_t* out)
{
  const uint64_t result = ((uint64_t) a) + ((uint64_t) b);
  if (result > UINT32_MAX) return FAILURE;
  *out = (uint32_t) result;
  return SUCCESS;
}

int sum(uint32_t a, uint32_t b, uint32_t* out)
{
  __CPROVER_assume(__CPROVER_is_fresh(out, sizeof(*out)));

  int __return_value;

  __return_value = __CPROVER_contracts_original_sum(a, b, out);

  __CPROVER_assert(
    __return_value == SUCCESS || __return_value == FAILURE,
    "Check ensures clause");

  __CPROVER_assert(
    (__return_value == SUCCESS) ==> (*out == (a + b)),
    "Check ensures clause");

  return __return_value;
}
```

### Replacement

Assuming *requires* and *ensures* clauses are a sound abstraction of function `f`, CBMC replaces function calls with:

1. Assertions for all `__CPROVER_requires` clauses.
2. Non-deterministic assignments for symbols in `__CPROVER_assigns`.
3. Non-deterministic frees for symbols in `__CPROVER_frees`.
4. Assumptions for all `__CPROVER_ensures` clauses.

For example, a function `foo`:

```c
int foo()
{
  uint32_t a = ... ;
  uint32_t b = ... ;
  uint32_t out = 0;
  int rval = sum(a, b, &out);
  if (SUCCESS != rval)
    return FAILURE;

  // else, use out
  uint32_t result = out + ...;
}
```

Will be transformed into:

```c
int foo()
{
  uint32_t a = ...;
  uint32_t b = ...;
  uint32_t out = 0;

  // start of call-by-contract replacement
  __CPROVER_assert(
    __CPROVER_is_fresh(out, sizeof(*out)), "Check requires clause");

  int __return_value = nondet_int();

  __CPROVER_assume(__return_value == SUCCESS || __return_value == FAILURE);
  __CPROVER_assume((__return_value == SUCCESS) ==> (*out == (a + b)));

  int rval = __return_value;
  // end of call-by-contract replacement

  if (SUCCESS != rval)
    return FAILURE;

  // else, use out
  uint32_t result = out + ...;
}
```

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
