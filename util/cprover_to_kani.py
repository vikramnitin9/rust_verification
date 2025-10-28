"""Module to convert a CProver specification to a Kani specification."""


def cprover_to_kani(spec: list[str]) -> list[str]:
    """Convert a CProver specification to a Kani specification.

    Args:
        spec (list[str]): A CProver specification: a list of clauses.

    Returns:
        list[str]: A Kani specification: a list of clauses.
    """
    kani_spec = []

    # Here is a CProver clause:
    # __CPROVER_requires(x > 0)
    # The corresponding Kani clause:
    # kani::requires(x > 0)

    for clause in spec:
        clause = clause.strip()
        if clause.startswith("__CPROVER_requires"):
            condition = clause[len("__CPROVER_requires(") : -1]
            kani_clause = f"#[kani::requires({condition})]"

        elif clause.startswith("__CPROVER_ensures"):
            condition = clause[len("__CPROVER_ensures(") : -1]
            kani_clause = f"#[kani::ensures({condition})]"

        elif clause.startswith("__CPROVER_assigns"):
            condition = clause[len("__CPROVER_assigns(") : -1]
            kani_clause = f"#[kani::modifies({condition})]"

        else:
            # Skip unknown clause types.
            continue

        if "NULL" in condition:
            continue

        kani_spec.append(kani_clause)
    return kani_spec


if __name__ == "__main__":
    spec = [
        "__CPROVER_requires(x > 0)",
        "__CPROVER_ensures(result >= 0)",
        "__CPROVER_assigns(x, y)",
        "__CPROVER_requires(ptr != NULL)",  # This should be filtered out
    ]
    kani_spec = cprover_to_kani(spec)
    for clause in kani_spec:
        print(clause)
