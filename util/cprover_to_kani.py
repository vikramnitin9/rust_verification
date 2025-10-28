"""Module to convert CProver specifications to Kani specifications."""


def cprover_to_kani(specs: list[str]) -> list[str]:
    """Convert CProver specifications to Kani specifications.

    Args:
        specs (list[str]): List of CProver specifications.

    Returns:
        list[str]: List of Kani specifications.
    """
    kani_specs = []

    ## TODO: This example doesn't include "#[...]".  Should it?

    # Here is an example of a CProver spec:
    # __CPROVER_requires(x > 0)
    # We will convert it to a Kani spec:
    # kani::requires(x > 0)

    for spec in specs:
        spec = spec.strip()
        if spec.startswith("__CPROVER_requires"):
            condition = spec[len("__CPROVER_requires(") : -1]
            kani_spec = f"#[kani::requires({condition})]"

        elif spec.startswith("__CPROVER_ensures"):
            condition = spec[len("__CPROVER_ensures(") : -1]
            kani_spec = f"#[kani::ensures({condition})]"

        elif spec.startswith("__CPROVER_assigns"):
            condition = spec[len("__CPROVER_assigns(") : -1]
            kani_spec = f"#[kani::modifies({condition})]"

        # TODO: This seems overly broad.
        if "NULL" in condition:
            continue

        kani_specs.append(kani_spec)
    return kani_specs


if __name__ == "__main__":
    specs = [
        "__CPROVER_requires(x > 0)",
        "__CPROVER_ensures(result >= 0)",
        "__CPROVER_assigns(x, y)",
        "__CPROVER_requires(ptr != NULL)",  # This should be filtered out
    ]
    kani_specs = cprover_to_kani(specs)
    for spec in kani_specs:
        print(spec)
