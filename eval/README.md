# Evaluation Infrastructure

## Summarizing Verification Results

To summarize the results of verifying a C file (i.e., the verification results for each function
in a given C file), run (from the root of this project):

```sh
% ./eval/get_verification_summary.py --file <PATH_TO_C_FILE> --path-to-cache-dir <PATH_TO_VERIFICATION_CACHE_DIR>
```

The output of this script conforms to this schema:

```json
{
    "file_name": <FILE_NAME>,
    "functions": [<VERIFICATION_SUMMARY>*]
}
```

The schema for `VERIFICATION_SUMMARY`:

```json
{
    "function_name": <FUNCTION_NAME>,
    "verifying_specs": [<SPEC_WITH_COMPLEXITY>*],
    "failing_specs": [<SPEC_WITH_COMPLEXITY>*],
    "lookup_errors": [<CACHE_LOOKUP_ERROR>*]
}

```

The schema for `SPEC_WITH_COMPLEXITY`:

```json
{
    "spec": <FUNCTION_SPECIFICATION>,
    "precondition_complexity": [<CLAUSE_COMPLEXITY_INFO>*],
    "postcondition_complexity": [<CLAUSE_COMPLEXITY_INFO>*]
}
```

[function_specification.py](../util/function_specification.py) contains a definition for
`FUNCTION_SPECIFICATION`.

The schema for `CLAUSE_COMPLEXITY_INFO` is either:

```json
{
    "clause": <STRING>,
    "num_atoms": <INT>,
    "num_unique_atoms": <INT>,
    "is_tautology": <BOOL>
}
```

or, if complexity computation failed:

```json
{
    "clause": <STRING>,
    "error": <STRING>
}
```
