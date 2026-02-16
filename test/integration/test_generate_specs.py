"""Integration tests with stubbed-out LLM calls."""

import subprocess
import pickle as pkl

LLM_CACHE_DIR_FOR_INTEGRATION_TESTS = "test/data/caching/llm/integration"
PATH_TO_INTEGRATION_TEST_DIR = "test/integration"
DEFAULT_SPEC_CANDIDATES_FOR_TESTING = 5

VERIFIED_FUNCTION_SRC_CODE = """struct Pair get_min_max(int arr[], int n)
__CPROVER_requires(__CPROVER_is_fresh(arr, n * sizeof(int)))
__CPROVER_requires(n > 0)
__CPROVER_ensures(__CPROVER_return_value.min <= __CPROVER_return_value.max)
__CPROVER_ensures(__CPROVER_forall { int i; (0 <= i && i < n) ==> (__CPROVER_return_value.min <= arr[i] && arr[i] <= __CPROVER_return_value.max) })
__CPROVER_assigns()
{
    struct Pair min_max;

    if (n == 1)
    {
        min_max.min = arr[0];
        min_max.max = arr[0];
    }
    else
    {
        int curr_min = INT_MAX;
        int curr_max = INT_MIN;
        for (int i = 0; i < n; i++)
        {
            curr_min = curr_min <= arr[i] ? curr_min : arr[i];
            curr_max = curr_max >= arr[i] ? curr_max : arr[i];
        }
        min_max.min = curr_min;
        min_max.max = curr_max;

    }
    return min_max;
}"""


def test_generate_specs_max_min() -> None:
    path_to_max_min_source = "data/max_min.c"
    cmd = (
        f"./main.py {path_to_max_min_source}"
        f" --num-specification-candidates 5"
        f" --num-repair-candidates 2"
        f" --num-specification-repair-iterations 1"
        f" --path-to-llm-response-cache-dir {LLM_CACHE_DIR_FOR_INTEGRATION_TESTS}"
        f" --path-to-save-proofstates {PATH_TO_INTEGRATION_TEST_DIR}"
        f" --stub-out-llm"
    )
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)

    assert result.returncode == 0

    # There are 3 successfully-verifying specs parsed from the cached LLM response.
    # Note that they don't have to be unique.
    assert result.stderr.count("Verification succeeded for function 'get_min_max") == 3

    with open(f"{PATH_TO_INTEGRATION_TEST_DIR}/proofstates.pkl", "rb") as f:
        proof_states = pkl.load(f)
        get_min_max_src = set()
        for ps in proof_states:
            for fn in ps.get_specifications():
                if fn.name == "get_min_max":
                    get_min_max_src.add(fn.get_source_code())

        assert list(get_min_max_src)[0] == VERIFIED_FUNCTION_SRC_CODE

    # Clean up the temporary proof states.
    cmd = f"rm {PATH_TO_INTEGRATION_TEST_DIR}/**.pkl"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    assert result.returncode == 0, f"Failed to delete temporary proof state files in {PATH_TO_INTEGRATION_TEST_DIR}"
