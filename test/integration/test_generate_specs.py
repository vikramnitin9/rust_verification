"""Integration tests with stubbed-out LLM calls."""

import shutil
import subprocess
import pickle as pkl
import os
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
LLM_CACHE_DIR_FOR_INTEGRATION_TESTS = str(REPO_ROOT / "test/data/caching/llm/integration")
PATH_TO_INTEGRATION_TEST_DIR = str(REPO_ROOT / "test/integration")

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

    # Copy the cache to a temp directory so the test doesn't modify the checked-in cache.db.
    with tempfile.TemporaryDirectory() as tmp_cache_dir:
        shutil.copytree(LLM_CACHE_DIR_FOR_INTEGRATION_TESTS, tmp_cache_dir, dirs_exist_ok=True)

        cmd = (
            f"./main.py {path_to_max_min_source}"
            f" --num-specification-candidates 5"
            f" --num-repair-candidates 2"
            f" --num-specification-repair-iterations 1"
            f" --path-to-llm-response-cache-dir {tmp_cache_dir}"
            f" --path-to-save-proofstates {PATH_TO_INTEGRATION_TEST_DIR}"
            f" --stub-out-llm"
        )
        result = subprocess.run(
            cmd, shell=True, capture_output=True, text=True, cwd=str(REPO_ROOT)
        )

    assert result.returncode == 0, f"Process failed.\nstderr:\n{result.stderr}"
    assert result.stderr.count("Verification succeeded for function 'get_min_max") == 3

    pkl_path = Path(PATH_TO_INTEGRATION_TEST_DIR) / "proofstates.pkl"
    assert pkl_path.exists(), f"File not found at {pkl_path}.\nstderr:\n{result.stderr}"

    try:
        with open(pkl_path, "rb") as f:
            proof_states = pkl.load(f)
            get_min_max_src = set()
            for ps in proof_states:
                for fn in ps.get_specifications():
                    if fn.name == "get_min_max":
                        get_min_max_src.add(fn.get_source_code())


            assert len(get_min_max_src) > 0, f"Expected at least one verified specification for 'get_min_max'"
            assert next(iter(get_min_max_src)) == VERIFIED_FUNCTION_SRC_CODE
    finally:
        # Clean up the temporary proof states.
        cmd = f"rm {PATH_TO_INTEGRATION_TEST_DIR}/*.pkl"
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        assert result.returncode == 0, f"Failed to delete temporary proof state files in {PATH_TO_INTEGRATION_TEST_DIR}"

