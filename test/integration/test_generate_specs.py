"""Integration tests with stubbed-out LLM calls."""

import subprocess

LLM_CACHE_DIR_FOR_INTEGRATION_TESTS = "test/data/caching/llm/integration"
DEFAULT_SPEC_CANDIDATES_FOR_TESTING = 5

def test_generate_specs_max_min() -> None:
    path_to_max_min_source = "data/max_min.c"
    cmd = f"./main.py {path_to_max_min_source} --num-specification-candidates 5 --num-repair-candidates 2 --num-specification-repair-iterations 1 --path-to-llm-response-cache-dir {LLM_CACHE_DIR_FOR_INTEGRATION_TESTS}"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    # TODO: assert on the result.

