"""Integration tests with stubbed-out LLM calls."""

import subprocess

LLM_CACHE_DIR_FOR_INTEGRATION_TESTS = "data/caching/llm/integration"

def test_generate_specs_max_min() -> None:
    path_to_max_min_source = "data/max_min.c"
    pass
    # cmd = f"./main.py {path_to_max_min_source} --path-to-llm-response-cache {LLM_CACHE_DIR_FOR_INTEGRATION_TESTS}"
    # result = subprocess.run(cmd, shell=True, capture_output=True, text=True)

