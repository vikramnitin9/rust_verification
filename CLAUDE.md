# AGENTS.md

## Development Commands

- `make run`: starts the Docker container in which this system runs.
  - All commands should be executed inside this container.
- `make unit-test`: runs unit tests.
- `make integration-test`: runs integration tests.
- `make`: runs both unit and integration tests.

## Code Style

- All code *must* should pass linting:
  - `make checks` should yield 0 errors or warnings.
  - Consult the user if there is ever a need to suppress a warning.
- All business logic should be documented, even helper code. Test code (i.e., any code under
  `test/`) need not be documented.
- Do not use double backticks in docstrings, use single backticks.

## Basic Organization

- `util/`: Utilities related to representing functions (`c_function.py`, `function_util.py`),
    C projects (`c_function_graph.py`),
    files (`file_util.py`),
    text (`text_util.py`),
    ASTs (`tree_sitter_util.py`).
- `verification/`: Code related to verification with CBMC or other verifiers
    (`cbmc_verification_client.py`, `verification_client.py`),
    verifier inputs (`verification_input.py`),
    outputs (`verification_output.py`),
    and results (`verification_result.py`),
    prompt templates (`prompt_builder.py`).
- `prompts/`: Plaintext prompt templates.
- `models/`: Code related to LLM calls.
- `translation/`: Code related to translating between CBMC and Kani,
    includes CBMC grammar (`cbmc.txt`).
