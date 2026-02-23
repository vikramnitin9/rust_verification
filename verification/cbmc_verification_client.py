"""Verifies source code using CBMC."""

import subprocess
import tempfile
from collections.abc import Sequence
from pathlib import Path

from diskcache import Cache  # ty: ignore
from loguru import logger

from util import file_util
from verification.verification_result import VerificationResult

from .verification_client import VerificationClient
from .verification_input import VerificationInput


class CbmcVerificationClient(VerificationClient):
    """Verifies source code using CBMC. The entry point is `verify()`.

    Attributes:
        _cache (Cache): A cache of verification results mapped to verification inputs. The keys for
            this cache are `VerificationInput` and the values are `VerificationResult`.
    """

    _cache: Cache

    # These headers should be inserted into each file that is input to the verifier;
    # generated specs often use constants from these headers (e.g., INT_MAX) assuming they already
    # exist in the file.
    DEFAULT_HEADERS_FOR_VERIFICATION: Sequence[str] = (
        "#include <stdlib.h>",
        "#include <limits.h>",
    )

    def __init__(
        self,
        cache: Cache,
    ) -> None:
        """Create a new CbmcVerificationClient."""
        self._cache = cache

    def verify(self, vinput: VerificationInput) -> VerificationResult:
        """Return the result of verifying the given verification input.

        Args:
            vinput (VerificationInput): The verification input.

        Returns:
            VerificationResult: The result of verifying the given verification input.
        """
        function = vinput.function
        if vinput not in self._cache:
            logger.debug(f"vresult cache miss for: {function}")
            with tempfile.NamedTemporaryFile(
                mode="w+t", prefix=function.name, suffix=".c"
            ) as tmp_f:
                tmp_f.write(vinput.contents_of_file_to_verify)
                tmp_f.flush()
                path_to_file = Path(tmp_f.name)
                file_util.ensure_lines_at_beginning(
                    CbmcVerificationClient.DEFAULT_HEADERS_FOR_VERIFICATION, path_to_file
                )
                try:
                    vcommand = self._get_cbmc_verification_command(
                        vinput, path_to_file_to_verify=path_to_file
                    )
                    logger.debug(f"Running command: {vcommand}")
                    result = subprocess.run(vcommand, shell=True, capture_output=True, text=True)
                    # Normalize the temp file path in CBMC output so that LLM cache keys
                    # are deterministic across runs (temp file names are random).
                    path_str = str(path_to_file)
                    basename_str = path_to_file.name
                    stable_name = f"{function.name}.c"
                    normalized_stdout = result.stdout.replace(path_str, stable_name).replace(
                        basename_str, stable_name
                    )
                    normalized_stderr = result.stderr.replace(path_str, stable_name).replace(
                        basename_str, stable_name
                    )
                    self._cache[vinput] = VerificationResult(
                        vinput,
                        vcommand,
                        succeeded=result.returncode == 0,
                        stdout=normalized_stdout,
                        stderr=normalized_stderr,
                    )
                    logger.debug(f"Caching vresult for: {vinput.function}")
                except Exception as e:
                    msg = f"Error running command for function {function.name}: {e}"
                    raise RuntimeError(msg) from e
        vresult = self._cache[vinput]
        if vresult.succeeded:
            logger.success(f"Verification succeeded for function '{function.name}'")
        else:
            logger.error(f"Verification failed for function '{function.name}'")
        return vresult

    def _get_cbmc_verification_command(
        self,
        verification_input: VerificationInput,
        path_to_file_to_verify: Path,
    ) -> str:
        """Return the command used to verify a function in a file with CBMC.

        Args:
            verification_input (VerificationInput): The verification input.
            path_to_file_to_verify (Path): The path to the file to verify.

        Returns:
            str: The command used to verify a function in a file with CBMC.
        """
        function_name = verification_input.function.name
        callee_names = [callee.name for callee in verification_input.get_callees_to_specs()]
        replace_call_with_contract_args = " ".join(
            [f"--replace-call-with-contract {callee_name}" for callee_name in callee_names]
        )
        return " && ".join(
            [
                (
                    f"goto-cc -o {function_name}.goto {path_to_file_to_verify} "
                    f"--function {function_name}"
                ),
                (
                    f"goto-instrument --partial-loops --unwind 5 "
                    f"{function_name}.goto {function_name}.goto"
                ),
                (
                    f"goto-instrument {replace_call_with_contract_args} "
                    f"--enforce-contract {function_name} "
                    f"{function_name}.goto checking-{function_name}-contracts.goto"
                ),
                (
                    f"cbmc checking-{function_name}-contracts.goto "
                    f"--function {function_name} --depth 100"
                ),
            ]
        )
