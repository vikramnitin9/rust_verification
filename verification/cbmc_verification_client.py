"""Verifies source code using CBMC."""

import subprocess
import tempfile
from collections.abc import Sequence
from pathlib import Path

from diskcache import Cache  # ty: ignore
from loguru import logger

from util import file_util, text_util
from verification.verification_result import VerificationResult

from .verification_client import VerificationClient
from .verification_input import VerificationInput


class CbmcVerificationClient(VerificationClient):
    """Verifies source code using CBMC. The entry point is `verify()`.

    Attributes:
        _cache (Cache | None): A cache of verification results mapped to verification inputs. The
            keys for this cache are `VerificationInput` and the values are `VerificationResult`.
    """

    _cache: Cache | None

    # These headers should be inserted into each file that is input to the verifier;
    # generated specs often use constants from these headers (e.g., INT_MAX) assuming they already
    # exist in the file.
    DEFAULT_HEADERS_FOR_VERIFICATION: Sequence[str] = (
        "stdlib.h",
        "limits.h",
    )

    def __init__(
        self,
        cache: Cache | None,
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
        if self._cache is None:
            return self._run_verifier(vinput)

        if vinput in self._cache:
            return self._cache[vinput]

        logger.debug(f"vresult cache miss for: {vinput.function}")
        vresult = self._run_verifier(vinput)
        self._cache[vinput] = vresult
        return vresult

    def _run_verifier(self, vinput: VerificationInput) -> VerificationResult:
        with tempfile.NamedTemporaryFile(
            mode="w+t", prefix=vinput.function.name, suffix=".c"
        ) as tmp_f:
            tmp_f.write(vinput.contents_of_file_to_verify)
            tmp_f.flush()
            file = Path(tmp_f.name)
            default_header_include_lines = [
                f"#include <{header}>"
                for header in CbmcVerificationClient.DEFAULT_HEADERS_FOR_VERIFICATION
            ]
            file_util.ensure_lines_at_beginning(default_header_include_lines, file)
            try:
                vcommand = self._get_cbmc_verification_command(vinput, path_to_file_to_verify=file)
                logger.debug(f"Running command: {vcommand}")
                result = subprocess.run(vcommand, capture_output=True, text=True, shell=True)
                # Normalize the temp file path in CBMC output so that LLM cache keys
                # are deterministic across runs (temp file names are random).
                normalized_stdout = text_util.normalize_cbmc_output_paths(
                    result.stdout, vinput.function.name, temp_file_path=str(file)
                )
                normalized_stderr = text_util.normalize_cbmc_output_paths(
                    result.stderr, vinput.function.name, temp_file_path=str(file)
                )
                vresult = VerificationResult(
                    vinput,
                    vcommand,
                    succeeded=result.returncode == 0,
                    stdout=normalized_stdout,
                    stderr=normalized_stderr,
                )
                if vresult.succeeded:
                    logger.success(f"Verification succeeded for function '{vinput.function.name}'")
                else:
                    logger.error(f"Verification failed for function '{vinput.function.name}'")
                return vresult
            except Exception as e:
                msg = f"Error running command for function {vinput.function.name}: {e}"
                raise RuntimeError(msg) from e

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
        replace_call_with_contract_args = (
            ""
            if not callee_names
            else " ".join(
                [
                    arg
                    for callee_name in callee_names
                    for arg in ("--replace-call-with-contract", callee_name)
                ]
            )
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
