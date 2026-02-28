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
                file = Path(tmp_f.name)
                file_util.ensure_lines_at_beginning(
                    CbmcVerificationClient.DEFAULT_HEADERS_FOR_VERIFICATION, file
                )
                try:
                    vcommands = self._get_cbmc_verification_commands(vinput, file_to_verify=file)
                    logger.debug(f"Running command: {vcommands[0]}")
                    result = subprocess.run(vcommands[0], capture_output=True, text=True)
                    for vcommand in vcommands[1:]:
                        if result.returncode != 0:
                            break
                        logger.debug(f"Running command: {vcommand}")
                        result = subprocess.run(vcommand, capture_output=True, text=True)
                    # Normalize the temp file path in CBMC output so that LLM cache keys
                    # are deterministic across runs (temp file names are random).
                    normalized_stdout = text_util.normalize_cbmc_output_paths(
                        result.stdout, function.name, temp_file_path=str(file)
                    )
                    normalized_stderr = text_util.normalize_cbmc_output_paths(
                        result.stderr, function.name, temp_file_path=str(file)
                    )
                    self._cache[vinput] = VerificationResult(
                        vinput,
                        vcommands,
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

    def _get_cbmc_verification_commands(
        self,
        verification_input: VerificationInput,
        file_to_verify: Path,
    ) -> list[list[str]]:
        """Return the command used to verify a function in a file with CBMC.

        Args:
            verification_input (VerificationInput): The verification input.
            file_to_verify (Path): The path to the file to verify.

        Returns:
            list[list[str]]: The commands used to verify a function in a file with CBMC.
        """
        function_name = verification_input.function.name
        callee_names = [callee.name for callee in verification_input.get_callees_to_specs()]
        replace_call_with_contract_args = [
            arg
            for callee_name in callee_names
            for arg in ("--replace-call-with-contract", callee_name)
        ]
        return [
            [
                "goto-cc",
                "-o",
                f"{function_name}.goto",
                # These seemingly gratuitous f-strings are necessary for type-checking:
                # they convert a Path into a string.
                f"{file_to_verify}",
                "--function",
                f"{function_name}",
            ],
            [
                "goto-instrument",
                "--partial-loops",
                "--unwind",
                "5",
                f"{function_name}.goto",
                f"{function_name}.goto",
            ],
            [
                "goto-instrument",
                *replace_call_with_contract_args,
                "--enforce-contract",
                function_name,
                f"{function_name}.goto",
                f"checking-{function_name}-contracts.goto",
            ],
            [
                "cbmc",
                f"checking-{function_name}-contracts.goto",
                "--function",
                function_name,
                "--depth",
                "100",
            ],
        ]
