"""Verifies source code using CBMC."""

import subprocess
import tempfile
from collections.abc import Sequence
from pathlib import Path

from diskcache import Cache
from loguru import logger

from util import file_util, text_util
from verification.verification_result import VerificationResult

from .avocado_stub_util import AvocadoIdentifierRenamer, RenameResult
from .verification_client import VerificationClient
from .verification_input import VerificationInput


class CbmcVerificationClient(VerificationClient):
    """Verifies source code using CBMC. The entry point is `verify()`.

    Attributes:
        _cache (Cache | None): A cache of verification results mapped to verification inputs. The
            keys for this cache are `VerificationInput` and the values are `VerificationResult`.
        _avocado_identifier_renamer (AvocadoIdentifierRenamer): Used to rename ANSI-C library
            function identifiers in C source code to their Avocado identifiers.
            See `avocado_stub_util.py` for details.

    """

    _cache: Cache | None
    _avocado_identifier_renamer: AvocadoIdentifierRenamer

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
        self._avocado_identifier_renamer = AvocadoIdentifierRenamer()

    def verify(self, vinput: VerificationInput) -> VerificationResult:
        """Return the result of verifying the given verification input.

        Args:
            vinput (VerificationInput): The verification input.

        Returns:
            VerificationResult: The result of verifying the given verification input.
        """
        if self._cache is None:
            vresult = self._run_verifier(vinput)
        elif vinput in self._cache:
            vresult = self._cache[vinput]
        else:
            logger.debug(f"vresult cache miss for: {vinput.function}")
            vresult = self._run_verifier(vinput)
            logger.debug(f"Caching vresult for: {vinput.function}")
            self._cache[vinput] = vresult

        if vresult.succeeded:
            logger.success(f"Verification succeeded for function '{vinput.function.name}'")
        else:
            logger.error(f"Verification failed for function '{vinput.function.name}'")
        return vresult

    def _run_verifier(self, vinput: VerificationInput) -> VerificationResult:
        with tempfile.NamedTemporaryFile(
            mode="w+t", prefix=vinput.function.name, suffix=".c"
        ) as tmp_f:
            rename_result = (
                self._avocado_identifier_renamer.rename_ansi_identifiers_to_avocado_identifiers(
                    vinput.contents_of_file_to_verify
                )
            )
            tmp_f.write(rename_result.src_after_renaming)
            tmp_f.flush()
            file = Path(tmp_f.name)
            headers_for_verification = rename_result.get_headers_for_renamed_functions().union(
                CbmcVerificationClient.DEFAULT_HEADERS_FOR_VERIFICATION
            )
            include_header_lines = [f"#include <{header}>" for header in headers_for_verification]
            file_util.ensure_lines_at_beginning(include_header_lines, file)
            try:
                vcommand = self._get_cbmc_verification_command(
                    vinput, rename_result, path_to_file_to_verify=file
                )
                logger.debug(f"Running command: {vcommand}")
                result = subprocess.run(
                    vcommand, capture_output=True, text=True, shell=True, check=False
                )
                # Normalize the temp file path in CBMC output so that LLM cache keys
                # are deterministic across runs (temp file names are random).
                normalized_stdout = text_util.normalize_cbmc_output_paths(
                    result.stdout, vinput.function.name, temp_file_path=str(file)
                )
                normalized_stderr = text_util.normalize_cbmc_output_paths(
                    result.stderr, vinput.function.name, temp_file_path=str(file)
                )
                return VerificationResult(
                    vinput,
                    vcommand,
                    succeeded=result.returncode == 0,
                    stdout=normalized_stdout,
                    stderr=normalized_stderr,
                )
            except Exception as e:
                msg = f"Error running command for function {vinput.function.name}: {e}"
                raise RuntimeError(msg) from e

    def _get_cbmc_verification_command(
        self,
        verification_input: VerificationInput,
        rename_result: RenameResult,
        path_to_file_to_verify: Path,
    ) -> str:
        """Return the command used to verify a function in a file with CBMC.

        Args:
            verification_input (VerificationInput): The verification input.
            rename_result (RenameResult): The rename result.
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
        path_to_avocado_stub_files = " ".join(
            rename_result.get_stub_file_paths(
                default_headers=list(CbmcVerificationClient.DEFAULT_HEADERS_FOR_VERIFICATION)
            )
        )
        return " && ".join(
            [
                (
                    f"goto-cc -o {function_name}.goto "
                    f"{path_to_avocado_stub_files} "
                    f"{path_to_file_to_verify} "
                    f"--function {function_name}"
                ),
                (
                    f"goto-instrument --partial-loops --unwind 5 "
                    f"{function_name}.goto {function_name}.goto"
                ),
                (
                    f"goto-instrument "
                    f"{
                        ' ' + replace_call_with_contract_args
                        if replace_call_with_contract_args
                        else ''
                    } "
                    f"--enforce-contract {function_name} "
                    f"{function_name}.goto checking-{function_name}-contracts.goto"
                ),
                (
                    f"cbmc checking-{function_name}-contracts.goto "
                    f"--function {function_name} --depth 100"
                ),
            ]
        )
