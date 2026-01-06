"""Verifies source code using CBMC."""

import subprocess
import tempfile
from pathlib import Path

from diskcache import Cache  # ty: ignore
from loguru import logger

from util import CFunction, FunctionSpecification
from verification.proof_state import ProofState
from verification.verification_result import VerificationResult

from .verification_client import VerificationClient
from .verification_input import VerificationInput


class CbmcVerificationClient(VerificationClient):
    """Verifies source code using CBMC. The entry point is `verify()`.

    Attributes:
        _cache (Cache): A cache of verification results mapped to verification inputs. The keys for
            VERIFIER_CACHE are `VerificationInput` and the values are `VerificationResult`.
    """

    _cache: Cache

    def __init__(
        self,
        cache: Cache,
    ) -> None:
        """Create a new CbmcVerificationClient."""
        self._cache = cache

    def verify(
        self,
        function: CFunction,
        spec: FunctionSpecification,
        proof_state: ProofState,
        source_code_content: str,
    ) -> VerificationResult:
        """Return the result of verifying the given function.

        Args:
            function (CFunction): The function to verify.
            spec (FunctionSpecification): The specification for the function to verify.
            proof_state (ProofState): The proof state.
            source_code_content (str): The source code content.
                # MDE: Should this be in the CFunction abstraction?

        Returns:
            VerificationResult: The result of verifying the given function.
        """
        with tempfile.NamedTemporaryFile(mode="w+t", prefix=function.name, suffix=".c") as tmp_f:
            tmp_f.write(source_code_content)
            tmp_f.seek(0)
            path_to_file = Path(tmp_f.name)
            vinput = VerificationInput(
                function=function,
                spec=spec,
                context=proof_state.get_current_context(function=function),
                contents_of_file_to_verify=source_code_content,
            )
            if vinput not in self._cache:
                logger.debug(f"vresult cache miss for: {vinput.function}")
                vcommand = self._get_cbmc_verification_command(
                    vinput, path_to_file_to_verify=path_to_file, proof_state=proof_state
                )
                try:
                    logger.debug(f"Running command: {vcommand}")
                    result = subprocess.run(vcommand, shell=True, capture_output=True, text=True)
                    failure_messages = (
                        None
                        if result.returncode == 0
                        else f"STDOUT: {result.stdout}\nSTDERR: {result.stderr}"
                    )
                    self._cache[vinput] = VerificationResult(
                        vinput, succeeded=result.returncode == 0, failure_messages=failure_messages
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
            return self._cache[vinput]

    def _get_cbmc_verification_command(
        self,
        verification_input: VerificationInput,
        path_to_file_to_verify: Path,
        proof_state: ProofState,
    ) -> str:
        """Return the command used to verify a function in a file with CBMC.

        Args:
            verification_input (VerificationInput): The verification input.
            path_to_file_to_verify (Path): The path to the file to verify.
            proof_state (ProofState): The proof state under which verification is occurring.

        Returns:
            str: The command used to verify a function in a file with CBMC.
        """
        function_name = verification_input.function.name
        # MDE: Do we want to replace *every* function (except the one being verified) by its current
        # specification, whether or not it is verified/assumed?  Please discuss.
        replace_call_with_contract_args = " ".join(
            [
                f"--replace-call-with-contract {previously_verified_function.name}"
                for previously_verified_function in proof_state.get_specifications()
            ]
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
