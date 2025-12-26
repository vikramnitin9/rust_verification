"""Client for verifying source code via CBMC."""

import subprocess
import tempfile
from pathlib import Path

from loguru import logger

from util import CFunction, FunctionSpecification
from verification.proof_state import ProofState
from verification.verification_result import VerificationResult

from .verification_client import VerificationClient
from .verification_context_manager import VerificationContextManager
from .verification_input import VerificationInput


class CbmcVerificationClient(VerificationClient):
    """Client for verifying source code via CBMC."""

    _cache: dict[VerificationInput, VerificationResult]
    _context_manager: VerificationContextManager

    def __init__(
        self,
        cache: dict[VerificationInput, VerificationResult],
        context_manager: VerificationContextManager,
    ) -> None:
        """Create a new CbmcVerificationClient."""
        self._cache = cache
        self._context_manager = context_manager

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

        Returns:
            VerificationResult: The result of verifying the given function.
        """
        with tempfile.NamedTemporaryFile(mode="w+t", prefix=function.name, suffix=".c") as tmp_f:
            tmp_f.write(source_code_content)
            tmp_f.seek(0)
            path_to_file = Path(tmp_f.name)
            current_context = self._context_manager.current_context(
                function=function,
                proof_state=proof_state,
            )
            vinput = VerificationInput(
                function=function,
                spec=spec,
                context=current_context,
                contents_of_file_to_verify=source_code_content,
            )
            if vinput not in self._cache:
                logger.debug(f"vresult was not cached for: {vinput}")
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
                    logger.debug(f"Cached vresult for: {vinput}")
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
            proof_state (ProofState): The proof state to verify under.

        Returns:
            str: The command used to verify a function in a file with CBMC.
        """
        function_name = verification_input.function.name
        replace_call_with_contract_args = "".join(
            [
                f"--replace-call-with-contract {f} "
                for f in proof_state.get_assumed_functions() + proof_state.get_verified_functions()
            ]
        )
        return (
            f"goto-cc -o {function_name}.goto {path_to_file_to_verify} --function {function_name} && "  # noqa : E501
            f"goto-instrument --partial-loops --unwind 5 {function_name}.goto {function_name}.goto "
            f"&& goto-instrument {replace_call_with_contract_args} "
            f"--enforce-contract {function_name} "
            f"{function_name}.goto checking-{function_name}-contracts.goto && "
            f"cbmc checking-{function_name}-contracts.goto --function {function_name} --depth 100"
        )
