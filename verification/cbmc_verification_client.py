"""Client for verifying source code via CBMC."""

from pathlib import Path

from util import FunctionSpecification
from verification.proof_state import ProofState
from verification.verification_result import VerificationResult

from .verification_client import VerificationClient
from .verification_input import VerificationInput


class CbmcVerificationClient(VerificationClient):
    """Client for verifying source code via CBMC."""

    _cache: dict[VerificationInput, VerificationResult]

    def __init__(self, cache: dict[VerificationInput, VerificationResult]) -> None:
        """Create a new CbmcVerificationClient."""
        self._cache = cache

    def verify(
        self,
        function_name: str,
        names_of_verified_functions: list[str],
        names_of_trusted_functions: list[str],
        file_path: Path,
    ) -> VerificationResult:
        """TODO: document me.

        Args:
            function_name (str): _description_
            names_of_verified_functions (list[str]): _description_
            names_of_trusted_functions (list[str]): _description_
            file_path (Path): _description_

        Returns:
            VerificationResult: _description_
        """
        raise NotImplementedError()

    def verify_function_with_spec(
        self, function_name: str, spec: FunctionSpecification, proof_state: ProofState
    ) -> VerificationResult:
        """TODO: document me.

        Args:
            function_name (str): _description_
            spec (FunctionSpecification): _description_
            proof_state (ProofState): _description_

        Raises:
            NotImplementedError: _description_

        Returns:
            VerificationResult: _description_
        """
        raise NotImplementedError("Implement me")

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
