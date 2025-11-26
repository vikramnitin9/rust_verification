"""Client for verifying source code via CBMC."""

import subprocess

from loguru import logger

from .specification_generation_context import SpecificationGenerationContext
from .verification_client import VerificationClient
from .verification_result import Failure, Success


class CbmcVerificationClient(VerificationClient):
    """Client for verifying source code via CBMC."""

    def verify(
        self, specification_generation_context: SpecificationGenerationContext
    ) -> Success | Failure:
        """Return the result of verifying the function in the context with CBMC.

        Args:
            specification_generation_context (SpecificationGenerationContext): The specification
                generation context to be used in verification.

        Raises:
            RuntimeError: Raised when an error occurs in executing the verification command.

        Returns:
            Success | Failure: Success if the function successfully verifies, Failure if the
                function does not verify.
        """
        function_name = specification_generation_context.get_function_name()

        replace_call_with_contract_args = "".join(
            [
                f"--replace-call-with-contract {f} "
                for f in specification_generation_context.verified_functions
            ]
        )
        verification_command = (
            f"goto-cc -o {function_name}.goto "
            f"{specification_generation_context.output_file_path.absolute()} --function "
            f"{function_name} && "
            f"goto-instrument --partial-loops --unwind 5 {function_name}.goto {function_name}.goto "
            f"&& goto-instrument {replace_call_with_contract_args} "
            f"--enforce-contract {function_name} "
            f"{function_name}.goto checking-{function_name}-contracts.goto && "
            f"cbmc checking-{function_name}-contracts.goto --function {function_name} --depth 100"
        )

        try:
            logger.debug(f"Running command: {verification_command}")
            result = subprocess.run(
                verification_command, shell=True, capture_output=True, text=True
            )
            if result.returncode == 0:
                return Success()
            return Failure(stdout=result.stdout, stderr=result.stderr)
        except Exception as e:
            msg = f"Error running command for function {function_name}: {e}"
            raise RuntimeError(msg) from e
