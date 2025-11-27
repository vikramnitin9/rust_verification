"""Client for verifying source code via CBMC."""

import subprocess
from pathlib import Path

from loguru import logger

from util import text_util

from .verification_client import VerificationClient
from .verification_result import Failure, Success


class CbmcVerificationClient(VerificationClient):
    """Client for verifying source code via CBMC."""

    def verify(
        self,
        function_name: str,
        names_of_verified_functions: list[str],
        names_of_trusted_functions: list[str],
        file_path: Path,
    ) -> Success | Failure:
        """Return the result of verifying the function named `function_name` with CBMC.

        Args:
            function_name (str): The name of the function to verify with CBMC.
            names_of_verified_functions (list[str]): The names of functions that have been verified
                with CBMC.
            names_of_trusted_functions (list[str]): The names of functions that are trusted by CBMC
                (i.e., their specifications are trusted, not verified.)
            file_path (Path): The path to the file in which the function to verify is defined.

        Raises:
            RuntimeError: Raised when an error occurs in executing the verification command.

        Returns:
            Success | Failure: Success if the function successfully verifies, Failure if the
                function does not verify.
        """
        replace_call_with_contract_args = "".join(
            [
                f"--replace-call-with-contract {f} "
                for f in names_of_verified_functions + names_of_trusted_functions
            ]
        )
        verification_command = (
            f"goto-cc -o {function_name}.goto {file_path.absolute()} --function {function_name} && "
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
            lines_with_failure = text_util.get_lines_with_suffix(
                text=result.stdout, suffix="FAILURE"
            )
            return Failure(
                stdout=result.stdout, stderr=result.stderr, num_failures=len(lines_with_failure)
            )
        except Exception as e:
            msg = f"Error running command for function {function_name}: {e}"
            raise RuntimeError(msg) from e
