"""Class to represent a specified function candidate/sample generated for verification."""

import shutil
from collections.abc import Iterator
from pathlib import Path

from util import ParsecFunction, ParsecResult, extract_function, file_util, function_util
from verification import Failure, Success, VerificationResult

from .llm_invocation_result import LlmInvocationResult


class SpecifiedFunctionSample:
    """Represent a specified function (i.e., a function with CBMC specifications).

    Attributes:
        function_name (str): The name of the function.
        specified_function (str): The implementation in source code of the specified function.
        path_to_file (Path): The path to the file in which this function is declared.
        parsec_result (ParsecResult): The Parsec result for this function sample.
        verification_result (VerificationResult | None): The result of verifying this function.

    """

    function_name: str
    specified_function: str
    path_to_file: Path
    parsec_result: ParsecResult
    verification_result: VerificationResult | None = None

    def __init__(
        self,
        function_name: str,
        specified_function: str,
        path_to_file: Path,
        verification_result: VerificationResult | None = None,
    ) -> None:
        self.function_name = function_name
        self.specified_function = specified_function
        self.path_to_file = path_to_file
        self.parsec_result = ParsecResult.parse_source_with_cbmc_annotations(path_to_file)
        self.verification_result = verification_result

    def __iter__(self) -> Iterator[str | Path]:
        """Return an iterator for this specified function sample.

        Returns:
            Iterator[(str, str)]: An iterator for this specified function sample.
        """
        return iter((self.specified_function, self.path_to_file))

    def get_parsec_representation(self) -> ParsecFunction:
        """Return the Parsec representation of this specified function sample.

        Raises:
            ValueError: Raised when the function is missing from the Parsec result.

        Returns:
            ParsecFunction: The Parsec representation of this specified function sample.
        """
        parsec_function = self.parsec_result.get_function(self.function_name)
        if not parsec_function:
            msg = f"'{self.function_name}' missing from Parsec Result"
            raise ValueError(msg)
        return parsec_function

    def delete_temporary_files(self) -> None:
        """Delete the temporary candidate files associated with this function sample."""
        parent_dir = self.path_to_file.parent
        if "specs" not in parent_dir.parts:
            raise ValueError(
                "Aborting temporary file deletion; 'specs' folder not found in temporary file path"
            )
        shutil.rmtree(self.path_to_file.parent)

    def is_verified(self) -> bool:
        """Return True iff the specified function successfully verifies.

        Returns:
            bool: True iff the specified function successfully verifies.
        """
        return isinstance(self.verification_result, Success)

    def get_num_verification_failures(self) -> int:
        """Return the number of failures reported by CBMC in verifying the function for this sample.

        Raises:
            ValueError: Raised when this sample's verification result is not set.

        Returns:
            int: The number of failures reported by CBMC in verifying the function for this sample.
        """
        if not self.verification_result:
            raise ValueError(
                "Cannot get the number of verification failures if a sample has not been verified"
            )
        if isinstance(self.verification_result, Failure):
            return self.verification_result.num_failures
        return 0

    @staticmethod
    def get_specified_function_samples(
        function_name: str,
        llm_invocation_result: LlmInvocationResult,
        parsec_result: ParsecResult,
        path_to_file: Path,
    ) -> list["SpecifiedFunctionSample"]:
        """Return specified function samples parsed from an LLM response.

        Note: The parsec_result and path_to_file are used to generate files where the
        candidate functions are inserted (keeping everything else unchanged).

        Args:
            function_name (str): The name of the function for which samples are being generated.
            llm_invocation_result (LlmInvocationResult): The LLM response to parse.
            parsec_result (ParsecResult): The parsec result.
            path_to_file (Path): The path to the file where the function is defined.

        Returns:
            list["SpecifiedFunctionSample"]: The specified function samples parsed from an LLM
                response.
        """
        samples = []
        for i, sample in enumerate(llm_invocation_result.responses):
            candidate_function = extract_function(sample)
            path_to_directory = file_util.get_directory_name_for_generated_code(
                path_to_file, function_name
            )
            path_to_candidate_file = (
                Path("specs")
                / path_to_directory
                / Path(f"sample_{i + 1}")
                / Path(f"sample{path_to_file.suffix}")
            )
            path_to_candidate_file = function_util.get_file_with_updated_function(
                function_name,
                candidate_function,
                parsec_result,
                original_src=path_to_file,
                path_to_candidate_file=path_to_candidate_file,
            )
            samples.append(
                SpecifiedFunctionSample(function_name, candidate_function, path_to_candidate_file)
            )
        return samples
