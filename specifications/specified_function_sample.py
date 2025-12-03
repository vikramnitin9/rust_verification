"""Class to represent a specified function candidate/sample generated for verification."""

from collections.abc import Iterator
from pathlib import Path

from util import ParsecResult, extract_function, function_util
from verification import Success, VerificationResult

from .llm_invocation_result import LlmInvocationResult


class SpecifiedFunctionSample:
    """Represent a specified function (i.e., a function with CBMC specifications).

    Attributes:
        function_name (str): The name of the function.
        specified_function (str): The implementation in source code of the specified function.
        path_to_file (Path): The path to the file in which this function is declared.
        verification_result (VerificationResult | None): The result of verifying this function.

    """

    function_name: str
    specified_function: str
    path_to_file: Path
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
        self.verification_result = verification_result

    def __iter__(self) -> Iterator[str | Path]:
        """Return an iterator for this specified function sample.

        Returns:
            Iterator[(str, str)]: An iterator for this specified function sample.
        """
        return iter((self.specified_function, self.path_to_file))

    def is_verified(self) -> bool:
        """Return True iff the specified function successfully verifies.

        Returns:
            bool: True iff the specified function successfully verifies.
        """
        return isinstance(self.verification_result, Success)

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
        for sample in llm_invocation_result.responses:
            candidate_function = extract_function(sample)
            path_to_candidate_file = function_util.get_file_with_updated_function(
                function_name, candidate_function, parsec_result, path_to_file
            )
            samples.append(
                SpecifiedFunctionSample(function_name, candidate_function, path_to_candidate_file)
            )
        return samples
