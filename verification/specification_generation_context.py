"""Module to encapsulate context for a specification generation/repair tasks."""

from dataclasses import dataclass
from pathlib import Path

from util import ParsecResult


@dataclass
class SpecificationGenerationContext:
    """Class to encapsulate context for a specification generation/repair task for a function.

    Attributes:
        function_name (str): The function for which to generate/repair specifications.
        verified_functions (list[str]): The list of verified functions.
        parsec_result (ParsecResult): The ParseC result (updated with specifications from a task).
        output_file_path (Path): The path to the output file where function(s) with specs are
            written.
        generation_attempts (int): The number of times a set of specifications was generated for
            the function, from scratch.
        repair_attempts (int): The number of times a set of specifications was repaired for the
            function, from scratch.
    """

    function_name: str
    verified_functions: list[str]
    parsec_result: ParsecResult
    output_file_path: Path
    generation_attempts: int = 0
    repair_attempts: int = 0

    def add_verified_function(self, function_name: str) -> None:
        """Add the function name to this context's list of verified functions.

        Args:
            function_name (str): The function name to add to this context's list of verified
                functions.
        """
        self.verified_functions.append(function_name)

    def increment_generation_attempt(self) -> None:
        """Increment this context's generation attempts."""
        self.generation_attempts += 1

    def increment_repair_attempt(self) -> None:
        """Increment this context's repair attempts."""
        self.repair_attempts += 1
