"""Module to encapsulate context for a specification generation/repair tasks."""

from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path

from loguru import logger

from util import ParsecFunction, ParsecResult


@dataclass
class SpecificationGenerationContext:
    """Class to encapsulate context for a specification generation/repair task for a function.

    Attributes:
        verified_functions (list[str]): The list of verified functions.
        parsec_result (ParsecResult): The ParseC result (updated with specifications from a task).
        output_file_path (Path): The path to the output file where function(s) with specs are
            written.
        function (ParsecFunction): The function for which to generate/repair specifications.
        _latest_verified_parsec_result (ParsecResult | None): The ParsecResult of the latest
            verified program.
        _latest_verified_program_content (str | None): The program content of the latest verified
            program content.
        generation_attempts (int): The number of times a set of specifications was generated for
            the function, from scratch.
        repair_attempts (int): The number of times a set of specifications was repaired for the
            function, from scratch.
    """

    verified_functions: list[str]
    parsec_result: ParsecResult
    output_file_path: Path
    function: ParsecFunction | None = None
    _latest_verified_parsec_result: ParsecResult | None = None
    _latest_verified_program_content: str | None = None
    generation_attempts: int = 0
    repair_attempts: int = 0

    def set_function(self, function: ParsecFunction) -> None:
        """Set this context's function, and reset the generation and repair attempts.

        Args:
            function (ParsecFunction): The function that this context's function should be set to.
        """
        self.function = function
        self.generation_attempts = 0
        self.repair_attempts = 0

    def get_function_name(self) -> str:
        """Return the name of this context's function.

        Raises:
            RuntimeError: Raised when this method is called before this context's function is set.

        Returns:
            str: The name of this context's function.
        """
        if not self.function:
            raise RuntimeError("A function was not set for this specification generation context")
        return self.function.name

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

    def reset_repair_attempts(self) -> None:
        """Set this context's repair attempts to 0."""
        self.repair_attempts = 0

    def checkpoint_successful_verification(self) -> None:
        """Set this context's latest verified ParsecResult and verified program content."""
        self._latest_verified_parsec_result = deepcopy(self.parsec_result)
        self._latest_verified_program_content = self.output_file_path.read_text(encoding="utf-8")

    def rollback_to_latest_verified_state(self) -> None:
        """Roll back this context to the latest verified program state.

        Raises:
            RuntimeError: Raised when rollback is attempted without a prior verified program state.
        """
        self.repair_attempts = 0
        if (
            self._latest_verified_parsec_result is not None
            and self._latest_verified_program_content is not None
        ):
            logger.debug("Rolling back to latest successful verification state")
            self.parsec_result = self._latest_verified_parsec_result
            self.function = self.parsec_result.get_function(self.get_function_name())
            self.output_file_path.write_text(
                self._latest_verified_program_content, encoding="utf-8"
            )
        else:
            raise RuntimeError(
                "Rollback is not possible when there is no prior program state that passed "
                "verification"
            )

    def has_successful_verification_state(self) -> bool:
        """Return True iff there is a prior program state that passed verification.

        Returns:
            bool: True iff there is a prior program state that passed verification.
        """
        return (
            self._latest_verified_parsec_result is not None
            and self._latest_verified_program_content is not None
        )
