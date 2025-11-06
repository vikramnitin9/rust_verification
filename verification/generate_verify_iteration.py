"""Module to represent an iteration of generating and verifying a specification."""

from dataclasses import dataclass

from verification import Failure, Success


@dataclass(frozen=True)
class GenerateVerifyIteration:
    """Represent one iteration of generating and verifying a specification.

    Attributes:
        prompt (str): The prompt used to generate a specification.
        file_content (str): The content of the file, updated with the specification.
        verification_result (Success | Failure): The result of verifying the specifications in the
            file.
    """

    prompt: str
    file_content: str
    verification_result: Success | Failure
