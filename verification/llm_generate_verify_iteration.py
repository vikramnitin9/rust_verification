"""Represents an iteration of generating a spec via an LLM and verifying it."""

from dataclasses import dataclass
from typing import Any

from verification import Failure, Success


@dataclass(frozen=True)
class LlmGenerateVerifyIteration:
    """Represent one iteration of generating a specification via an LLM and verifying it.

    Attributes:
        function (str): The function under specification generation and verification.
        prompt (str): The prompt used to generate a specification.
        response (str): The response from the LLM.
        verification_result (Success | Failure): The result of verifying the specifications in the
            file.
    """

    function: str
    prompt: str
    response: str
    verification_result: Success | Failure

    def to_dict(self: "LlmGenerateVerifyIteration") -> dict[str, Any]:
        """Return a dictionary representation of this class.

        Args:
            self (LlmGenerateVerifyIteration): An instance of this class.

        Returns:
            dict[str, Any]: A dictionary representation of this class.
        """
        verifier_result = (
            {"result": "SUCCESS"}
            if isinstance(self.verification_result, Success)
            else {"result": "FAILURE", "error_message": self.verification_result.stderr}
        )
        return {
            "function": self.function,
            "prompt": self.prompt,
            "response": self.response,
            "verification_result": verifier_result,
        }
