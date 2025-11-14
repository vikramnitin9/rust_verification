"""Represents an iteration of generating a spec via an LLM and verifying it."""

from dataclasses import dataclass
from typing import Any

from specifications import LlmInvocationResult
from verification import Failure, Success


@dataclass(frozen=True)
class LlmGenerateVerifyIteration:
    """Represent one iteration of generating a specification via an LLM and verifying it.

    Attributes:
        function (str): The function under specification generation and verification.
        llm_invocation_result (LlmInvocationResult): The prompt to an LLM and the result obtained.
        verification_result (Success | Failure): The result of verifying the specifications in the
            file.
    """

    function: str
    llm_invocation_result: LlmInvocationResult
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
            "prompt": self.llm_invocation_result.prompt,
            "response": self.llm_invocation_result.response,
            "verification_result": verifier_result,
        }
