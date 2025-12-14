"""Represents an iteration of generating a spec via an LLM and verifying it."""

from dataclasses import dataclass
from typing import Any

from specifications.llm_invocation_result import LlmInvocationResult
from .verification_result import Failure, Success


@dataclass(frozen=True)
class LlmGenerateVerifyIteration:
    """Represent one iteration of generating a specification via an LLM and verifying it.

    Attributes:
        function (str): The name of the function being analyzed.
        llm_invocation_result (LlmInvocationResult): The prompt to an LLM and its response.
        verification_result (Success | Failure): The result of verifying the specifications in the
            response.
    """

    function: str
    llm_invocation_result: LlmInvocationResult
    verification_result: Success | Failure

    def to_dict(self: "LlmGenerateVerifyIteration") -> dict[str, Any]:
        """Return a dictionary representation of this class.

        Note: the dictionary representation of this class differs in how the `llm_invocation_result`
        is formatted. The `prompt` and `response` fields are top-level key-value pairs as opposed
        to being nested inside an object that maps to an `llm_invocation_result` key.

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
            "response": self.llm_invocation_result.responses,
            "verification_result": verifier_result,
        }
