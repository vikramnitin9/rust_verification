"""Represents an iteration of generating a spec via an LLM and verifying it."""

from dataclasses import dataclass
from typing import Any

from util import LlmInvocationResult
from verification import Failure, Success

from .specification_generation_context import SpecificationGenerationContext


@dataclass
class GenerateRepairMetadata:
    """Represents a point in the specification generation/repair loop.

    Attributes:
        generation (int): The iteration of the generation loop.
        repair (int): The iteration of the repair loop.

    """

    generation: int
    repair: int

    def __init__(self, specgen_context: SpecificationGenerationContext):
        self.generation = specgen_context.generation_attempts
        self.repair = specgen_context.repair_attempts

    def __str__(self) -> str:
        """Return the string representation of this generate/repair metadata.

        Returns:
            str: The string representation of this generate/repair metadata.
        """
        return f"Generation attempt = {self.generation}, Repair attempt = {self.repair}"


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
    iteration_metadata: GenerateRepairMetadata
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
            "iteration_metadata": {
                "generation_attempt": self.iteration_metadata.generation,
                "repair_attempt": self.iteration_metadata.repair,
            },
            "verification_result": verifier_result,
        }
