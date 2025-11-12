"""Module to encapsulate a prompt dispatched to an LLM and the subsequent response."""

from dataclasses import dataclass


@dataclass(frozen=True)
class LlmInvocationResult:
    """Represent the prompt dispatched to an LLM and the subsequent response.

    Attributes:
        prompt (str): The prompt dispatched to an LLM.
        response (str): The response from an LLM.
    """

    prompt: str
    response: str
