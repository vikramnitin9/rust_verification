"""Module to represent the prompt dispatched to an LLM and the subsequent response."""

from dataclasses import dataclass


@dataclass(frozen=True)
class LlmInvocationResult:
    """Represent the prompt dispatched to an LLM and the subsequent response(s).

    The length of the list of responses depends on how many samples to take from the LLM.

    Attributes:
        prompt (str): The prompt dispatched to an LLM.
        responses (list[str]): The response(s) from an LLM.
    """

    prompt: str
    responses: list[str]
