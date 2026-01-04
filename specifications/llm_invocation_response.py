"""Module to represent the prompt dispatched to an LLM and the subsequent response."""

from dataclasses import dataclass


@dataclass(frozen=True)
class LlmInvocationResponse:
    """Represent the prompt dispatched to an LLM and the subsequent response.

    The response may comprise 1 or more samples (i.e., possible completions for the prompt).

    Attributes:
        prompt (str): The prompt dispatched to an LLM.
        samples (list[str]): The sample(s).
    """

    prompt: str
    # MDE: Should this be a tuple instead, since it is immutable?
    samples: list[str]
