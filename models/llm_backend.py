"""Protocol that defines a protocol for an LLM backend API."""

from typing import Protocol

from .conversation_message import ConversationMessage


class ModelError(Exception):
    """Represent errors related to LLM model instantiation."""


class GenerationError(Exception):
    """Represent errors related to LLM-based text generation."""


class LlmBackend(Protocol):
    """Protocol for an LLM backend API.

    Attributes:
        model (str): The name of the model that is used in this backend.
    """

    model: str

    def send_messages(
        self, messages: tuple[ConversationMessage, ...], temperature: float = 0, top_k: int = 1
    ) -> list[str]:
        """Return the response from calling an LLM API with the given parameters.

        Args:
            messages (tuple[ConversationMessage, ...]): The messages to send to the LLM API.
            temperature (float, optional): The temperature with which to invoke text generation.
                Defaults to 0.
            top_k (int, optional): The number of responses to sample from the model. Defaults to 1.

        Returns:
            list[str]: The response(s) from the model. The number of items should be equal to
                `top_k `.
        """
        ...
