"""Class representing a stubbed LLM backend, for testing."""

from models.conversation_message import ConversationMessage

from .llm_backend import LlmBackend


class StubLlmBackend(LlmBackend):
    """Class representing a stubbed LLM backend, for testing."""

    def __init__(self, model: str) -> None:
        """Create an instance of StubLlmBackend."""
        self.model = model

    def send_messages(
        self, messages: tuple[ConversationMessage, ...], temperature: float = 0, top_k: int = 1
    ) -> list[str]:
        """Stub method."""
        msg = "This method should not be invoked when testing with a cache."
        raise NotImplementedError(msg)
