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
        msg = (
            "Unexpected conversation while testing with a cache:\n\n"
            f"{messages}\n"
            "End of unexpected conversation while testing with a cache.\n"
        )
        # TODO: When this error is raised, no traceback should be shown by callers.
        raise NotImplementedError(msg)
