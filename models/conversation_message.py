"""Classes to represent messages in an LLM conversation."""

import abc
from dataclasses import dataclass


@dataclass
class ConversationMessage(abc.ABC):
    """Represents a message (either from an LLM or a user) in a conversation.

    Attributes:
        role (str): Denotes the provenance of a message (e.g., "user", "system").
        content (str): The content of a message (i.e., the actual prompt).
    """

    role: str
    content: str

    @abc.abstractmethod
    def __init__(self):
        """Create a ConversationMessage.

        Note: This is a no-op init method explicitly marked with @abstractmethod to disallow
        instantiation of this abstract parent class.
        """

    def to_dict(self) -> dict[str, str]:
        """Return a dictionary representation of this conversation message.

        Returns:
            dict[str, str]: A dictionary representation of this conversation message.
        """
        return {"role": self.role, "content": self.content}


class UserMessage(ConversationMessage):
    """Represents a message originating from a user (i.e., non-LLM entity) in a conversation."""

    def __init__(self, content: str) -> None:
        """Create a UserMessage."""
        self.role = "user"
        self.content = content


class LlmMessage(ConversationMessage):
    """Represents a message sent by an LLM in a conversation."""

    def __init__(self, content: str) -> None:
        """Create a LlmMessage."""
        self.role = "assistant"
        self.content = content


class SystemMessage(ConversationMessage):
    """Represents a message meant to be a system prompt in a conversation."""

    def __init__(self, content: str) -> None:
        """Create a SystemMessage."""
        self.role = "system"
        self.content = content
