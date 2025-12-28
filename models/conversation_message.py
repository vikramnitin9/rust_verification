"""Classes to represent messages in an LLM conversation."""

from dataclasses import dataclass


@dataclass(frozen=True)
class ConversationMessage:
    """Represents a message in a conversation.

    Attributes:
        content (str): The content of a message (i.e., the actual prompt).
        role (str): Denotes the provenance of a message (e.g., "user", "system").
    """

    content: str
    role: str = ""

    def __post_init__(self) -> None:
        """Prevent direct instantiation of ConversationMessage."""
        if type(self) is ConversationMessage:
            msg = "'ConversationMessage' should be treated as an abstract class"
            raise TypeError(msg)

    def to_dict(self) -> dict[str, str]:
        """Return a dictionary representation of this conversation message.

        Returns:
            dict[str, str]: A dictionary representation of this conversation message.
        """
        return {"role": self.role, "content": self.content}


@dataclass(frozen=True)
class UserMessage(ConversationMessage):
    """Represents a message originating from a user (i.e., non-LLM entity) in a conversation."""

    role: str = "user"


@dataclass(frozen=True)
class LlmMessage(ConversationMessage):
    """Represents a message sent by an LLM in a conversation."""

    role: str = "assistant"


@dataclass(frozen=True)
class SystemMessage(ConversationMessage):
    """Represents a message meant to be a system prompt in a conversation."""

    role: str = "system"
