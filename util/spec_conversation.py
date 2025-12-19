"""Class to represent an LLM-generated specification and the conversation that led to it."""

from dataclasses import dataclass

from .backtracking_strategy import BacktrackingStrategy
from .function_specification import FunctionSpecification


@dataclass(frozen=True)
class SpecConversation:
    """Class to represent an LLM-generated specification and the conversation that led to it.

    INVARIANT: the last key-value pair in conversation is the latest response from the LLM.

    Attributes:
        specification (FunctionSpecification): The LLM-generated specification.
        conversation (list[dict[str, str]]): The conversation that resulted in the specification.
        backtracking_strategy (BacktrackingStrategy | None): The backtracking strategy associated
            with the specification.
    """

    specification: FunctionSpecification
    conversation: list[dict[str, str]]
    backtracking_strategy: BacktrackingStrategy | None = None

    def get_conversation_with_message_appended(
        self, message: dict[str, str]
    ) -> list[dict[str, str]]:
        """Return a copy of this SpecConversation's conversation field with the message appended.

        Args:
            message (dict[str, str]): The message to append to the conversation field.

        Returns:
            list[dict[str, str]]: A copy of this SpecConversation's conversation field with the
                message appended.
        """
        return [*self.conversation, message]

    def get_latest_llm_response(self) -> str:
        """Return the latest LLM response in this specification's associated conversation.

        Raises:
            ValueError: Raised when the latest message in this specification's associated
                conversation does not originate from an LLM.

        Returns:
            str: The latest LLM response in this specification's associated conversation.
        """
        latest_message_in_conversation = self.conversation[-1]
        if latest_message_in_conversation["role"] != "assistant":
            # Note: The "role" being "assistant" for LLM responses should be consistent
            # for any API that are compatible with the OpenAI SDK, but others may be different.
            msg = (
                "Invariant violation: expected the last message "
                f"{latest_message_in_conversation} to originate from an LLM, but had role = "
                f"'{latest_message_in_conversation['role']}'"
            )
            raise ValueError(msg)
        return latest_message_in_conversation["content"]
