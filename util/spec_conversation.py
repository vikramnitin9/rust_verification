"""Class to represent an LLM-generated specification and the conversation that led to it."""

from .backtracking_strategy import BacktrackingStrategy
from .function_specification import FunctionSpecification


class SpecConversation:
    """Class to represent an LLM-generated specification and the conversation that led to it.

    INVARIANT: the last key-value pair in `conversation` is the latest response from the LLM.

    Attributes:
        specification (FunctionSpecification): The LLM-generated specification.
        conversation (list[dict[str, str]]): The conversation that resulted in the specification.
        backtracking_strategy (BacktrackingStrategy | None): The backtracking strategy associated
            with the specification.
            # MDE: Does the backtracking strategy also appear in the conversation?
            # MDE: How is the backtracking strategy used?
        contents_of_file_to_verify (str | None): The content of the file to be verified.

    # MDE: Should the CFunction be part of this datatype?
    """

    specification: FunctionSpecification
    conversation: list[dict[str, str]]
    backtracking_strategy: BacktrackingStrategy | None
    contents_of_file_to_verify: str | None

    def __init__(
        self,
        specification: FunctionSpecification,
        conversation: list[dict[str, str]],
        backtracking_strategy: BacktrackingStrategy | None = None,
        contents_of_file_to_verify: str | None = None,
    ) -> None:
        """Create a new SpecConversation."""
        self.specification = specification
        self.conversation = conversation
        self.backtracking_strategy = backtracking_strategy
        self.contents_of_file_to_verify = contents_of_file_to_verify

    def get_conversation_with_message_appended(
        self, message: dict[str, str]
    ) -> list[dict[str, str]]:
        """Return a copy of this SpecConversation's conversation with the given message appended.

        Args:
            message (dict[str, str]): The message to append to the conversation field.
                # MDE: Is this a singleton map?

        Returns:
            list[dict[str, str]]: A copy of this SpecConversation's conversation field with the
                message appended.
                # MDE: is each dict a singleton map?  Or maybe it has size two where one slot is
                # "role" and the other is "content"?  If so, maybe ONLY WITHIN OUR CODEBASE it
                # should be a datatype of its own (a "ConversationRound" or ""ConversationMessage")
                # with subtypes "UserMessage" and "LlmMessage").  This would provide better
                # abstraction.  A negative is that we would need to convert into the dict/JSON that
                # the LLM needs, but that would only have to be done at one place in the codebase.
        """
        return [*self.conversation, message]

    def get_latest_llm_response(self) -> str:
        """Return the latest LLM response in this specification's associated conversation.

        Raises:
            ValueError: Raised when the latest message in this specification's associated
                conversation does not originate from an LLM response, or if the conversation is
                empty.

        Returns:
            str: The latest LLM response in this specification's associated conversation.
        """
        if not self.conversation:
            raise ValueError("SpecConversation had an empty conversation")
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
