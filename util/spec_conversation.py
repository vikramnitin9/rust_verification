"""Class to represent an LLM-generated specification and the conversation that led to it."""

from models import ConversationMessage, LlmMessage

from .function_specification import FunctionSpecification
from .specification_generation_next_step import SpecificationGenerationNextStep


class SpecConversation:
    """Class to represent an LLM-generated specification and the conversation that led to it.

    INVARIANT: the last key-value pair in `conversation` is the latest response from the LLM.

    Attributes:
        specification (FunctionSpecification): The LLM-generated specification.
        conversation (list[ConversationMessage]): The conversation that resulted in the
            specification.
        specgen_next_step (SpecificationGenerationNextStep | None): The next step in the
            specification generation process. Defaults to None until a verifier is executed. The
            message that is parsed to populate this field exists in the conversation. The value of
            `specgen_next_step` is used to create the next proof state in a step of the
            generate/repair spec process.
        contents_of_file_to_verify (str | None): The content of the file to be verified.

    # MDE: Should the CFunction be part of this datatype?
    """

    specification: FunctionSpecification
    conversation: list[ConversationMessage]
    specgen_next_step: SpecificationGenerationNextStep | None
    contents_of_file_to_verify: str | None

    def __init__(
        self,
        specification: FunctionSpecification,
        conversation: list[ConversationMessage],
        specgen_next_step: SpecificationGenerationNextStep | None = None,
        contents_of_file_to_verify: str | None = None,
    ) -> None:
        """Create a new SpecConversation."""
        self.specification = specification
        self.conversation = conversation
        self.specgen_next_step = specgen_next_step
        self.contents_of_file_to_verify = contents_of_file_to_verify

    def get_conversation_with_message_appended(
        self, message: ConversationMessage
    ) -> list[ConversationMessage]:
        """Return a copy of this SpecConversation's conversation with the given message appended.

        Args:
            message (ConversationMessage): The message to append to the end of the conversation.

        Returns:
            list[ConversationMessage]: A copy of this SpecConversation's conversation field with the
                message appended.
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
        if isinstance(latest_message_in_conversation, LlmMessage):
            return latest_message_in_conversation.content
        # Note: The "role" being "assistant" for LLM responses should be consistent
        # for any API that are compatible with the OpenAI SDK, but others may be different.
        msg = (
            "Invariant violation: expected the last message "
            f"{latest_message_in_conversation} to originate from an LLM, but had role = "
            f"'{latest_message_in_conversation.role}'"
        )
        raise ValueError(msg)

    def has_next_step(self) -> bool:
        """Return True iff this conversation has a next step.

        Returns:
            bool: True iff this conversation has a next step.
        """
        return self.specgen_next_step is not None
