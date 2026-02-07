"""Class to represent an LLM-generated specification and the conversation that led to it."""

from types import MappingProxyType
from typing import Self

from models import ConversationMessage, LlmMessage

from .c_function import CFunction
from .function_specification import FunctionSpecification
from .function_util import get_source_content_with_specifications
from .parsec_project import ParsecProject
from .specification_generation_next_step import SpecificationGenerationNextStep


class SpecConversation:
    """Class to represent an LLM-generated specification and the conversation that led to it.

    Attributes:
        function (CFunction): The function for which the specification was generated.
        specification (FunctionSpecification): The LLM-generated specification.
        conversation (tuple[ConversationMessage, ...]): The conversation that resulted in the
            specification.  The last message is the latest response from the LLM.
        contents_of_file_to_verify (str | None): The content of the file to be verified.
        next_step (SpecificationGenerationNextStep | None): The next step in the specification
            generation process. Its value is set upon a successful verification run, or when an LLM
            produces a backtracking decision (on a spec that fails repair).
    """

    function: CFunction
    specification: FunctionSpecification
    conversation: tuple[ConversationMessage, ...]
    contents_of_file_to_verify: str
    next_step: SpecificationGenerationNextStep | None

    def __init__(
        self,
        function: CFunction,
        specification: FunctionSpecification,
        conversation: tuple[ConversationMessage, ...],
        contents_of_file_to_verify: str,
        next_step: SpecificationGenerationNextStep | None = None,
    ) -> None:
        """Create a new SpecConversation."""
        self.function = function
        self.specification = specification
        self.conversation = conversation
        self.next_step = next_step
        self.contents_of_file_to_verify = contents_of_file_to_verify

    @classmethod
    def create(
        cls,
        function: CFunction,
        specification: FunctionSpecification,
        conversation: tuple[ConversationMessage, ...],
        parsec_project: ParsecProject,
        existing_specs: MappingProxyType[CFunction, FunctionSpecification],
    ) -> Self:
        """Alternative constructor for SpecConversation.

        Args:
            function (CFunction): The CFunction for which specifications were generated.
            specification (FunctionSpecification): The specifications generated for the CFunction.
            conversation (tuple[ConversationMessage, ...]): The conversation from which the
                specifications were generated.
            parsec_project (ParsecProject): The ParseC project that contains `function`.
            existing_specs (MappingProxyType[CFunction, FunctionSpecification]): The existing
                specs.

        Returns:
            Self: A SpecConversation.
        """
        callees_to_specs = {
            callee: spec
            for callee in parsec_project.get_callees(function=function)
            if (spec := existing_specs.get(callee))
        }
        functions_with_specs = {function: specification} | callees_to_specs

        source_file_to_verify = get_source_content_with_specifications(
            specified_functions=functions_with_specs,
            parsec_project=parsec_project,
        )
        return cls(
            function=function,
            specification=specification,
            conversation=tuple(conversation),
            contents_of_file_to_verify=source_file_to_verify,
        )

    def get_conversation_with_message_appended(
        self, message: ConversationMessage
    ) -> tuple[ConversationMessage, ...]:
        """Return a copy of this SpecConversation's conversation with the given message appended.

        Args:
            message (ConversationMessage): The message to append to the end of the conversation.

        Returns:
            tuple[ConversationMessage]: A copy of this SpecConversation's conversation field with
                the message appended.
        """
        return (*self.conversation, message)

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
        """Return True iff this conversation includes the LLM deciding on a next step.

        Returns:
            bool: True iff this conversation includes the LLM deciding on a next step.
        """
        return self.next_step is not None
