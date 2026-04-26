"""Default module for LLM-based generation."""

# ruff: noqa
# TODO: Vikram, please document.
# Vikram would be best suited to document this class.

import json
import os
import pathlib
import time

import litellm
from dotenv import load_dotenv
from litellm import completion
from loguru import logger

from .conversation_message import ConversationMessage
from .llm_backend import ContextWindowExceededError, GenerationError, LlmBackend, ModelError

load_dotenv()


class DefaultLlmBackend(LlmBackend):
    """Encapsulate LLM-based generation logic."""

    def __init__(self, model: str, use_vertex_api: bool):
        if use_vertex_api and "VERTEX_AI_JSON" in os.environ:
            litellm.vertex_location = "us-east5"
            with pathlib.Path(os.environ["VERTEX_AI_JSON"]).open(encoding="utf-8") as file:
                self.vertex_credentials: str | None = json.dumps(json.load(file))
            self.model = f"vertex_ai/{model}"
            self.api_key = None
        else:
            self.vertex_credentials = None
            self.model = model
            self.api_key = os.environ["LLM_API_KEY"]

        if "claude" in model:
            self.max_tokens = 64000
        elif "gpt-4o" in model:
            self.max_tokens = 16384
        else:
            msg = f"Model {model} not supported"
            raise ModelError(msg)

    def send_messages(
        self, messages: tuple[ConversationMessage, ...], temperature: float = 0, top_k: int = 1
    ) -> list[str]:
        """messages: [{'role': 'system', 'content': 'You are an intelligent code assistant'},
                   {'role': 'user', 'content': 'Translate this program...'},
                   {'role': 'assistant', 'content': 'Here is the translation...'},
                   {'role': 'user', 'content': 'Do something else...'}]

        <returned>: ['Sure, here is...',
                     'Okay, let me see...',
                     ...]
        len(<returned>) == top_k
        """
        if top_k < 1:
            raise GenerationError("top_k must be >= 1")
        if top_k != 1 and temperature == 0:
            raise GenerationError("Top k sampling requires a non-zero temperature")

        count = 0
        while True:
            try:
                response = completion(
                    model=self.model,
                    messages=[message.to_dict() for message in messages],
                    temperature=temperature,
                    n=top_k,
                    api_key=self.api_key,
                    vertex_credentials=self.vertex_credentials,
                    max_tokens=self.max_tokens,
                )
                break
            except litellm.ContextWindowExceededError as e:
                compacted = self._compact_conversation(messages)
                if compacted is None:
                    msg = "Context window exceeded and conversation is too short to compact"
                    raise ContextWindowExceededError(msg) from e
                logger.warning("Context window exceeded; compacting conversation and retrying")
                messages = compacted
            except (
                litellm.BadRequestError,
                litellm.AuthenticationError,
                litellm.NotFoundError,
                litellm.UnprocessableEntityError,
            ) as e:
                raise GenerationError(f"Encountered an error with LLM call {e}")
            except (
                litellm.RateLimitError,
                litellm.InternalServerError,
                litellm.APIConnectionError,
            ) as e:
                count += 1
                if count >= 5:
                    raise ModelError("Vertex AI API: Too many retries")
                logger.warning(f"LLM Error {e}. Waiting 10 seconds and retrying")
                time.sleep(10)
            except Exception as e:
                raise GenerationError(f"LLM Error: {e}")

        return [choice["message"]["content"] for choice in response["choices"]]

    @staticmethod
    def get_instance(model_name: str, use_vertex_api: bool) -> LlmBackend:
        """Return an instance of LlmBackend for the given model.

        Args:
            model_name (str): The name of the model to use.
            use_vertex_api (bool): True iff the Google Cloud Platform Vertex AI API should be used
                to access a model. See Google Cloud Platform Vertex AI API
                (https://docs.cloud.google.com/vertex-ai/docs/reference/rest).

        Raises:
            ModelError: Raised when an unsupported model is passed to this function.

        Returns:
            LlmBackend: The LlmBackend instance used to run code generation with the given model.
        """
        match model_name:
            case "claude-sonnet-4-6" | "gpt-4o":
                return DefaultLlmBackend(model=model_name, use_vertex_api=use_vertex_api)
            case _:
                msg = f"Unsupported model: {model_name}"
                raise ModelError(msg)

    def _compact_conversation(
        self,
        messages: tuple[ConversationMessage, ...],
    ) -> tuple[ConversationMessage, ...] | None:
        """Return a compacted conversation, or `None` if it is already too short to compact.

        For example, given the following conversation:

        [
            SystemMessage,
            UserMessage_1,
            LlmResponse_1,
            UserMessage_2,
            LlmResponse_2,
            ...,
            LlmResponse_{n-1},
            UserMessage_n,
        ]

        Compaction retains the system message, the first user message, the most recent assistant
        message, and the final user message, resulting in:

        [
            SystemMessage,
            UserMessage_1,
            LlmResponse_{n-1},
            UserMessage_n,
        ]

        This preserves the framing, the best available
        response, and the current prompt while dropping intermediate turns.
        """
        if len(messages) <= 4:
            return None
        system_message = messages[0]
        initial_user_message = messages[1]
        latest_llm_response = next(
            (m for m in reversed(messages[:-1]) if m.role == "assistant"),
            None,
        )
        last_user_message = messages[-1]
        if latest_llm_response is None or (
            system_message.role != "system"
            or initial_user_message.role != "user"
            or last_user_message.role != "user"
        ):
            return None
        return (system_message, initial_user_message, latest_llm_response, last_user_message)
