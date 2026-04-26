"""Default module for LLM-based generation."""

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
    """Encapsulate LLM-based generation logic.

    Wraps `litellm` to support both direct API access (via `LLM_API_KEY`) and
    Google Cloud Vertex AI (via `VERTEX_AI_JSON`).  Automatically retries on
    transient errors and compacts the conversation when the context window is
    exceeded.

    Attributes:
        model (str): The litellm model string (e.g. `vertex_ai/claude-sonnet-4-6`).
        max_tokens (int): Maximum tokens allowed in a single response.
        api_key (str | None): API key for direct access; `None` when using Vertex AI.
        vertex_credentials (str | None): JSON credentials for Vertex AI; `None` otherwise.
    """

    def __init__(self, model: str, use_vertex_api: bool):
        """Create a new DefaultLlmBackend.

        Args:
            model (str): The model name to use (e.g. `claude-sonnet-4-6`, `gpt-4o`).
            use_vertex_api (bool): If True and `VERTEX_AI_JSON` is set, route requests
                through Google Cloud Vertex AI using the credentials in that file.

        Raises:
            ModelError: Raised when `model` is not a supported model name.
        """
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
        """Return `top_k` model responses for the given conversation.

        Retries up to 5 times on transient errors (rate limits, server errors, connection issues)
        with a 10-second delay between attempts.  On a context-window overflow, the conversation
        is compacted and retried once.

        Args:
            messages (tuple[ConversationMessage, ...]): The conversation history to send.
            temperature (float): Sampling temperature. Must be non-zero when `top_k > 1`.
            top_k (int): Number of independent completions to request.

        Returns:
            list[str]: The text content of each completion, with `len(result) == top_k`.

        Raises:
            GenerationError: Raised for unrecoverable API errors or invalid arguments.
            ContextWindowExceededError: Raised when the context window is exceeded and the
                conversation is already too short to compact further.
            ModelError: Raised after 5 consecutive transient failures.
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
                msg = f"Encountered an error with LLM call: {e}"
                raise GenerationError(msg) from e
            except (
                litellm.RateLimitError,
                litellm.InternalServerError,
                litellm.APIConnectionError,
            ) as e:
                count += 1
                if count >= 5:
                    raise ModelError("Vertex AI API: Too many retries") from e
                logger.warning(f"LLM Error {e}. Waiting 10 seconds and retrying")
                time.sleep(10)
            except Exception as e:  # noqa: BLE001
                msg = f"LLM Error: {e}"
                raise GenerationError(msg)  # noqa: B904

        return [choice["message"]["content"] for choice in response["choices"]]

    @staticmethod
    def get_instance(model_name: str, use_vertex_api: bool) -> LlmBackend:
        """Return an instance of LlmBackend for the given model.

        Args:
            model_name (str): The name of the model to use.
            use_vertex_api (bool): True iff the Google Cloud Platform Vertex AI API should be used
                to access a model. See Google Cloud Platform Vertex AI API
                (https://docs.cloud.google.com/vertex-ai/docs/reference/rest).

        Returns:
            LlmBackend: The LlmBackend instance used to run code generation with the given model.

        Raises:
            ModelError: Raised when an unsupported model is passed to this function.
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

        Returns:
            tuple[ConversationMessage, ...]: A compacted conversation,
                or None if too short to compact.
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
