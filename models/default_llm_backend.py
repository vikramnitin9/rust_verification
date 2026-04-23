"""Default module for LLM-based generation."""

# ruff: noqa
# TODO: Vikram, please document.
# Vikram would be best suited to document this class.

from .conversation_message import ConversationMessage
from .llm_backend import LlmBackend, ModelError, GenerationError, ContextWindowExceededError
from dotenv import load_dotenv

import json
import os
import pathlib
import time
from concurrent.futures import ThreadPoolExecutor

import litellm
from litellm import completion
from loguru import logger

load_dotenv()


class DefaultLlmBackend(LlmBackend):
    """Encapsulate LLM-based generation logic."""

    def __init__(self, model: str):
        if "VERTEX_AI_JSON" in os.environ:
            litellm.vertex_location = "us-east5"
            with pathlib.Path(os.environ["VERTEX_AI_JSON"]).open(encoding="utf-8") as file:
                self.vertex_credentials: str | None = json.dumps(json.load(file))
            self.model = f"vertex_ai/{model}"
            self.api_key = None
        else:
            self.vertex_credentials = None
            self.model = model
            api_key_for_model = "ANTHROPIC_API_KEY" if model.startswith("claude") else "LLM_API_KEY"
            self.api_key = os.environ[api_key_for_model]

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
        """Return `top_k` sampled responses from the LLM for the given messages.

        Args:
            messages (tuple[ConversationMessage, ...]): The conversation to send to the LLM.
            temperature (float): The sampling temperature. Must be non-zero when `top_k > 1`.
            top_k (int): The number of responses to sample.

        Returns:
            list[str]: The sampled responses. `len(returned) == top_k`.
        """
        if top_k < 1:
            raise GenerationError("top_k must be >= 1")
        if top_k != 1 and temperature == 0:
            raise GenerationError("Top k sampling requires a non-zero temperature")

        # Claude models do not support the `n` parameter; issue parallel requests instead.
        if "claude" in self.model:
            return self._send_parallel(messages, temperature, top_k)

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

    def _send_parallel(
        self, messages: tuple[ConversationMessage, ...], temperature: float, top_k: int
    ) -> list[str]:
        """Return `top_k` responses by issuing parallel single requests.

        Used for models that do not support the `n` parameter (e.g. Claude). Each request runs
        its own retry loop independently.

        Args:
            messages (tuple[ConversationMessage, ...]): The conversation to send.
            temperature (float): The sampling temperature.
            top_k (int): The number of parallel requests to make.

        Returns:
            list[str]: The `top_k` sampled responses.
        """
        with ThreadPoolExecutor(max_workers=top_k) as executor:
            futures = [
                executor.submit(self._send_one_message, messages, temperature) for _ in range(top_k)
            ]
            return [f.result() for f in futures]

    def _send_one_message(
        self, messages: tuple[ConversationMessage, ...], temperature: float
    ) -> str:
        """Return a single response from the LLM with retry and compaction logic.

        Args:
            messages (tuple[ConversationMessage, ...]): The conversation to send.
            temperature (float): The sampling temperature.

        Returns:
            str: The model's response text.
        """
        count = 0
        while True:
            try:
                response = completion(
                    model=self.model,
                    messages=[message.to_dict() for message in messages],
                    temperature=temperature,
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

        return response["choices"][0]["message"]["content"]

    @staticmethod
    def get_instance(model_name: str) -> LlmBackend:
        """Return an instance of LlmBackend for the given model.

        Raises:
            ModelError: Raised when an unsupported model is passed to this function.

        Returns:
            LlmBackend: The LlmBackend instance used to run code generation with the given model.
        """
        match model_name:
            case "claude-sonnet-4-6" | "gpt-4o":
                return DefaultLlmBackend(model=model_name)
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
