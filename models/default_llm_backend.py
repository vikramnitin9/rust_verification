"""Default module for LLM-based generation."""

# ruff: noqa
# TODO: Vikram, please document.
# Vikram would be best suited to document this class.

from .conversation_message import ConversationMessage
from .llm_backend import LlmBackend, ModelError, GenerationError
from dotenv import load_dotenv

import json
import os
import pathlib
import time

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
    def get_instance(model_name: str) -> LlmBackend:
        """Return an instance of LlmBackend for the given model.

        Raises:
            ModelError: Raised when an unsupported model is passed to this function.

        Returns:
            LlmBackend: The LlmBackend instance used to run code generation with the given model.
        """
        match model_name:
            case "claude37":
                claude_model_name = "claude-3-7-sonnet@20250219"
                if not "VERTEX_AI_JSON" in os.environ:
                    claude_model_name = claude_model_name.replace("@", "-")
                return DefaultLlmBackend(model=claude_model_name)
            case "gpt-4o":
                return DefaultLlmBackend(model=model_name)
            case _:
                msg = f"Unsupported model: {model_name}"
                raise ModelError(msg)
