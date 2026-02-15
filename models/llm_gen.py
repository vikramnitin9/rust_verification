"""Module for LLM-based generation."""

# ruff: noqa
# TODO: Vikram, please document.
# Vikram would be best suited to document this class.

from .conversation_message import ConversationMessage
from dotenv import load_dotenv

import json
import os
import pathlib
import time

import litellm
from litellm import completion
from loguru import logger

load_dotenv()

IS_VERTEX_AVAILABLE = "VERTEX_AI_JSON" in os.environ


class ModelError(Exception):
    """Represent errors related to working with LLMs."""


class LLMGen:
    """Encapsulate LLM-based generation logic."""

    def __init__(self, model: str, is_running_as_stub: bool, is_vertex_available: bool = True):
        if is_vertex_available:
            litellm.vertex_location = "us-east5"
            with pathlib.Path(os.environ["VERTEX_AI_JSON"]).open(encoding="utf-8") as file:
                self.vertex_credentials: str | None = json.dumps(json.load(file))
            self.model = f"vertex_ai/{model}"
            self.api_key = None
        else:
            self.vertex_credentials = None
            self.model = model
            self.api_key = None if is_running_as_stub else os.environ["LLM_API_KEY"]

        if "claude" in model:
            self.max_tokens = 64000
        elif "gpt-4o" in model:
            self.max_tokens = 16384
        else:
            msg = f"Model {model} not supported"
            raise Exception(msg)

    def gen(
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
        from . import ModelError

        if top_k < 1:
            raise ModelError("top_k must be >= 1")
        if top_k != 1 and temperature == 0:
            raise ModelError("Top k sampling requires a non-zero temperature")

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
                raise ModelError(f"Encountered an error with LLM call {e}")
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
                raise ModelError(f"LLM Error: {e}")

        return [choice["message"]["content"] for choice in response["choices"]]

    @staticmethod
    def get_llm_generation_with_model(model_name: str, is_running_as_stub: bool) -> "LLMGen":
        """Return an instance of LLMGen which calls the model with the given name.

        Args:
            model_name (str): The name of the model to run generation with.
            is_running_as_stub (bool): True iff code generation is stubbed out
                (e.g., for integration tests).

        Raises:
            ModelError: Raised when an unsupported model is passed to this function.

        Returns:
            LLMGen: The LLMGen instance used to run code generation with the given model.
        """
        match model_name:
            case "claude37":
                claude_model_name = "claude-3-7-sonnet@20250219"
                if not IS_VERTEX_AVAILABLE:
                    claude_model_name = claude_model_name.replace("@", "-")
                return LLMGen(
                    model=claude_model_name,
                    is_running_as_stub=is_running_as_stub,
                    is_vertex_available=IS_VERTEX_AVAILABLE,
                )
            case "gpt-4o":
                return LLMGen(
                    model=model_name,
                    is_running_as_stub=is_running_as_stub,
                    is_vertex_available=IS_VERTEX_AVAILABLE,
                )
            case _:
                msg = f"Unsupported model: {model_name}"
                raise ModelError(msg)
