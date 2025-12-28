"""Entry point for the models module."""

import os

from dotenv import load_dotenv

from .llm_gen import LLMGen
from .conversation_message import ConversationMessage, UserMessage, LlmMessage, SystemMessage

load_dotenv()

IS_VERTEX_AVAILABLE = "VERTEX_AI_JSON" in os.environ


class ModelError(Exception):
    """Represent errors related to working with LLMs."""


def get_llm_generation_with_model(model_name: str) -> LLMGen:
    """Return an instance of LLMGen which calls the model with the given name.

    Args:
        model_name (str): The name of the model to run generation with.

    Raises:
        ModelError: Raised when an unsupported model is passed to this function.

    Returns:
        LLMGen: The LLMGen instance used to run code generation with the given model.
    """
    match model_name:
        case "claude37":
            model_str = "claude-3-7-sonnet@20250219"
            if not IS_VERTEX_AVAILABLE:
                model_str = model_name.replace("@", "-")
            return LLMGen(model=model_str, vertex=IS_VERTEX_AVAILABLE)
        case "gpt-4o":
            return LLMGen(model=model_name, vertex=IS_VERTEX_AVAILABLE)
        case _:
            msg = f"Unsupported model: {model_name}"
            raise ModelError(msg)


__all__ = [
    "LLMGen",
    "ModelError",
    "get_llm_generation_with_model",
    "ConversationMessage",
    "UserMessage",
    "LlmMessage",
    "SystemMessage",
]
