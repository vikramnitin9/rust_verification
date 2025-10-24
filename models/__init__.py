import os

from dotenv import load_dotenv

from .llm_gen import LLMGen

load_dotenv()


class ModelException(Exception):
    pass


def get_model_from_name(name: str) -> LLMGen:
    vertex = True if "VERTEX_AI_JSON" in os.environ else False

    if name == "claude37":
        model_str = "claude-3-7-sonnet@20250219"
        if not vertex:
            model_str = model_str.replace("@", "-")
        return LLMGen(model=model_str, vertex=vertex)
    if name == "gpt-4o":
        model_str = "gpt-4o"
        return LLMGen(model=model_str, vertex=vertex)
    raise NotImplementedError("Unknown model name")


__all__ = [
    "LLMGen",
    "ModelException",
    "get_model_from_name",
]
