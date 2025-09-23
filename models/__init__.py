from .vertex_ai import VertexGen
from dotenv import load_dotenv
import os

load_dotenv()

class ModelException(Exception):
    pass


def get_model_from_name(name):

    vertex = True if 'VERTEX_AI_JSON' in os.environ else False

    if name == "claude37":
        model_str = "claude-3-7-sonnet@20250219"
        if not vertex:
            model_str = model_str.replace('@', '-')
        return VertexGen(model=model_str, vertex=vertex)
    elif name == "gpt-4o":
        model_str = "gpt-4o"
        return VertexGen(model=model_str, vertex=vertex)
    else:
        raise NotImplementedError("Unknown model name")

__all__ = [
    "VertexGen",
    "ModelException",
    "get_model_from_name",
]