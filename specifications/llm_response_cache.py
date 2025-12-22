"""Class to cache LLM responses for specification generation and repair."""

import atexit
import json
from pathlib import Path

from loguru import logger


class LlmResponseCache:
    """Class to cache LLM responses for specification generation and repair.

    Each prompt is mapped to a list of responses. This is because a call to an LLM may pick the
    top-k responses, where k is a value greater than one (i.e., this is effectively the value we use
    for the number of candidates).

    Attributes:
        _path_to_cache (str): The path to the file used as the cache.
        _cache (dict[str, list[str]]): The cache, mapping from prompts to responses.

    """

    _path_to_cache: str
    _cache: dict[str, list[str]]

    DEFAULT_LLM_RESPONSE_CACHE_PATH = "data/caching/cache.json"

    def __init__(self, path_to_cache: str = DEFAULT_LLM_RESPONSE_CACHE_PATH):
        """Create a new LlmResponseCache that loads from the cache file."""
        self._path_to_cache = path_to_cache
        self._cache = json.loads(Path(self._path_to_cache).read_text())
        atexit.register(self.commit)

    def read(self, prompt: str) -> list[str] | None:
        """Read the cache for the given prompt.

        Args:
            prompt (str): The prompt to look up in the cache.

        Returns:
            list[str] | None: The response(s) that map to the given prompt, or None.
        """
        return self._cache.get(prompt)

    def write(self, prompt: str, responses: list[str]) -> None:
        """Write to the cache with the prompt and its associated response(s).

        Args:
            prompt (str): _description_
            responses (list[str]): _description_
        """
        self._cache[prompt] = responses

    def commit(self) -> None:
        """Commit the current contents of the in-memory cache to disk."""
        logger.info(f"Committing current LlmResponseCache to disk at: {self._path_to_cache}")
        Path(self._path_to_cache).write_text(json.dumps(self._cache, indent=4))
