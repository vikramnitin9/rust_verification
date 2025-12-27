"""Class to cache LLM responses.

This reduces cost by avoiding sending the same LLM prompt twice.
It also enables running tests without sending any LLM prompts.
"""

import atexit
import json
from pathlib import Path

from loguru import logger

# MDE: This class currently has nothing to do with LLMs, so its name is misleading.  But, I think it
# should call the LLM itself, so the name will be informative.

# MDE: I think there should be only one user-visible method (in addition to a constructor), which
# has a name like "get".  Transparently to the user, the "get" method may call an LLM or it may read
# from the cache.

# MDE: Rather than implementing functionality yourself, I suggest using the `diskcache` package.


class LlmResponseCache:
    """Class to cache LLM responses.

    Each prompt is mapped to a list of the top k responses.

    Attributes:
        _path_to_cache (Path): The file used as the cache.
        _cache (dict[str, list[str]]): The cache, mapping from prompts to responses.
    """

    _path_to_cache: Path
    _cache: dict[str, list[str]]

    DEFAULT_LLM_RESPONSE_CACHE_PATH = "data/caching/cache.json"

    def __init__(self, path_to_cache: str = DEFAULT_LLM_RESPONSE_CACHE_PATH):
        """Create a new LlmResponseCache that loads from the cache file."""
        self._path_to_cache = Path(path_to_cache)
        if not self._path_to_cache.exists():
            self._path_to_cache.touch()
        self._cache = json.loads(self._path_to_cache.read_text())
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
            prompt (str): The prompt to an LLM.
            responses (list[str]): The LLM response(s) to the prompt.
        """
        self._cache[prompt] = responses

    def commit(self) -> None:
        """Commit the current contents of the in-memory cache to disk."""
        logger.info(f"Committing current LlmResponseCache to disk at: {self._path_to_cache}")
        Path(self._path_to_cache).write_text(json.dumps(self._cache, indent=4))
