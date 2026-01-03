"""Class to cache LLM samples.

This reduces cost by avoiding sending the same LLM prompt twice.
It also enables running tests without sending any LLM prompts.
"""

import atexit
import json
from pathlib import Path

from loguru import logger

# MDE: This class currently has nothing to do with LLMs, so its name is misleading.  But, I think it
# should call the LLM itself, so the name will be informative.

# JY: Response to above; I'm not sure if the cache itself should call the LLM. This feels like a
# violation of separation of concerns. A cache should only concern itself with storing/providing
# values. Adding the additional responsibility of actually computing (i.e., calling the LLM) values
# seems wrong.

# MDE: I think there should be only one user-visible method (in addition to a constructor), which
# has a name like "get".  Transparently to the user, the "get" method may call an LLM or it may read
# from the cache.

# MDE: Rather than implementing functionality yourself, I suggest using the `diskcache` package.
#
# JY: DiskCache's latest commit to main was March 2, 2024, is there a reason we want to use it in
# particular?


class LlmSampleCache:
    """Class to cache LLM samples from responses.

    Invoking an LLM results in a response (see llm_invocation_response.py). Each response may
    comprise 1 or more samples. In the context of specification generation, each sample represents
    a specification.


    Attributes:
        _path_to_cache (Path): The file used as the cache.
        _cache (dict[str, list[str]]): The cache, mapping from prompts to samples.
    """

    _path_to_cache_file: Path
    _cache: dict[str, list[str]]

    DEFAULT_LLM_SAMPLE_CACHE_PATH = "data/caching/cache.json"

    def __init__(self, path_to_cache: str = DEFAULT_LLM_SAMPLE_CACHE_PATH):
        """Create a new LlmResponseCache that loads from the cache file."""
        self._path_to_cache_file = Path(path_to_cache)
        if not self._path_to_cache_file.exists():
            self._path_to_cache_file.parent.mkdir(parents=True)
            self._path_to_cache_file.write_text("{}", encoding="utf-8")
        self._cache = json.loads(self._path_to_cache_file.read_text())
        atexit.register(self.commit)

    def read(self, prompt: str) -> list[str] | None:
        """Read the cache for the given prompt.

        Args:
            prompt (str): The prompt to look up in the cache.

        Returns:
            list[str] | None: The sample(s) that map to the given prompt, or None.
        """
        return self._cache.get(prompt)

    def write(self, prompt: str, samples: list[str]) -> None:
        """Write to the cache with the prompt and its associated samples.

        Args:
            prompt (str): The prompt to an LLM.
            samples (list[str]): The LLM samples for the prompt.
        """
        self._cache[prompt] = samples

    def commit(self) -> None:
        """Commit the current contents of the in-memory cache to disk."""
        logger.info(f"Committing current LlmSampleCache to disk at: {self._path_to_cache_file}")
        Path(self._path_to_cache_file).write_text(json.dumps(self._cache, indent=4))
