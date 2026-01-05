"""Class providing cached-backed LLM-calling functions."""

from diskcache import Cache  # ty: ignore

from .conversation_message import ConversationMessage
from .llm_gen import LLMGen

DEFAULT_CACHE_DIR = "data/caching/"


class LlmClient:
    """Class providing cache-backed LLM-calling functions.

    Attributes:
        _llm (LLMGen): The internal LLM interface (see https://docs.litellm.ai/docs/).
        _top_k (int): The number of samples to obtain from the LLM.
        _temperature (float): The temperature (cannot be 0 for top-k > 1).
        _sample_cache (Cache | None): The cache storing samples from the LLM.
    """

    _llm: LLMGen
    _top_k: int
    _temperature: float
    _sample_cache: Cache | None

    def __init__(
        self, model_name: str, top_k: int, temperature: float, disable_cache: bool = False
    ):
        """Create a new LlmClient."""
        if top_k > 1 and temperature == 0:
            msg = (
                f"Model temperature must be non-zero for a `top_k` value greater than 1 "
                f"(temperature = {temperature}, top_k = {top_k})"
            )
            raise ValueError(msg)
        self._llm = LLMGen.get_llm_generation_with_model(model_name=model_name)
        self._top_k = top_k
        self._temperature = temperature
        self._sample_cache = None if disable_cache else Cache(directory=DEFAULT_CACHE_DIR)

    def get(self, conversation: tuple[ConversationMessage, ...]) -> list[str]:
        """Return the response from the LLM for the given conversation.

        INVARIANT: The last message in the conversation comprises the prompt for the model.

        Args:
            conversation (tuple[ConversationMessage, ...]): The conversation for the LLM.

        Raises:
            ValueError: Raised when an empty conversation is passed in.

        Returns:
            list[str]: The list of samples (of length `self._top_k`) from the LLM.
        """
        if not conversation:
            msg = "Cannot prompt an LLM with an empty conversation"
            raise ValueError(msg)

        cache_key = self._get_cache_key(conversation=conversation)
        samples = []
        if self._sample_cache is not None:
            if cached_response := self._sample_cache.get(cache_key):
                return cached_response

            # Cache miss.
            samples = self._llm.gen(
                messages=conversation, temperature=self._temperature, top_k=self._top_k
            )
            self._sample_cache[cache_key] = samples
            return samples

        return self._llm.gen(
            messages=conversation, temperature=self._temperature, top_k=self._top_k
        )

    def _get_cache_key(
        self, conversation: tuple[ConversationMessage, ...]
    ) -> tuple[tuple[str, str], ...]:
        """Return the key used to cache the given conversation.

        Args:
            conversation (tuple[ConversationMessage, ...]): The conversation to cache.

        Returns:
            tuple[tuple[str, str],...]: The key used to cache the given conversation.
        """
        return tuple((message.role, message.content) for message in conversation)
