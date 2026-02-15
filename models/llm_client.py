"""Class providing cached-backed LLM-calling functions."""

from diskcache import Cache  # ty: ignore

from .conversation_message import ConversationMessage
from .llm_gen import LLMGen


class LlmClient:
    """Class providing cache-backed LLM-calling functions.

    Attributes:
        _llm (LLMGen): The internal LLM interface (see https://docs.litellm.ai/docs/).
        _top_k (int): The number of samples to obtain from the LLM.
        _temperature (float): The temperature (cannot be 0 if top_k > 1).
        _path_to_llm_cache_dir (str): The path to the LLM response cache directory.
        _llm_cache (Cache | None): A cache of LLM responses.
    """

    _llm: LLMGen
    _top_k: int
    _temperature: float
    _path_to_llm_response_cache_dir: str
    _llm_cache: Cache | None

    def __init__(
        self,
        model_name: str,
        top_k: int,
        temperature: float,
        path_to_llm_response_cache_dir: str,
        disable_llm_cache: bool = False,
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
        self._llm_cache = (
            None if disable_llm_cache else Cache(directory=path_to_llm_response_cache_dir)
        )

    def get(
        self,
        conversation: tuple[ConversationMessage, ...],
        temperature: float | None = None,
        top_k: int | None = None,
    ) -> list[str]:
        """Return the response from the LLM for the given conversation.

        INVARIANT: The last message in the conversation comprises the prompt for the model.

        Args:
            conversation (tuple[ConversationMessage, ...]): The conversation for the LLM.
            temperature (float | None): The temperature for generation.
            top_k (int | None): The number of samples to obtain.

        Raises:
            ValueError: Raised when an empty conversation is passed in.

        Returns:
            list[str]: The list of samples (of length `self._top_k` or `top_k` if not None)
                from the LLM.
        """
        if not conversation:
            msg = "Cannot prompt an LLM with an empty conversation"
            raise ValueError(msg)

        temperature = temperature or self._temperature
        top_k = top_k or self._top_k
        cache_key = None
        if self._llm_cache is not None:
            cache_key = self._get_cache_key(
                conversation=conversation, temperature=temperature, top_k=top_k
            )
            if cached_response := self._llm_cache.get(cache_key):
                return cached_response

        result = self._llm.gen(
            messages=conversation,
            temperature=temperature or self._temperature,
            top_k=top_k or self._top_k,
        )

        if self._llm_cache is not None:
            self._llm_cache[cache_key] = result

        return result

    def _get_cache_key(
        self,
        conversation: tuple[ConversationMessage, ...],
        temperature: float,
        top_k: int,
    ) -> tuple[tuple[str, str], ...]:
        """Return the key used to cache the given conversation.

        The cache key comprises:

            1. The conversation.
            2. The temperature.
            3. The value of `top_k`.
            4. The model name.

        Args:
            conversation (tuple[ConversationMessage, ...]): The conversation to cache.
            temperature (float): The temperature for generation.
            top_k (int): The number of samples to obtain.

        Returns:
            tuple[tuple[str, str],...]: The key used to cache the given conversation.
        """
        conversation_tuples = tuple((message.role, message.content) for message in conversation)
        return (
            *conversation_tuples,
            ("temperature", str(temperature)),
            ("top_k", str(top_k)),
            ("model", self._llm.model),
        )
