"""Module for regenerating C function implementations from specifications using an LLM."""

import json
from pathlib import Path
from string import Template

from models import LlmClient, SystemMessage, UserMessage
from util import FunctionSpecification


class ImplementationRegenerator:
    """Regenerates C function implementations from a specification and signature using an LLM.

    Attributes:
        _llm_client (LlmClient): The LLM client used to sample implementations.
        _system_prompt (str): The system prompt sent at the start of every conversation.
    """

    _llm_client: LlmClient
    _system_prompt: str

    FUNCTION_IMPLEMENTATION_GENERATION_PROMPT_TEMPLATE: str = Path(
        "./prompts/regenerate-implementation-prompt-template.txt"
    ).read_text(encoding="utf-8")

    def __init__(self, llm_client: LlmClient, system_prompt: str) -> None:
        """Create a new ImplementationRegenerator.

        Args:
            llm_client (LlmClient): The LLM client used to sample implementations.
            system_prompt (str): The system prompt sent at the start of every conversation.
        """
        self._llm_client = llm_client
        self._system_prompt = system_prompt

    def regenerate(
        self,
        signature: str,
        specification: FunctionSpecification,
    ) -> list[str]:
        """Return candidate C function bodies for the given signature and specification.

        Each element of the returned list corresponds to one LLM sample and contains the
        function body extracted from the model's JSON response.  Samples whose responses
        cannot be parsed as valid JSON (or lack the ``"implementation"`` key) are silently
        dropped.

        Args:
            signature (str): The C function signature to implement (e.g.
                ``"int add(int a, int b)"``).
            specification (FunctionSpecification): The CBMC pre- and postconditions that the
                regenerated implementation must satisfy.

        Returns:
            list[str]: A list of candidate C function implementations.
        """
        prompt = Template(
            ImplementationRegenerator.FUNCTION_IMPLEMENTATION_GENERATION_PROMPT_TEMPLATE
        ).substitute(
            signature=signature.strip(),
            specification=specification.get_prompt_str(),
        )
        conversation = (
            SystemMessage(content=self._system_prompt),
            UserMessage(content=prompt),
        )
        raw_responses = self._llm_client.get(conversation=conversation)
        return [impl for impl in (_extract_code(r) for r in raw_responses) if impl is not None]


def _extract_code(llm_response: str) -> str | None:
    """Return the function body found in an LLM JSON response, or None if parsing fails.

    The LLM is instructed to return a JSON object of the form ``{"implementation": "<body>"}``.
    This function parses that object and returns the value of the ``"implementation"`` key.

    Args:
        llm_response (str): A raw LLM response string.

    Returns:
        str | None: The extracted function body, or None if the response could not be parsed.
    """
    try:
        data = json.loads(llm_response.strip())
        implementation = data.get("implementation")
        return str(implementation).strip() if implementation is not None else None
    except json.JSONDecodeError:
        return None
