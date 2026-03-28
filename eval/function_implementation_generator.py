"""Module for generating C function implementations from signatures and specifications."""

import json

from loguru import logger

from models import LlmClient, SystemMessage, UserMessage
from util import FunctionSpecification, json_util
from verification import PromptBuilder


class FunctionImplementationGenerator:
    """Generates a C function implementation from a specification and signature using an LLM.

    Attributes:
        _llm_client (LlmClient): The LLM client used to generate function implementations.
        _prompt_builder (PromptBuilder): Constructs LLM prompts.
    """

    _llm_client: LlmClient
    _prompt_builder: PromptBuilder

    def __init__(self, llm_client: LlmClient) -> None:
        """Create a new FunctionImplementationGenerator.

        Args:
            llm_client (LlmClient): The LLM client used to generate function implementations.
        """
        self._llm_client = llm_client
        self._prompt_builder = PromptBuilder()

    def generate_implementation(
        self,
        system_prompt: str,
        signature: str,
        specification: FunctionSpecification,
    ) -> list[str]:
        """Return candidate C function implementations for the given signature and specification.

        Each element of the returned list corresponds to one LLM sample and contains the
        complete C function (signature + body) extracted from the model's response.

        Args:
            system_prompt (str): The system prompt for the implementation generation conversation.
            signature (str): The signature for the C function to implement,
                such as "int add(int a, int b)".
            specification (FunctionSpecification): The CBMC pre- and postconditions the
                implementation must satisfy.

        Returns:
            list[str]: A list of candidate C function implementations.
        """
        prompt = self._prompt_builder.generate_implementation_prompt(
            signature=signature,
            specification=specification,
        )
        conversation = (
            SystemMessage(content=system_prompt),
            UserMessage(content=prompt),
        )
        # Each element of `raw_responses` is a JSON object with an "implementation" key.
        raw_responses = self._llm_client.get(conversation=conversation)
        implementations = [
            impl for impl in (self._extract_code(r) for r in raw_responses) if impl is not None
        ]
        return [f"{signature}{{\n{impl}\n}}" for impl in implementations]

    def _extract_code(self, llm_response: str) -> str | None:
        """Return the function body found in an LLM JSON response, or None if parsing fails.

        The response from the LLM should be a JSON object with an "implementation" key, i.e.,

            {
                "implementation": <BODY>
            }

        Where <BODY> comprises the body of the C function (i.e., everything between the braces,
        exclusive). See `prompts/generate-implementation-prompt-template.txt` for additional
        details.

        Args:
            llm_response (str): A raw LLM response string.

        Returns:
            str | None: The extracted function body, or None if the response could not be parsed.
        """
        try:
            data = json_util.parse_object(llm_response.strip())
            if implementation := data.get("implementation"):
                if isinstance(implementation, str):
                    return str(implementation).strip()
            logger.error(
                f"Valid JSON, but missing or malformed 'implementation' key-value pair from: "
                f"{llm_response}"
            )
            return None
        except json.JSONDecodeError:
            logger.error(f"Failed to parse JSON from raw LLM response: {llm_response}")
            return None
