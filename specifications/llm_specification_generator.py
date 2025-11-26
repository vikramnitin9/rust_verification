"""Module for generating and repairing specifications via LLMs."""

from models import LLMGen, ModelError, get_llm_generation_with_model
from util import ParsecResult
from verification import Failure, PromptBuilder, VerificationResult

from .llm_invocation_result import LlmInvocationResult


class LlmSpecificationGenerator:
    """Class for LLM-driven specification generation and repair.

    Attributes:
        _model (LLMGen): The model to use for specification generation and repair.
        _parsec_result (ParsecResult): The ParseC result to use to obtain functions.
        _prompt_builder (PromptBuilder): Used in creating specification generation and repair
            prompts.
    """

    _model: LLMGen
    _parsec_result: ParsecResult
    _prompt_builder: PromptBuilder

    def __init__(self, model: str, parsec_result: ParsecResult):
        self._model = get_llm_generation_with_model(model)
        self._parsec_result = parsec_result
        self._prompt_builder = PromptBuilder()

    def generate_specifications(
        self,
        function_name: str,
        conversation: list[dict[str, str]],
        num_samples: int,
        temperature: float = 0.0,
    ) -> LlmInvocationResult:
        """Generate a set of specifications for the function with the given name.

        Args:
            function_name (str): The function for which to generate specifications.
            conversation (list[dict[str, str]]): The LLM conversation, so far.
            num_samples (int): The number of generated specifications to sample from the LLM.
            temperature (float): The temperature setting for the LLM. Defaults to 0.0.

        Raises:
            RuntimeError: Raised when the function is missing from the ParseC result, or an error
                occurs during specification generation.

        Returns:
            LlmInvocationResult: The prompt used to invoke an LLM and its response.
        """
        function = self._parsec_result.get_function(function_name)
        if not function:
            msg = f"Function: '{function_name}' was missing from the ParseC result"
            raise RuntimeError(msg)

        specification_generation_prompt = self._prompt_builder.specification_generation_prompt(
            function, self._parsec_result
        )
        specification_generation_message = {
            "role": "user",
            "content": specification_generation_prompt,
        }
        conversation.append(specification_generation_message)

        try:
            response = self._model.gen(conversation, top_k=num_samples, temperature=temperature)
            print(response)
            return LlmInvocationResult(specification_generation_prompt, response)
        except ModelError as e:
            msg = f"Error during specification generation for '{function_name}': {e}"
            raise RuntimeError(msg) from e

    def repair_specifications(
        self,
        function_name: str,
        verification_result: VerificationResult,
        conversation: list[dict[str, str]],
    ) -> LlmInvocationResult:
        """Repair the specifications for the function with the given name.

        Args:
            function_name (str): The function for which to repair specifications.
            verification_result (VerificationResult): The result of a verifier run.
            conversation (list[dict[str, str]]): The LLM conversation, so far.

        Raises:
            RuntimeError: Raised when the function is missing from the ParseC result, or an error
                occurs during specification repair.

        Returns:
            LlmInvocationResult: The prompt used to invoke an LLM and its response.
        """
        function = self._parsec_result.get_function(function_name)
        if not function:
            msg = f"Function: '{function_name}' was missing from the ParseC result"
            raise RuntimeError(msg)

        if not isinstance(verification_result, Failure):
            msg = "Repairing a specification that verifies successfully is not required"
            raise TypeError(msg)

        repair_prompt = self._prompt_builder.specification_repair_prompt(
            function, verification_result
        )
        repair_message = {"role": "user", "content": repair_prompt}
        conversation.append(repair_message)

        try:
            response = self._model.gen(conversation, top_k=1, temperature=0.0)
            return LlmInvocationResult(repair_prompt, response)
        except ModelError as e:
            msg = f"Error during specification repair for '{function_name}': {e}"
            raise RuntimeError(msg) from e
