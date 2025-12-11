"""Module for generating and repairing specifications via LLMs."""

from models import LLMGen, ModelError, get_llm_generation_with_model
from util import ParsecFunction, ParsecResult
from verification import Failure, PromptBuilder

from .candidate_specification import CandidateSpecification
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
            if len(response) < 1:
                raise RuntimeError("Model failed to return a response for specification generation")
            return LlmInvocationResult(specification_generation_prompt, response)
        except ModelError as e:
            msg = f"Error during specification generation for '{function_name}': {e}"
            raise RuntimeError(msg) from e

    def repair_specifications(
        self,
        failing_function_sample: CandidateSpecification,
        conversation: list[dict[str, str]],
    ) -> LlmInvocationResult:
        """Repair the specifications for the function with the given name.

        Args:
            failing_function_sample (SpecifiedFunctionSample): A function sample with failing
                specifications to repair.
            conversation (list[dict[str, str]]): The LLM conversation, so far.

        Raises:
            RuntimeError: Raised when the function is missing from the ParseC result, or an error
                occurs during specification repair.

        Returns:
            LlmInvocationResult: The prompt used to invoke an LLM and its response.
        """
        if not isinstance(failing_function_sample.verification_result, Failure):
            msg = (
                "repair_specifications expects the verification result of a sample to be a Failure"
                f" but got {type(failing_function_sample.verification_result)}"
            )
            raise TypeError(msg)

        failing_function = failing_function_sample.get_parsec_representation()
        if not failing_function:
            msg = f"Function '{failing_function_sample.function_name}' is missing from Parsec data"
            raise ValueError(msg)
        repair_prompt = self._prompt_builder.specification_repair_prompt(
            failing_function, failing_function_sample.verification_result
        )
        repair_message = {"role": "user", "content": repair_prompt}
        conversation.append(repair_message)

        try:
            response = self._model.gen(conversation, top_k=1, temperature=0.0)
            if len(response) < 1:
                raise RuntimeError("Model failed to return a response for specification repair")
            return LlmInvocationResult(repair_prompt, response)
        except ModelError as e:
            msg = f"Error during specification repair for '{failing_function.name}': {e}"
            raise RuntimeError(msg) from e

    def backtrack_to_callee(
        self,
        function: ParsecFunction,
        callee_name: str,
        backtracking_reasoning: str,
        conversation: list[dict[str, str]],
    ) -> LlmInvocationResult:
        """Return the result of backtracking (i.e., regenerating a callee's spec) for a function.

        Args:
            function (ParsecFunction): The function for which to execute backtracking.
            callee_name (str): The callee for which to regenerate specifications.
            backtracking_reasoning (str): The reasoning for backtracking.
            conversation: list[dict[str, str]]: The LLM conversation, so far.

        Raises:
            ValueError: Raised when the callee is missing from the Parsec result.
            RuntimeError: If the LLM does not return at least one result.

        Returns:
            LlmInvocationResult: The prompt used to invoke the LLM and its response.
        """
        callee = self._parsec_result.get_function(callee_name)
        if not callee:
            msg = (
                f"Callee '{callee_name}' for function '{function.name}' "
                "was missing from the Parsec result"
            )
            raise ValueError(msg)
        backtracking_prompt = self._prompt_builder.backtracking_prompt(
            function_under_failure_recovery=function,
            callee=callee,
            backtracking_reasoning=backtracking_reasoning,
        )
        backtracking_message = {"role": "user", "content": backtracking_prompt}
        conversation.append(backtracking_message)
        try:
            response = self._model.gen(conversation, top_k=1, temperature=0.0)
            if len(response) < 1:
                raise RuntimeError("Model failed to return a response for backtracking")
            return LlmInvocationResult(backtracking_prompt, response)
        except ModelError as e:
            msg = (
                f"Error during backtracking for function '{function.name}' and callee "
                f"'{callee_name}': {e}"
            )
            raise RuntimeError(msg) from e
