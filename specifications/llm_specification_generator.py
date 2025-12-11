"""Module for generating and repairing specifications via LLMs."""

from models import LLMGen, ModelError, get_llm_generation_with_model
from util import (
    FunctionSpecification,
    ParsecFunction,
    ParsecResult,
    extract_function,
    function_util,
)
from verification import PromptBuilder


class LlmSpecificationGenerator:
    """Class for LLM-driven specification generation and repair."""

    _llm: LLMGen
    _prompt_builder: PromptBuilder
    _parsec_result: ParsecResult
    _num_specification_generation_candidates: int

    def __init__(self, model: str, num_specification_generation_candidates: int):
        self._model = get_llm_generation_with_model(model)
        self._prompt_builder = PromptBuilder()
        self._num_specification_generation_candidates = num_specification_generation_candidates

    def try_to_specify(
        self, function: ParsecFunction, hints: str, conversation: list[dict[str, str]]
    ) -> list[FunctionSpecification]:
        # TODO: Somehow incorporate `hints` into the prompt.
        specification_generation_prompt = self._prompt_builder.specification_generation_prompt(
            function, self._parsec_result
        )
        specification_generation_message = {
            "role": "user",
            "content": specification_generation_prompt,
        }
        try:
            conversation.append(specification_generation_message)
            model_responses = self._model.gen(
                conversation, top_k=self._num_specification_generation_candidates, temperature=0.8
            )
            candidate_specified_functions = [
                extract_function(response) for response in model_responses
            ]
            return [
                function_util.extract_specification(function.splitlines())
                for function in candidate_specified_functions
            ]
        except ModelError as me:
            msg = f"Failed to generate specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _repair_spec(
        self, function: ParsecFunction, spec: FunctionSpecification
    ) -> FunctionSpecification:
        pass
