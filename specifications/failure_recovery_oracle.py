"""Class for an LLM-based oracle to determine failure recovery policies for specifications."""

from models import LLMGen, get_llm_generation_with_model
from util import ParsecResult
from verification import Failure, LlmGenerateVerifyIteration, PromptBuilder


class FailureRecoveryOracle:
    """Class for an LLM-based oracle to determine failure recovery policies for failing specs.

    Attributes:
        _model (LLMGen): The LLM to use as an oracle.
        _parsec_result (ParsecResult): The ParsecResult.
        _prompt_builder (PromptBuilder): The prompt builder.
    """

    _model: LLMGen
    _parsec_result: ParsecResult
    _prompt_builder: PromptBuilder

    def __init__(self, model: str, parsec_result: ParsecResult):
        self._model = get_llm_generation_with_model(model)
        self._parsec_result = parsec_result
        self._prompt_builder = PromptBuilder()

    def determine_recovery_policy(
        self, function_name: str, iterations: list[LlmGenerateVerifyIteration]
    ) -> None:
        """TODO: document me.

        Args:
            function_name (str): _description_
            iterations (list[LlmGenerateVerifyIteration]): _description_
        """
        # failed_iterations: list[tuple[LlmGenerateVerifyIteration, int]] = (
        #     self._get_failed_iterations(function_name, iterations)
        # )
        # iteration_with_fewest_errors, _ = min(failed_iterations, key=operator.itemgetter(1))
        # if function := self._parsec_result.get_function(function_name):
        #     pass

    def _get_failed_iterations(
        self, function_name: str, iterations: list[LlmGenerateVerifyIteration]
    ) -> list[tuple[LlmGenerateVerifyIteration, int]]:
        failed_iterations: list[tuple[LlmGenerateVerifyIteration, int]] = [
            (iteration, iteration.verification_result.num_failures)
            for iteration in iterations
            if isinstance(iteration.verification_result, Failure)
        ]
        if len(failed_iterations) != len(iterations):
            msg = f"'{function_name}' had a successfully verifying specification"
            raise RuntimeError(msg)
        return failed_iterations
