"""Class for an LLM-based oracle to determine failure recovery policies for specifications."""

from models import LLMGen, get_llm_generation_with_model
from util import ParsecResult, text_util
from verification import PromptBuilder

from .failure_recovery_policy import AssumeSpec, BacktrackToCallee, FailureRecoveryPolicy
from .specified_function_sample import SpecifiedFunctionSample


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
        self, function_name: str, failing_specification_samples: list[SpecifiedFunctionSample]
    ) -> FailureRecoveryPolicy:
        """Return the recovery policy decided by the LLM for the function that fails to verify.

        An LLM acts as an oracle to determine the next step for a function that fails to verify
        after repairing and regenerating specifications up to the user-specified limits.

        At a high level, the LLM is sent the specified function with the fewest errors reported by
        CBMC, and directed to return the error recovery policy. See:

            failure-recovery-classification-prompt-template.txt

        For details on the exact prompt.

        Args:
            function_name (str): The name of the function that fails to verify.
            failing_specification_samples (list[LlmGenerateVerifyIteration]): The list of specified
                function samples that fail to verify.

        Returns:
            FailureRecoveryPolicy: The recovery policy classification.
        """
        sample_with_fewest_errors = min(
            failing_specification_samples, key=lambda sample: sample.get_num_verification_failures()
        )
        parsec_function_for_sample = sample_with_fewest_errors.get_parsec_representation()
        if not sample_with_fewest_errors.verification_result:
            msg = f"'{function_name}' did not have a verification result"
            raise ValueError(msg)
        verification_failure_classification_prompt = (
            self._prompt_builder.failure_recovery_classification_prompt(
                parsec_function_for_sample,
                sample_with_fewest_errors.verification_result,
                self._parsec_result,
            )
        )

        conversation = [{"role": "user", "content": verification_failure_classification_prompt}]
        response = self._model.gen(messages=conversation, temperature=0.0, top_k=1)[0]
        return self._parse_classification_response(response)

    def _parse_classification_response(self, llm_response: str) -> FailureRecoveryPolicy:
        """Return a failure recovery policy parsed from an LLM response.

        Args:
            llm_response (str): The LLM response from which to parse a recovery policy.

        Raises:
            RuntimeError: Raised when the LLM response is malformed or does not match the schema
                provided in `failure-recovery-classification-prompt-template.txt`.

        Returns:
            FailureRecoveryPolicy: A failure recovery policy parsed from an LLM response.
        """
        response_dict = text_util.get_dict_from_json(llm_response)
        reasoning = response_dict.get("reasoning")
        classification_data = response_dict.get("classification")
        if not (classification_data and reasoning):
            msg = "The model failed to provide a complete failure recovery policy"
            raise RuntimeError(msg)
        match classification_data.get("action"):
            case "ASSUME_SPEC":
                return AssumeSpec(reasoning)
            case "BACKTRACK_TO_CALLEE":
                callee_to_backtrack_to = classification_data.get("callee_for_backtracking")
                if not callee_to_backtrack_to:
                    raise RuntimeError("The model failed to specify a callee for backtracking")
                return BacktrackToCallee(reasoning, callee_to_backtrack_to)
            case _:
                msg = "The model failed to provide a complete failure recovery policy"
                raise RuntimeError(msg)
