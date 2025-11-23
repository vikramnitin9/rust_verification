"""Class for an LLM-based oracle to determine failure recovery policies for specifications."""

import operator
from dataclasses import dataclass
from enum import Enum

from models import LLMGen, get_llm_generation_with_model
from util import ParsecResult, text_util
from verification import Failure, LlmGenerateVerifyIteration, PromptBuilder


class FailureRecoveryPolicy(str, Enum):
    """Represent failure recovery policies."""

    GIVE_UP = "GIVE_UP"
    BACKTRACK = "BACKTRACK"
    KEEP_GOING = "KEEP_GOING"


@dataclass(frozen=True)
class VerificationFailureRecoveryPolicyClassification:
    """Represent an LLM-based classification of a verification failure.

    Attributes:
        policy (FailureRecoveryPolicy): The failure recovery policy.
        reasoning (str): The reasoning produced by the model for the policy it selected.
    """

    policy: FailureRecoveryPolicy
    reasoning: str


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
    ) -> VerificationFailureRecoveryPolicyClassification:
        """Return the recovery policy decided by the LLM for the function that fails to verify.

        An LLM acts as an oracle to determine the next step for a function that fails to verify
        after repairing and regenerating specifications up to the user-specified limits.

        At a high level, the LLM is sent the specified function with the fewest errors reported by
        CBMC, and directed to return the error recovery policy. See:

            failure-recovery-classification-prompt-template.txt

        For details on the exact prompt.

        Args:
            function_name (str): The name of the function that fails to verify.
            iterations (list[LlmGenerateVerifyIteration]): The list of specifications generated for
                the function, all of which fail to verify.

        Returns:
            VerificationFailureRecoveryPolicyClassification: The recovery policy classification.
        """
        failed_iterations: list[tuple[LlmGenerateVerifyIteration, int]] = (
            self._get_failed_iterations(function_name, iterations)
        )
        iteration_with_fewest_errors, _ = min(failed_iterations, key=operator.itemgetter(1))
        if function := self._parsec_result.get_function(function_name):
            verification_failure_classification_prompt = (
                self._prompt_builder.failure_recovery_classification_prompt(
                    function, iteration_with_fewest_errors
                )
            )
            conversation = [{"role": "user", "content": verification_failure_classification_prompt}]
            response = self._model.gen(messages=conversation, temperature=0.0, top_k=1)[0]
            return self._parse_classification_response(response)
        msg = f"'{function_name}' was missing from the ParseC result"
        raise RuntimeError(msg)

    def _get_failed_iterations(
        self, function_name: str, iterations: list[LlmGenerateVerifyIteration]
    ) -> list[tuple[LlmGenerateVerifyIteration, int]]:
        """Return a tuple of failed iterations and the number of errors produced by CBMC for them.

        Args:
            function_name (str): The name of the function that failed to verify.
            iterations (list[LlmGenerateVerifyIteration]): The failed iterations of specification
                generation.

        Raises:
            RuntimeError: Raised when there is a successful specification generation iteration.

        Returns:
            list[tuple[LlmGenerateVerifyIteration, int]]: A tuple of failed iterations and the
                number of errors produced by CBMC for them.
        """
        failed_iterations: list[tuple[LlmGenerateVerifyIteration, int]] = [
            (iteration, iteration.verification_result.num_failures)
            for iteration in iterations
            if isinstance(iteration.verification_result, Failure)
        ]
        if len(failed_iterations) != len(iterations):
            msg = f"'{function_name}' had a successfully verifying specification"
            raise RuntimeError(msg)
        return failed_iterations

    def _parse_classification_response(
        self, llm_response: str
    ) -> VerificationFailureRecoveryPolicyClassification:
        """Return a verification failure classification parsed from an LLM response.

        Args:
            llm_response (str): The LLM response from which to parse a verification failure.

        Returns:
            VerificationFailureClassification: A verification failure classification parsed from an
                LLM response.
        """
        next_step = text_util.get_value_of_field_with_key(llm_response, key="next_step")
        reasoning = text_util.get_value_of_field_with_key(llm_response, key="reasoning")
        return VerificationFailureRecoveryPolicyClassification(
            policy=FailureRecoveryPolicy[next_step], reasoning=reasoning
        )
