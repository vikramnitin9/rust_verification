"""Module for generating and repairing specifications via LLMs."""

from models import LLMGen, ModelError, get_llm_generation_with_model
from util import (
    FunctionSpecification,
    ParsecFile,
    ParsecFunction,
    SpecConversation,
    extract_function,
    function_util,
)
from verification import PromptBuilder, ProofState, VerificationClient


class LlmSpecificationGenerator:
    """Class for LLM-driven specification generation and repair.

    Attributes:
        _model (LLMGen): The model to use for specification generation and repair.
        _parsec_file (ParsecFile): The ParseC file to use to obtain functions.
        _prompt_builder (PromptBuilder): Used in creating specification generation and repair
            prompts.
    """

    _model: LLMGen
    _parsec_file: ParsecFile
    _prompt_builder: PromptBuilder
    _llm: LLMGen
    _verifier: VerificationClient
    _num_specification_generation_candidates: int
    _num_repair_iterations: int
    _num_repair_candidates: int
    _system_prompt: str

    def __init__(
        self,
        model: str,
        system_prompt: str,
        verifier: VerificationClient,
        num_specification_generation_candidates: int,
        num_repair_iterations: int,
    ):
        """Create a new LlmSpecificationGenerator."""
        self._llm = get_llm_generation_with_model(model)
        self._system_prompt = system_prompt
        self._verifier = verifier
        self._prompt_builder = PromptBuilder()
        self._num_specification_generation_candidates = num_specification_generation_candidates
        self._num_repair_iterations = num_repair_iterations

    def generate_and_repair_spec(
        self, function: ParsecFunction, backtracking_hint: str, proof_state: ProofState
    ) -> list[SpecConversation]:
        """Return a list of potential specifications for the function.

        Args:
            function (ParsecFunction): The function for which to generate potential specs.
            backtracking_hint (str): Hints to help guide spec generation. Only non-empty when
                backtracking.
            proof_state (ProofState): The proof state under which to generate specs.

        Returns:
            list[SpecConversation]: A list of potential specifications for the function.
        """
        candidate_specs = self._generate_specs(
            function=function, backtracking_hint=backtracking_hint
        )
        # TODO: Actually perform some pruning here of the candidate specs first.
        pruned_specs = candidate_specs
        repaired_specs = []
        for pruned_spec in pruned_specs:
            repaired_specs.extend(
                self._repair_spec(
                    function=function, spec_conversation=pruned_spec, proof_state=proof_state
                )
            )
        return repaired_specs

    def _generate_specs(
        self,
        function: ParsecFunction,
        backtracking_hint: str,  # noqa: ARG002
    ) -> list[SpecConversation]:
        # TODO: Somehow incorporate `backtracking_hint` into the prompt.
        conversation = [{"role": "system", "content": self._system_prompt}]
        specification_generation_prompt = self._prompt_builder.specification_generation_prompt(
            function, self._parsec_file
        )
        specification_generation_message = {
            "role": "user",
            "content": specification_generation_prompt,
        }
        try:
            conversation.append(specification_generation_message)
            model_responses = self._llm.gen(
                conversation, top_k=self._num_specification_generation_candidates, temperature=0.8
            )
            candidate_specified_functions = [
                extract_function(response) for response in model_responses
            ]
            candidate_specs = [
                function_util.extract_specification(function.splitlines())
                for function in candidate_specified_functions
            ]
            return [
                SpecConversation(specification=candidate_spec, conversation=conversation)
                for candidate_spec in candidate_specs
            ]

        except ModelError as me:
            msg = f"Failed to generate specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _repair_spec(
        self,
        function: ParsecFunction,
        spec_conversation: SpecConversation,
        proof_state: ProofState,
    ) -> list[SpecConversation]:
        observed_spec_conversations = []
        verified_spec_conversations = []
        current_spec_conversations = [spec_conversation]
        for _ in range(self._num_repair_iterations):
            unverified_spec_conversations: list[SpecConversation] = []
            for current_spec_conversation in current_spec_conversations:
                if current_spec_conversation in observed_spec_conversations:
                    continue
                observed_spec_conversations.append(current_spec_conversation)

                vresult = self._verifier.verify_function_with_spec(
                    function_name=function.name,
                    spec=current_spec_conversation.specification,
                    proof_state=proof_state,
                )

                if vresult.succeeded:
                    verified_spec_conversations.append(current_spec_conversation)
                else:
                    unverified_spec_conversations.append(current_spec_conversation)

            for unverified_spec_conversation in unverified_spec_conversations:
                vresult = self._verifier.verify_function_with_spec(
                    function_name=function.name,
                    spec=unverified_spec_conversation.specification,
                    proof_state=proof_state,
                )
                conversation_updated_with_failure_information = (
                    unverified_spec_conversation.get_conversation_with_message_appended(
                        {
                            "user": self._prompt_builder.backtracking_prompt(
                                verification_result=vresult
                            )
                        }
                    )
                )

                model_responses = self._call_llm_for_repair(
                    function=function, conversation=conversation_updated_with_failure_information
                )
                current_spec_conversations += [
                    SpecConversation(
                        specification=specification,
                        conversation=unverified_spec_conversation.get_conversation_with_message_appended(
                            {"role": "assistant", "response": response}
                        ),
                    )
                    for specification, response in model_responses.items()
                ]
        return verified_spec_conversations or observed_spec_conversations

    def _call_llm_for_repair(
        self, function: ParsecFunction, conversation: list[dict[str, str]]
    ) -> dict[FunctionSpecification, str]:
        try:
            responses = self._model.gen(
                messages=conversation, top_k=self._num_repair_candidates, temperature=0.8
            )
            candidate_repaired_functions_to_response = {
                extract_function(response): response for response in responses
            }
            return {
                function_util.extract_specification(function.splitlines()): response
                for function, response in candidate_repaired_functions_to_response.items()
            }
        except ModelError as me:
            msg = f"Failed to repair specifications for '{function.name}'"
            raise RuntimeError(msg) from me
