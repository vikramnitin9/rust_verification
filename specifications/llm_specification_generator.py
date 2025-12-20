"""Module for generating and repairing specifications via LLMs."""

import json
from pathlib import Path

from models import LLMGen, ModelError, get_llm_generation_with_model
from util import (
    BacktrackingStrategy,
    CFunction,
    FunctionSpecification,
    ParsecFile,
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
    _num_specification_candidates: int
    _num_repair_iterations: int
    _num_repair_candidates: int
    _system_prompt: str

    def __init__(
        self,
        model: str,
        system_prompt: str,
        verifier: VerificationClient,
        num_specification_candidates: int,
        num_repair_iterations: int,
    ):
        """Create a new LlmSpecificationGenerator."""
        self._llm = get_llm_generation_with_model(model)
        self._system_prompt = system_prompt
        self._verifier = verifier
        self._prompt_builder = PromptBuilder()
        self._num_specification_candidates = num_specification_candidates
        self._num_repair_iterations = num_repair_iterations

    def generate_and_repair_spec(
        self,
        function: CFunction,
        backtracking_hint: str,
        proof_state: ProofState,
        parsec_file: ParsecFile,
    ) -> list[SpecConversation]:
        """Return a list of potential specifications for the function.

        Args:
            function (CFunction): The function for which to generate potential specs.
            backtracking_hint (str): Hints to help guide spec generation. Only non-empty when
                backtracking.
            proof_state (ProofState): The proof state under which to generate specs.
            parsec_file (ParsecFile): The ParsecFile containing the function for which to
                generate and repair potential specs.

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
                    function=function,
                    spec_conversation=pruned_spec,
                    proof_state=proof_state,
                    parsec_file=parsec_file,
                )
            )
        return repaired_specs

    def _generate_specs(
        self,
        function: CFunction,
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
                conversation, top_k=self._num_specification_candidates, temperature=0.8
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
                if candidate_spec
            ]

        except ModelError as me:
            msg = f"Failed to generate specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _repair_spec(
        self,
        function: CFunction,
        spec_conversation: SpecConversation,
        proof_state: ProofState,
        parsec_file: ParsecFile,
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

                # TODO: Create a separate file for each SpecConversation and pass it to the
                # verifier.
                path_to_file_to_verify = self._get_path_to_file_to_verify(
                    function=function,
                    spec_conversation=current_spec_conversation,
                    original_file_path=parsec_file.file_path,
                )
                current_spec_conversation.path_to_file = path_to_file_to_verify

                vresult = self._verifier.verify(
                    function=function,
                    spec=current_spec_conversation.specification,
                    proof_state=proof_state,
                    path_to_file=current_spec_conversation.path_to_file,
                )

                if vresult.succeeded:
                    verified_spec_conversations.append(current_spec_conversation)
                else:
                    unverified_spec_conversations.append(current_spec_conversation)

            for unverified_spec_conversation in unverified_spec_conversations:
                path_to_file_to_verify = unverified_spec_conversation.path_to_file
                if not path_to_file_to_verify:
                    msg = "A spec that failed to verify is missing the file in which it is declared"
                    raise ValueError(msg)
                vresult = self._verifier.verify(
                    function=function,
                    spec=unverified_spec_conversation.specification,
                    proof_state=proof_state,
                    path_to_file=path_to_file_to_verify,
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
                        backtracking_strategy=self._parse_backtracking_strategy(response),
                    )
                    for specification, response in model_responses.items()
                ]
        return verified_spec_conversations or observed_spec_conversations

    def _call_llm_for_repair(
        self, function: CFunction, conversation: list[dict[str, str]]
    ) -> dict[FunctionSpecification, str]:
        """Call an LLM for repairing a failing spec.

        Args:
            function (CFunction): The function with the failing spec.
            conversation (list[dict[str, str]]): The conversation for specification repair.

        Raises:
            RuntimeError: Raised when a failure occurs (e.g., API timeout) during a call to an LLM
                for specification repair.

        Returns:
            dict[FunctionSpecification, str]: A map of repaired specifications and the raw response
                from the LLM from which the repaired specification was extracted.
        """
        try:
            responses = self._model.gen(
                messages=conversation, top_k=self._num_repair_candidates, temperature=0.8
            )
            candidate_repaired_functions_to_response = {
                extract_function(response): response for response in responses
            }
            repaired_specs_to_responses: dict[FunctionSpecification, str] = {}
            for function_str, response in candidate_repaired_functions_to_response.items():
                if repaired_spec := function_util.extract_specification(function_str.splitlines()):
                    repaired_specs_to_responses[repaired_spec] = response
            return repaired_specs_to_responses
        except ModelError as me:
            msg = f"Failed to repair specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _parse_backtracking_strategy(self, llm_response: str) -> BacktrackingStrategy:
        """Parse a backtracking strategy from an LLM response.

        An LLM is asked to select a backtracking strategy and include it in its response when it
        is asked to repair a spec. This function parses the strategy to include in a
        SpecConversation object.

        Args:
            llm_response (str): The LLM response from which to parse a backtracking strategy.

        Raises:
            RuntimeError: Raised when an error is encountered when parsing a backtracking strategy.

        Returns:
            BacktrackingStrategy: The backtracking strategy returned by the LLM in its response.
        """
        llm_response = llm_response.strip()
        if llm_response.startswith("```json") or llm_response.endswith("```"):
            # The LLM likely did not follow instructions to return just the plain object.
            llm_response = llm_response.removeprefix("```json").removesuffix("```")
        try:
            return BacktrackingStrategy(json.loads(llm_response)["backtracking_strategy"])
        except json.JSONDecodeError as je:
            msg = f"The LLM failed to return a valid JSON object: {llm_response}, error = {je}"
            raise RuntimeError(msg) from je
        except KeyError as ke:
            msg = (
                "The LLM returned valid JSON, but was missing the 'backtracking_strategy' key: "
                f"{llm_response}"
            )
            raise RuntimeError(msg) from ke
        except ValueError as ve:
            msg = f"The LLM likely returned an invalid backtracking strategy: {llm_response}"
            raise RuntimeError(msg) from ve

    def _get_path_to_file_to_verify(
        self, function: CFunction, spec_conversation: SpecConversation, original_file_path: Path
    ) -> Path:
        raise NotImplementedError()
