"""Module for generating and repairing specifications at the function-level via LLMs."""

import json
from pathlib import Path

from models import (
    ConversationMessage,
    LlmClient,
    LlmMessage,
    ModelError,
    SystemMessage,
    UserMessage,
)
from util import (
    CFunction,
    FunctionSpecification,
    ParsecResult,
    SpecConversation,
    SpecificationGenerationNextStep,
    extract_function_source_code,
    function_util,
)
from verification import PromptBuilder, ProofState, VerificationClient


class LlmSpecificationGenerator:
    """Class for LLM-driven specification generation and repair.

    The public method is `generate_and_repair_spec()`, which accepts a single function and generates
    a set of potential specifications for it. Each specification may or may not verify.

    Attributes:
        _parsec_result (ParsecResult): The ParseC result to use to obtain functions.
        _prompt_builder (PromptBuilder): Used in creating specification generation/repair prompts.
        _verifier (VerificationClient): The client for specification verification.
        _num_specification_candidates (int): The number of specifications to initially generate.
        _num_repair_iterations (int): The number of repair iterations (i.e., how many times an
            LLM is able to repair a spec).
        _num_repair_candidates (int): The number of repaired specs sampled from an LLM in each
            repair round.
        _system_prompt (str): The system prompt for the LLM.
        _disable_cache (bool): True iff caching should be disabled for LLM responses.
        _llm_client (LlmClient): The client used to invoke LLMs.
    """

    _parsec_result: ParsecResult
    _prompt_builder: PromptBuilder
    _verifier: VerificationClient
    _num_specification_candidates: int
    _num_repair_iterations: int
    _num_repair_candidates: int
    _system_prompt: str
    _disable_cache: bool
    _llm_client: LlmClient

    def __init__(
        self,
        model: str,
        system_prompt: str,
        verifier: VerificationClient,
        parsec_result: ParsecResult,
        num_specification_candidates: int,
        num_repair_candidates: int,
        num_repair_iterations: int,
        disable_cache: bool = False,
    ) -> None:
        """Create a new LlmSpecificationGenerator."""
        self._system_prompt = system_prompt
        self._verifier = verifier
        self._parsec_result = parsec_result
        self._prompt_builder = PromptBuilder()
        self._num_specification_candidates = num_specification_candidates
        self._num_repair_candidates = num_repair_candidates
        self._num_repair_iterations = num_repair_iterations
        self._llm_client = LlmClient(
            model_name=model,
            top_k=num_specification_candidates,
            temperature=0.8,
            disable_cache=disable_cache,
        )

    def generate_and_repair_spec(
        self,
        function: CFunction,
        hint: str,
        proof_state: ProofState,
    ) -> list[SpecConversation]:
        """Return a list of potential specifications for the function.

        Args:
            function (CFunction): The function for which to generate potential specs.
            hint (str): Hints to help guide specification regeneration (i.e., when a
                specification is not accepted or assumed as-is, and is either being repaired or when
                a callee specification is re-generated).
            proof_state (ProofState): The proof state, which includes specifications for callees.

        Returns:
            list[SpecConversation]: A list of potential specifications for the function.
        """
        candidate_specs = self._generate_unrepaired_specs(function=function, hint=hint)

        # TODO: Actually perform some pruning here of the candidate specs.
        pruned_specs = candidate_specs

        repaired_specs = []
        for pruned_spec in pruned_specs:
            repaired_specs.extend(
                # `_repair_spec()` is called whether or not the spec verifies.
                self._repair_spec(
                    spec_conversation=pruned_spec,
                    proof_state=proof_state,
                )
            )
        return repaired_specs

    def _generate_unrepaired_specs(
        self,
        function: CFunction,
        hint: str,
    ) -> list[SpecConversation]:
        """Generate potential specifications for the given function.

        Each LLM sample yields one SpecConversation in the result list.

        # TODO: When `hint` is non-empty, this function is being invoked with the intent
        to repair a spec; we cannot simply grab the source code from the CFunction, it'll be the
        function without any specs. We need a way to get the failed spec.

        Args:
            function (CFunction): The function for which to generate specifications.
            hint (str): Hints to guide specification generation. Only non-empty when
                generating specs during backtracking (i.e., a specification is not accepted or
                assumed as-is, and is either being repaired or when a callee specification is
                re-generated).

        Returns:
            list[SpecConversation]: The generated specifications for the given function, as a
                SpecConversation.
        """
        conversation: list[ConversationMessage] = [SystemMessage(content=self._system_prompt)]
        specification_generation_prompt = self._prompt_builder.specification_generation_prompt(
            function, self._parsec_result
        )
        if hint:
            specification_generation_prompt += "\n\n" + hint
        specification_generation_message = UserMessage(content=specification_generation_prompt)

        try:
            conversation.append(specification_generation_message)
            spec_samples = self._llm_client.get(conversation=tuple(conversation))

            candidate_specified_functions_with_samples = [
                (extract_function_source_code(sample), sample) for sample in spec_samples
            ]
            candidate_specs_with_samples = [
                (function_util.extract_specification(function_from_response.splitlines()), response)
                for function_from_response, response in candidate_specified_functions_with_samples
            ]
            return [
                SpecConversation(
                    function=function,
                    specification=candidate_spec,
                    conversation=[*conversation, LlmMessage(content=sample)],
                )
                for candidate_spec, sample in candidate_specs_with_samples
                if candidate_spec
            ]

        except ModelError as me:
            msg = f"Failed to generate specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _repair_spec(
        self,
        spec_conversation: SpecConversation,
        proof_state: ProofState,
    ) -> list[SpecConversation]:
        """If the spec verifies, return it.  If the spec does not verify, try to repair it.

        Args:
            spec_conversation (SpecConversation): The SpecConversation that ends with the spec that
                may fail to verify.
            proof_state (ProofState): The proof state for the specification.

        Returns:
            list[SpecConversation]: The repaired specifications.
        """
        # This is the return value of the method.
        verified_spec_conversations: list[SpecConversation] = []

        observed_spec_conversations: list[SpecConversation] = []
        current_spec_conversations: list[SpecConversation] = [spec_conversation]
        for i in range(self._num_repair_iterations + 1):
            unverified_spec_conversations: list[SpecConversation] = []
            for current_spec_conversation in current_spec_conversations:
                if current_spec_conversation in observed_spec_conversations:
                    continue

                contents_of_file_to_verify = self._get_content_of_file_to_verify(
                    spec_conversation=current_spec_conversation,
                    original_file_path=self._parsec_result.file_path,
                    proof_state=proof_state,
                )
                function_under_repair = current_spec_conversation.function
                function_under_repair.set_source_code(
                    function_util.get_source_code_with_inserted_spec(
                        function_name=function_under_repair.name,
                        specification=current_spec_conversation.specification,
                        parsec_result=self._parsec_result,
                    )
                )
                current_spec_conversation.contents_of_file_to_verify = contents_of_file_to_verify

                # TODO: Consider refactoring `verify` to consume a `SpecConversation`?
                vresult = self._verifier.verify(
                    function=function_under_repair,
                    spec=current_spec_conversation.specification,
                    proof_state=proof_state,
                    source_code_content=current_spec_conversation.contents_of_file_to_verify,
                )

                if vresult.succeeded:
                    current_spec_conversation.specgen_next_step = (
                        SpecificationGenerationNextStep.ACCEPT_VERIFIED_SPEC
                    )
                    verified_spec_conversations.append(current_spec_conversation)
                else:
                    unverified_spec_conversations.append(current_spec_conversation)

                observed_spec_conversations.append(current_spec_conversation)

            if i == self._num_repair_candidates:
                break

            current_spec_conversations = []
            for unverified_spec_conversation in unverified_spec_conversations:
                contents_of_file_to_verify = unverified_spec_conversation.contents_of_file_to_verify
                if contents_of_file_to_verify is None:
                    msg = "A spec that failed to verify is missing its contents"
                    raise ValueError(msg)
                # Re-verifying the function might seem wasteful, but the result of verification is
                # cached by default, and likely computed in the prior loop.
                vresult = self._verifier.verify(
                    function=unverified_spec_conversation.function,
                    spec=unverified_spec_conversation.specification,
                    proof_state=proof_state,
                    source_code_content=contents_of_file_to_verify,
                )
                next_step_prompt = self._prompt_builder.next_step_prompt(
                    verification_result=vresult
                )
                conversation_updated_with_failure_information = (
                    unverified_spec_conversation.get_conversation_with_message_appended(
                        UserMessage(content=next_step_prompt)
                    )
                )

                model_responses = self._call_llm_for_repair(
                    function=unverified_spec_conversation.function,
                    conversation=tuple(conversation_updated_with_failure_information),
                )
                current_spec_conversations += [
                    SpecConversation(
                        function=unverified_spec_conversation.function,
                        specification=specification,
                        conversation=[
                            *conversation_updated_with_failure_information,
                            LlmMessage(content=response),
                        ],
                        specgen_next_step=self._parse_next_step(response),
                    )
                    for specification, response in model_responses.items()
                ]
        return verified_spec_conversations or [
            spec_conversation
            for spec_conversation in observed_spec_conversations
            if spec_conversation.has_next_step()
        ]

    def _call_llm_for_repair(
        self, function: CFunction, conversation: tuple[ConversationMessage, ...]
    ) -> dict[FunctionSpecification, str]:
        """Call an LLM to repair a failing spec.

        The conversation passed in originates from a `SpecConversation` that has a LLM-generated
        specification that fails to verify.

        The conversation is already appended with a user message that directs the LLM to fix the
        failing spec, and is not modified by this function.

        Args:
            function (CFunction): The function with the failing spec.
            conversation (tuple[ConversationMessage]): The conversation for specification repair,
                which ends with a user message telling the LLM to fix a failing spec.

        Raises:
            RuntimeError: Raised when a failure occurs (e.g., API timeout) during a call to an LLM
                for specification repair.

        Returns:
            dict[FunctionSpecification, str]: A map of repaired specifications and the raw response
                from the LLM from which the repaired specification was extracted.

        """
        try:
            responses = self._llm_client.get(
                conversation=conversation, top_k=self._num_repair_candidates
            )
            candidate_repaired_functions_to_response = {
                extract_function_source_code(response): response for response in responses
            }
            repaired_specs_to_responses: dict[FunctionSpecification, str] = {}
            for function_str, response in candidate_repaired_functions_to_response.items():
                if repaired_spec := function_util.extract_specification(function_str.splitlines()):
                    repaired_specs_to_responses[repaired_spec] = response
            return repaired_specs_to_responses
        except ModelError as me:
            msg = f"Failed to repair specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _parse_next_step(self, llm_response: str) -> SpecificationGenerationNextStep:
        """Parse the next steps for a prompt from an LLM response.

        An LLM is asked to choose a next step and include it in its response when it is asked to
        repair a spec. This function parses the next step to include in a SpecConversation object.

        Args:
            llm_response (str): The LLM response from which to parse a next step.

        Returns:
            SpecificationGenerationNextStep: The next step returned by the LLM in its response.
        """
        llm_response = llm_response.strip()
        # Handle the possibility that the LLM did not follow instructions to return just the plain
        # object.
        llm_response = llm_response.removeprefix("```json").removesuffix("```")

        try:
            return SpecificationGenerationNextStep(json.loads(llm_response)["next_step"])
        except json.JSONDecodeError as je:
            msg = f"The LLM failed to return a valid JSON object: {llm_response}, error = {je}"
            raise RuntimeError(msg) from je
        except KeyError as ke:
            msg = (
                f"The LLM returned valid JSON, but was missing the 'next_step' key: {llm_response}"
            )
            raise RuntimeError(msg) from ke
        except ValueError as ve:
            msg = f"The LLM likely returned an invalid next step: {llm_response}"
            raise RuntimeError(msg) from ve

    def _get_content_of_file_to_verify(
        self,
        spec_conversation: SpecConversation,
        original_file_path: Path,
        proof_state: ProofState,
    ) -> str:
        """Return the content of the file that should be verified.

        Args:
            spec_conversation (SpecConversation): The spec conversation comprising the function and
                the specification under verification.
            original_file_path (Path): The path to the original file where the function is declared.
            proof_state (ProofState): The proof state under which the function is verified.
                # MDE: Should the CFunction object contain a field with the original file path?
                # MDE: That would perhaps yield better encapsulation.

        Returns:
            str: The content of the file that should be verified.

        """
        parsec_result = ParsecResult(original_file_path)
        callees_to_specs = {
            callee: spec
            for callee in parsec_result.get_callees(function=spec_conversation.function)
            if (spec := proof_state.get_specification(function=callee))
        }

        functions_with_specs = {
            spec_conversation.function: spec_conversation.specification
        } | callees_to_specs

        return function_util.get_source_content_with_specifications(
            specified_functions=functions_with_specs, parsec_result=parsec_result
        )
