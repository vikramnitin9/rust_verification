"""Module for generating and repairing specifications at the function-level via LLMs."""

import json
from collections import deque
from copy import deepcopy

from loguru import logger

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
    ParsecFile,
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
        _parsec_file (ParsecFile): The ParseC file to use to obtain functions.
        _prompt_builder (PromptBuilder): Used in creating specification generation/repair prompts.
        _verifier (VerificationClient): The client for specification verification.
        _num_specification_candidates (int): The number of specifications to initially generate.
        _num_specification_repair_iterations (int): The number of repair iterations (i.e., how many
            times an LLM is able to repair a spec).
        _num_specification_repair_candidates (int): The number of repaired specs sampled from an LLM
            in each repair round.
        _system_prompt (str): The system prompt for the LLM.
        _disable_cache (bool): True iff caching should be disabled for LLM responses.
        _llm_client (LlmClient): The client used to invoke LLMs.
    """

    _parsec_file: ParsecFile
    _prompt_builder: PromptBuilder
    _verifier: VerificationClient
    _num_specification_candidates: int
    _num_specification_repair_iterations: int
    _num_specification_repair_candidates: int
    _system_prompt: str
    _disable_cache: bool
    _llm_client: LlmClient

    def __init__(
        self,
        model: str,
        system_prompt: str,
        verifier: VerificationClient,
        parsec_file: ParsecFile,
        num_specification_candidates: int,
        num_specification_repair_candidates: int,
        num_specification_repair_iterations: int,
        disable_cache: bool = False,
    ) -> None:
        """Create a new LlmSpecificationGenerator."""
        self._system_prompt = system_prompt
        self._verifier = verifier
        self._parsec_file = parsec_file
        self._prompt_builder = PromptBuilder()
        self._num_specification_candidates = num_specification_candidates
        self._num_specification_repair_candidates = num_specification_repair_candidates
        self._num_specification_repair_iterations = num_specification_repair_iterations
        self._llm_client = LlmClient(
            model_name=model,
            top_k=num_specification_candidates,
            temperature=0.8,
            disable_cache=disable_cache,
        )

    # MDE: This function currently does more than its documentation admits, since it also chooses a
    # backtracking strategy.  Move that into a caller of this function.
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
                Each may or may not verify.
        """
        candidate_specs = self._generate_unrepaired_specs(
            function=function, hint=hint, proof_state=proof_state
        )

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
        proof_state: ProofState,
        hint: str,
    ) -> list[SpecConversation]:
        """Generate potential specifications for the given function.

        Each LLM sample yields one SpecConversation in the result list.

        Args:
            function (CFunction): The function for which to generate specifications.
            hint (str): Hints to guide specification generation. Only non-empty when
                generating specs during backtracking (i.e., a callee specification is being
                re-generated).
            proof_state (ProofState): The proof state under which specifications are generated
                (relevant for looking up callee specifications).

        Returns:
            list[SpecConversation]: The generated specifications for the given function, as a
                SpecConversation.
        """
        conversation: list[ConversationMessage] = [SystemMessage(content=self._system_prompt)]
        specification_generation_prompt = self._prompt_builder.specification_generation_prompt(
            function, self._parsec_file
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
            unrepaired_spec_conversations = []
            for candidate_spec, sample in candidate_specs_with_samples:
                if candidate_spec:
                    function_code_with_specs = function_util.get_source_code_with_inserted_spec(
                        function_name=function.name,
                        specification=candidate_spec,
                        parsec_file=self._parsec_file,
                    )
                    function.set_specifications(specifications=candidate_spec)
                    function.set_source_code(function_code_with_specs)
                    unrepaired_spec_conversations.append(
                        SpecConversation.create(
                            function=function,
                            specification=candidate_spec,
                            conversation=(*conversation, LlmMessage(content=sample)),
                            parsec_file=self._parsec_file,
                            existing_specs=proof_state.get_specifications(),
                        )
                    )
                else:
                    logger.warning(f"Failed to parse a specification from: {sample}")

            return unrepaired_spec_conversations

        except ModelError as me:
            msg = f"Failed to generate specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    # MDE: The name and first line of documentation of this function omit important functionality of
    # choosing the next step if no verified specification could be generated.  Currently, that
    # functionality is independent of the rest of the functionality of this function.  (It occurs in
    # the call to `_call_llm_for_backtracking_strategy()` at the very end of the function.)
    # Therefore, I suggest keeping the name and spec of this function simple:  it just tries to do
    # repair.  Move the unrelated choice of whethere to backtrack into a client.
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
            list[SpecConversation]: A list of specifications that successfully verify (they either
                verified in the first place, or were repaired), or a list of specifications that
                ultimately failed to be repaired with a next step set for specification generation.
        """
        # Below are the two possible return values of this method.
        verified_spec_conversations: list[SpecConversation] = []
        specs_that_failed_repair: list[SpecConversation] = []

        # Check whether the given spec even needs repair.
        vresult = self._verifier.verify(
            function=spec_conversation.function,
            spec=spec_conversation.specification,
            proof_state=proof_state,
            source_file_content=spec_conversation.contents_of_file_to_verify,
        )
        if vresult.succeeded:
            # MDE: I don't think this assignment is needed.  Other code can cheaply check whether
            # verification succeeded.
            spec_conversation.specgen_next_step = (
                SpecificationGenerationNextStep.ACCEPT_VERIFIED_SPEC
            )
            verified_spec_conversations.append(spec_conversation)
            return verified_spec_conversations

        # Each tuple comprises the spec conversation, and the repair count (i.e., how many times a
        # a repair was attempted on it).
        specs_to_repair: deque[tuple[SpecConversation, int]] = deque([(spec_conversation, 0)])
        visited_specs: set[SpecConversation] = set()

        # Attempt to repair each broken spec.
        while specs_to_repair:
            spec_under_repair, num_repair_attempts = specs_to_repair.popleft()

            if spec_under_repair in visited_specs:
                # We've seen this spec before, move on.
                continue
            visited_specs.add(spec_under_repair)

            # Re-verifying the function might seem wasteful, but the result of verification is
            # cached by default, and likely computed in the prior loop.
            vresult = self._verifier.verify(
                function=spec_under_repair.function,
                spec=spec_under_repair.specification,
                proof_state=proof_state,
                source_file_content=spec_under_repair.contents_of_file_to_verify,
            )

            if vresult.succeeded:
                # No need to iterate further, there is nothing to repair.
                # MDE: I don't think this assignment is needed.  Other code can cheaply check
                # whether verification succeeded.
                spec_under_repair.specgen_next_step = (
                    SpecificationGenerationNextStep.ACCEPT_VERIFIED_SPEC
                )
                verified_spec_conversations.append(spec_under_repair)
                continue

            specs_that_failed_repair.append(spec_under_repair)
            if num_repair_attempts >= self._num_specification_repair_iterations:
                # We've iteratively repaired this spec as much as we had to, but failed.
                continue

            # Attempt repair.
            repair_prompt = self._prompt_builder.repair_prompt(verification_result=vresult)
            conversation_updated_with_repair_prompt = (
                spec_under_repair.get_conversation_with_message_appended(
                    message=UserMessage(content=repair_prompt)
                )
            )
            newly_repaired_specs_with_responses = self._call_llm_for_repair(
                function=spec_under_repair.function,
                conversation=conversation_updated_with_repair_prompt,
            )

            # Add all repaired specs to the queue, increment repair count.
            for newly_repaired_spec, response in newly_repaired_specs_with_responses:
                function_under_repair_copy = deepcopy(spec_under_repair.function)
                function_under_repair_copy.set_specifications(newly_repaired_spec)
                next_spec_conversation = SpecConversation.create(
                    function=function_under_repair_copy,
                    specification=newly_repaired_spec,
                    conversation=(
                        *conversation_updated_with_repair_prompt,
                        LlmMessage(content=response),
                    ),
                    parsec_file=self._parsec_file,
                    existing_specs=proof_state.get_specifications(),
                )
                specs_to_repair.append((next_spec_conversation, num_repair_attempts + 1))

        return verified_spec_conversations or [
            self._call_llm_for_backtracking_strategy(
                spec_conversation=unrepairable_spec, proof_state=proof_state
            )
            for unrepairable_spec in specs_that_failed_repair
        ]

    def _call_llm_for_repair(
        self, function: CFunction, conversation: tuple[ConversationMessage, ...]
    ) -> tuple[tuple[FunctionSpecification, str], ...]:
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
            tuple[tuple[FunctionSpecification, str], ...]: A tuple of function specifications paired
                with the raw LLM response from which they were extracted.

        """
        try:
            responses = self._llm_client.get(
                conversation=conversation, top_k=self._num_specification_repair_candidates
            )
            repaired_specs_with_responses: list[tuple[FunctionSpecification, str]] = []
            for response in responses:
                if repaired_spec := self._parse_specification_from_response(response):
                    repaired_specs_with_responses.append((repaired_spec, response))
                else:
                    logger.warning(f"Failed to parse a specification from: {response}")
            return tuple(repaired_specs_with_responses)
        except ModelError as me:
            msg = f"Failed to repair specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _call_llm_for_backtracking_strategy(
        self, spec_conversation: SpecConversation, proof_state: ProofState
    ) -> SpecConversation:
        """Return a SpecConversation that resulted from asking an LLM for a backtracking strategy.

        Args:
            spec_conversation (SpecConversation): The SpecConversation for a specification that
                failed repair.
            proof_state (ProofState): The proof state under which verification fails.

        Returns:
            SpecConversation: A SpecConversation that includes the backtracking strategy decided by
                an LLM.
        """
        vresult = self._verifier.verify(
            function=spec_conversation.function,
            spec=spec_conversation.specification,
            proof_state=proof_state,
            source_file_content=spec_conversation.contents_of_file_to_verify,
        )
        next_step_prompt = self._prompt_builder.next_step_prompt(verification_result=vresult)
        conversation_with_next_step_prompt = (
            spec_conversation.get_conversation_with_message_appended(
                message=UserMessage(content=next_step_prompt)
            )
        )

        # Give us one backtracking decision, for now.
        backtracking_samples = self._llm_client.get(
            conversation=conversation_with_next_step_prompt, top_k=1
        )
        backtracking_decision = backtracking_samples[0]

        return SpecConversation(
            function=spec_conversation.function,
            specification=spec_conversation.specification,
            conversation=(
                *conversation_with_next_step_prompt,
                LlmMessage(content=backtracking_decision),
            ),
            contents_of_file_to_verify=spec_conversation.contents_of_file_to_verify,
            specgen_next_step=self._parse_next_step(backtracking_decision),
        )

    def _parse_specification_from_response(self, llm_response: str) -> FunctionSpecification | None:
        """Return the specification parsed from an LLM response.

        Args:
            llm_response (str): The LLM response from which to parse a specification.

        Returns:
            FunctionSpecification | None: The parsed specification, or None.
        """
        function_in_response = extract_function_source_code(llm_response)
        return function_util.extract_specification(function_in_response.splitlines())

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
