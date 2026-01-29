"""Module for generating and repairing function specifications using an LLM."""

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
    AcceptVerifiedSpec,
    AssumeSpecAsIs,
    BacktrackToCallee,
    CFunction,
    FunctionSpecification,
    ParsecFile,
    SpecConversation,
    SpecificationGenerationNextStep,
    fix_syntax,
    function_util,
    parse_expressions_for_spec,
)
from verification import PromptBuilder, ProofState, VerificationClient, VerificationInput


class LlmSpecificationGenerator:
    """Class for LLM-driven specification generation and repair.

    The public method is `generate_and_repair_spec()`, which accepts a single function and generates
    a set of potential specifications for it. Each specification may or may not verify.

    Attributes:
        _prompt_builder (PromptBuilder): Used in creating specification generation/repair prompts.
        _verifier (VerificationClient): The client for specification verification.
        _num_specification_candidates (int): The number of specifications the LLM should generate.
        _num_specification_repair_iterations (int): The number of repair iterations (i.e., how many
            times an LLM is able to repair a spec).
        _num_specification_repair_candidates (int): The number of repaired specs sampled from an LLM
            in each repair round.
        _system_prompt (str): The system prompt for the LLM.
        _disable_llm_cache (bool): True iff caching should be disabled for LLM responses.
        _fix_illegal_syntax (bool): True iff syntax fixing should be enabled for specifications.
        _llm_client (LlmClient): The client used to invoke LLMs.
    """

    _prompt_builder: PromptBuilder
    _verifier: VerificationClient
    _num_specification_candidates: int
    _num_specification_repair_iterations: int
    _num_specification_repair_candidates: int
    _system_prompt: str
    _disable_llm_cache: bool
    _fix_illegal_syntax: bool
    _llm_client: LlmClient

    def __init__(
        self,
        model: str,
        temperature: float,
        system_prompt: str,
        verifier: VerificationClient,
        num_specification_candidates: int,
        num_specification_repair_candidates: int,
        num_specification_repair_iterations: int,
        fix_illegal_syntax: bool,
        disable_llm_cache: bool = False,
    ) -> None:
        """Create a new LlmSpecificationGenerator."""
        self._system_prompt = system_prompt
        self._verifier = verifier
        self._prompt_builder = PromptBuilder()
        self._num_specification_candidates = num_specification_candidates
        self._num_specification_repair_candidates = num_specification_repair_candidates
        self._num_specification_repair_iterations = num_specification_repair_iterations
        self._fix_illegal_syntax = fix_illegal_syntax
        self._llm_client = LlmClient(
            model_name=model,
            top_k=num_specification_candidates,
            temperature=temperature,
            disable_llm_cache=disable_llm_cache,
        )

    def generate_and_repair_spec(
        self,
        function: CFunction,
        parsec_file: ParsecFile,
        hint: str,
        proof_state: ProofState,
    ) -> list[SpecConversation]:
        """Return a list of potential specifications for the function.

        Args:
            function (CFunction): The function for which to generate potential specs.
            parsec_file (ParsecFile): The file that contains `function`.
            hint (str): Hints to help guide specification regeneration (i.e., when a
                specification is not accepted or assumed as-is, and is either being repaired or when
                a callee specification is re-generated).
            proof_state (ProofState): The proof state, which includes specifications for callees.

        Returns:
            list[SpecConversation]: A list of potential specifications for the function.
                Each may or may not verify.
        """
        candidate_speccs = self._generate_unrepaired_speccs(
            function=function, parsec_file=parsec_file, hint=hint, proof_state=proof_state
        )

        # Right now, the "pruning" strategy is just to partition the candidate specs into a set
        # of verifying and invalid specs.
        verifying_speccs, non_verifying_speccs = self._get_verifying_and_non_verifying_speccs(
            # MDE: Why call `tuple` here?  The client only iterates over `candidate_speccs`.
            speccs=tuple(candidate_speccs),
            proof_state=proof_state,
        )

        repaired_speccs = []
        for non_verifying_specc in non_verifying_speccs:
            repaired_speccs.extend(
                # `_repair_spec()` is called whether or not the spec verifies.
                self._repair_spec(
                    specc=non_verifying_specc, proof_state=proof_state, parsec_file=parsec_file
                )
            )
        return [*verifying_speccs, *repaired_speccs]

    def _generate_unrepaired_speccs(
        self,
        function: CFunction,
        parsec_file: ParsecFile,
        hint: str,
        proof_state: ProofState,
    ) -> list[SpecConversation]:
        """Generate potential specifications for the given function.

        Each LLM sample yields one SpecConversation in the result list.

        Args:
            function (CFunction): The function for which to generate specifications.
            parsec_file (ParsecFile): The file that contains `function`.
            hint (str): Hints to guide specification generation. Only non-empty when
                generating specs during backtracking (i.e., a callee specification is being
                re-generated).
            proof_state (ProofState): the proof state

        Returns:
            list[SpecConversation]: The generated specifications for the given function.
        """
        conversation: list[ConversationMessage] = [SystemMessage(content=self._system_prompt)]
        specification_generation_prompt = self._prompt_builder.specification_generation_prompt(
            function, parsec_file
        )
        if hint:
            specification_generation_prompt += "\n\n" + hint
        specification_generation_message = UserMessage(content=specification_generation_prompt)

        try:
            conversation.append(specification_generation_message)
            llm_responses = self._llm_client.get(conversation=tuple(conversation))

            specs_with_llm_responses = [
                (parse_expressions_for_spec(llm_response), llm_response)
                for llm_response in llm_responses
            ]
            result_spec_conversations = []
            for candidate_spec, llm_response in specs_with_llm_responses:
                if candidate_spec:
                    if self._fix_illegal_syntax:
                        candidate_spec = fix_syntax(candidate_spec)
                    function_code_with_specs = function_util.get_source_code_with_inserted_spec(
                        function_name=function.name,
                        specification=candidate_spec,
                        parsec_file=parsec_file,
                    )
                    function.set_specifications(specifications=candidate_spec)
                    function.set_source_code(function_code_with_specs)
                    result_spec_conversations.append(
                        SpecConversation.create(
                            function=function,
                            specification=candidate_spec,
                            conversation=(*conversation, LlmMessage(content=llm_response)),
                            parsec_file=parsec_file,
                            existing_specs=proof_state.get_specifications(),
                        )
                    )
                else:
                    logger.warning(f"Failed to parse a specification from: {llm_response}")

            return result_spec_conversations

        except ModelError as me:
            msg = f"Failed to generate specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def _repair_spec(
        self,
        specc: SpecConversation,
        proof_state: ProofState,
        parsec_file: ParsecFile,
    ) -> list[SpecConversation]:
        """If the spec verifies, return it.  If the spec does not verify, try to repair it.

        Args:
            specc (SpecConversation): The SpecConversation that ends with the spec that
                may fail to verify.
            proof_state (ProofState): The proof state for the specification.
            parsec_file (ParsecFile): The file being verified.

        Returns:
            list[SpecConversation]: A list of specifications that successfully verify (they either
                verified in the first place, or were repaired), or a list of specifications that
                ultimately failed repair.
        """
        # Check whether the given spec even needs repair.
        vinput = VerificationInput(
            function=specc.function,
            spec=specc.specification,
            context=proof_state.get_current_context(specc.function),
            contents_of_file_to_verify=specc.contents_of_file_to_verify,
        )
        vresult = self._verifier.verify(vinput=vinput)
        if vresult.succeeded:
            specc.next_step = AcceptVerifiedSpec()
            return [specc]

        # These two variables are the two possible return values of this method.
        verified_speccs: list[SpecConversation] = []
        speccs_that_failed_repair: list[SpecConversation] = []

        # Each tuple comprises the spec conversation, and the repair count (i.e., how many times a
        # a repair was attempted on it).
        speccs_to_repair: deque[tuple[SpecConversation, int]] = deque([(specc, 0)])
        visited_speccs: set[SpecConversation] = set()

        # Attempt to repair each broken spec.
        while speccs_to_repair:
            specc_under_repair, num_repair_attempts = speccs_to_repair.popleft()

            if specc_under_repair in visited_speccs:
                # We've seen this spec before, move on.
                continue
            visited_speccs.add(specc_under_repair)

            # Re-verifying the function might seem wasteful, but the result of verification is
            # cached by default, and likely computed in the prior loop.
            vinput = VerificationInput(
                function=specc_under_repair.function,
                spec=specc_under_repair.specification,
                context=proof_state.get_current_context(specc_under_repair.function),
                contents_of_file_to_verify=specc_under_repair.contents_of_file_to_verify,
            )
            vresult = self._verifier.verify(vinput=vinput)

            if vresult.succeeded:
                # No need to iterate further, there is nothing to repair.
                specc_under_repair.next_step = AcceptVerifiedSpec()
                verified_speccs.append(specc_under_repair)
                continue

            speccs_that_failed_repair.append(specc_under_repair)
            if num_repair_attempts >= self._num_specification_repair_iterations:
                # We've iteratively repaired this spec as much as we could, but failed.
                continue

            # Attempt repair.
            repair_prompt = self._prompt_builder.repair_prompt(verification_result=vresult)
            conversation_updated_with_repair_prompt = (
                specc_under_repair.get_conversation_with_message_appended(
                    message=UserMessage(content=repair_prompt)
                )
            )
            newly_repaired_specs_with_llm_responses = self._call_llm_for_repair(
                function=specc_under_repair.function,
                conversation=conversation_updated_with_repair_prompt,
            )

            # Add all repaired specs to the queue, increment repair count.
            for newly_repaired_spec, response in newly_repaired_specs_with_llm_responses:
                if self._fix_illegal_syntax:
                    newly_repaired_spec = fix_syntax(newly_repaired_spec)
                function_under_repair_copy = deepcopy(specc_under_repair.function)
                function_under_repair_copy.set_specifications(newly_repaired_spec)
                next_specc = SpecConversation.create(
                    function=function_under_repair_copy,
                    specification=newly_repaired_spec,
                    conversation=(
                        *conversation_updated_with_repair_prompt,
                        LlmMessage(content=response),
                    ),
                    parsec_file=parsec_file,
                    existing_specs=proof_state.get_specifications(),
                )
                speccs_to_repair.append((next_specc, num_repair_attempts + 1))

        return verified_speccs or speccs_that_failed_repair

    def _call_llm_for_repair(
        self,
        function: CFunction,
        conversation: tuple[ConversationMessage, ...],
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
            repaired_specs_with_llm_responses: list[tuple[FunctionSpecification, str]] = []
            for response in responses:
                if repaired_spec := parse_expressions_for_spec(response):
                    repaired_specs_with_llm_responses.append((repaired_spec, response))
                else:
                    logger.warning(f"Failed to parse a specification from: {response}")
            return tuple(repaired_specs_with_llm_responses)
        except ModelError as me:
            msg = f"Failed to repair specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def call_llm_for_next_steps(
        self, spec_conversation: SpecConversation, proof_state: ProofState
    ) -> tuple[SpecConversation, ...]:
        """Return SpecConversations produced by asking an LLM for next steps (e.g., backtracking).

        Args:
            spec_conversation (SpecConversation): A SpecConversation that ends with a specification
                that failed repair.
            proof_state (ProofState): The proof state under which verification fails.

        Returns:
            tuple[SpecConversation,...]: SpecConversations that includes next steps
                (e.g., backtracking) decided by an LLM.
        """
        vinput = VerificationInput(
            function=spec_conversation.function,
            spec=spec_conversation.specification,
            context=proof_state.get_current_context(spec_conversation.function),
            contents_of_file_to_verify=spec_conversation.contents_of_file_to_verify,
        )
        vresult = self._verifier.verify(vinput=vinput)
        next_step_prompt = self._prompt_builder.next_step_prompt(verification_result=vresult)
        conversation_with_next_step_prompt = (
            spec_conversation.get_conversation_with_message_appended(
                message=UserMessage(content=next_step_prompt)
            )
        )

        # Give us one next-step (e.g., backtracking) decision, for now.
        next_step_llm_responses = self._llm_client.get(
            conversation=conversation_with_next_step_prompt, top_k=1
        )
        next_step_decision = next_step_llm_responses[0]

        # We currently determine a *single* next step. But, this might change in the future.
        return (
            SpecConversation(
                function=spec_conversation.function,
                specification=spec_conversation.specification,
                conversation=(
                    *conversation_with_next_step_prompt,
                    LlmMessage(content=next_step_decision),
                ),
                contents_of_file_to_verify=spec_conversation.contents_of_file_to_verify,
                next_step=self._parse_next_step(next_step_decision),
            ),
        )

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
            llm_response_dict = json.loads(llm_response)
            match llm_response_dict["next_step"]:
                case "ASSUME_SPEC_AS_IS":
                    return AssumeSpecAsIs()
                case "BACKTRACK_TO_CALLEE":
                    return BacktrackToCallee(
                        callee=llm_response_dict["callee"],
                        hint=llm_response_dict["postcondition_strengthening_description"],
                    )
                case unexpected_step:
                    msg = f"Unexpected next step for specification generation = '{unexpected_step}'"
                    raise RuntimeError(msg)
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

    def _get_verifying_and_non_verifying_speccs(
        self, speccs: tuple[SpecConversation, ...], proof_state: ProofState
    ) -> tuple[tuple[SpecConversation, ...], tuple[SpecConversation, ...]]:
        """Return a tuple of verifying specs and invalid specs.

        Args:
            speccs (tuple[SpecConversation, ...]): The list of spec conversations, each
                may or may not verify.
            proof_state (ProofState): The proof state.

        Returns:
            tuple[tuple[SpecConversation, ...], tuple[SpecConversation, ...]]: A tuple comprising
                specs that verify and specs that are invalid.
        """
        verified_speccs = []
        non_verifying_speccs = []
        for specc in speccs:
            vinput = VerificationInput(
                function=specc.function,
                spec=specc.specification,
                context=proof_state.get_current_context(specc.function),
                contents_of_file_to_verify=specc.contents_of_file_to_verify,
            )
            vresult = self._verifier.verify(vinput=vinput)
            if vresult.succeeded:
                verified_speccs.append(specc)
            else:
                non_verifying_speccs.append(specc)

        return tuple(verified_speccs), tuple(non_verifying_speccs)
