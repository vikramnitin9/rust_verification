"""Module for generating and repairing specifications at the function-level via LLMs."""

import json
from pathlib import Path

from models import (
    ConversationMessage,
    LLMGen,
    LlmMessage,
    ModelError,
    SystemMessage,
    UserMessage,
    get_llm_generation_with_model,
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

from .llm_sample_cache import LlmSampleCache


class LlmSpecificationGenerator:
    """Class for LLM-driven specification generation and repair.

    The public method is `generate_and_repair_spec()`, which accepts a single function and generates
    a set of potential specifications for it. Each specification may or may not verify.

    Attributes:
        _parsec_file (ParsecFile): The ParseC file to use to obtain functions.
        _prompt_builder (PromptBuilder): Used in creating specification generation/repair prompts.
        _llm (LLMGen): The client used to invoke LLMs.
        _verifier (VerificationClient): The client for specification verification.
        _num_specification_candidates (int): The number of specifications to initially generate.
        _num_repair_iterations (int): The number of repair iterations (i.e., how many times an
            LLM is able to repair a spec).
        _num_repair_candidates (int): The number of repaired specs sampled from an LLM in each
            repair round.
        _system_prompt (str): The system prompt for the LLM.
        _llm_sample_cache (LlmSampleCache): The cache mapping LLM prompts and samples.
        _use_cache (bool): True iff the LLM sample cache should be used.
            # MDE: Can eliminate the `_use_cache` field by testing whether `_llm_sample_cache` is
            # None.
    """

    _parsec_file: ParsecFile
    _prompt_builder: PromptBuilder
    _llm: LLMGen
    _verifier: VerificationClient
    _num_specification_candidates: int
    _num_repair_iterations: int
    _num_repair_candidates: int
    _system_prompt: str
    _llm_sample_cache: LlmSampleCache
    _use_cache: bool

    def __init__(
        self,
        # MDE: Maybe pass in an LlmCache, which can encapsulate the model and the system prompt.
        model: str,
        system_prompt: str,
        verifier: VerificationClient,
        parsec_file: ParsecFile,
        num_specification_candidates: int,
        num_repair_candidates: int,
        num_repair_iterations: int,
        use_cache: bool = False,
    ) -> None:
        """Create a new LlmSpecificationGenerator."""
        self._llm = get_llm_generation_with_model(model)
        self._system_prompt = system_prompt
        self._verifier = verifier
        self._parsec_file = parsec_file
        self._prompt_builder = PromptBuilder()
        self._num_specification_candidates = num_specification_candidates
        self._num_repair_candidates = num_repair_candidates
        self._num_repair_iterations = num_repair_iterations
        self._llm_sample_cache = LlmSampleCache()
        self._use_cache = use_cache

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

        # MDE: I think the following "TODO" is wrong.  Repair is done elsewhere, and it does not
        # call this function.
        # TODO: When `hint` is non-empty, this function is being invoked with the intent
        to repair a spec; we cannot simply grab the source code from the CFunction, it'll be the
        function without any specs. We need a way to get the failed spec.

        Args:
            function (CFunction): The function for which to generate specifications.
            hint (str): Hints to guide specification generation. Only non-empty when
                generating specs during backtracking (i.e., a specification is not accepted or
                assumed as-is, and is either being repaired or when a callee specification is
                re-generated).
                # MDE: Same comment as above: delete "either being repaired or".

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

        # MDE: As mentioned in my comments on `llm_sample_cache.py`, I think that invoking the LLM
        # should be encapsulated in an LlmClient or LlmInvoker class.  This client code should not
        # be aware of whether there is a cache miss or a cache hit, or even of whether a cache
        # exists.
        try:
            conversation.append(specification_generation_message)
            spec_samples = None
            if self._use_cache:
                spec_samples = self._llm_sample_cache.read(specification_generation_prompt)
            if not spec_samples:
                # Cache miss.
                spec_samples = self._llm.gen(
                    tuple(conversation), top_k=self._num_specification_candidates, temperature=0.8
                )
                self._llm_sample_cache.write(
                    prompt=specification_generation_prompt, samples=spec_samples
                )

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
                # MDE: As currently implemented, the repaired specs may or may not verify.  If they
                # don't verify, then what is the point of returning them?  We have already done as
                # much repair as we are willing to do (that is, num_repair_iterations).  Maybe this
                # method should return a list of specs that verify, which may be empty.
        """
        # This is the return value of the method.
        verified_spec_conversations: list[SpecConversation] = []

        observed_spec_conversations: list[SpecConversation] = []
        current_spec_conversations: list[SpecConversation] = [spec_conversation]
        # MDE: Please document how the above three variables are used.  (I did one of them in the
        # other branch, which should be merged before this comment is addressed.)
        for i in range(self._num_repair_iterations + 1):
            unverified_spec_conversations: list[SpecConversation] = []
            for current_spec_conversation in current_spec_conversations:
                if current_spec_conversation in observed_spec_conversations:
                    # MDE: I don't understand how this can happen.  `current_spec_conversation` is
                    # created by extending some existing conversation, so it will never have been
                    # previously observed.  What am I missing?
                    continue

                contents_of_file_to_verify = self._get_content_of_file_to_verify(
                    spec_conversation=current_spec_conversation,
                    original_file_path=self._parsec_file.file_path,
                    proof_state=proof_state,
                )
                function_under_repair = current_spec_conversation.function
                function_under_repair.set_source_code(
                    function_util.get_source_code_with_inserted_spec(
                        function_name=function_under_repair.name,
                        specification=current_spec_conversation.specification,
                        parsec_file=self._parsec_file,
                    )
                )
                current_spec_conversation.contents_of_file_to_verify = contents_of_file_to_verify

                # TODO: Consider refactoring `verify` to consume a `SpecConversation`?
                vresult = self._verifier.verify(
                    function=function_under_repair,
                    spec=current_spec_conversation.specification,
                    proof_state=proof_state,
                    # MDE: Is the source code available in the `function` argument in this call?
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

            # MDE: This looks very suspicious to me.  i is assigned from `_num_repair_iterations`,
            # but here it is compared to `_num_repair_candidates`.  Those are conceptually different
            # types.  `_num_repair_candidates` is how many samples to take from the LLM response,
            # and is currently always 1.
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
                # MDE: Write a brief comment about why this doesn't use `append()`.  Probably
                # because it wants to create a new list rather than modify an existing list.
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
            responses = self._llm.gen(
                messages=tuple(conversation), top_k=self._num_repair_candidates, temperature=0.8
            )
            # MDE: Why is this a map rather than a list of pairs?  Using a map suggests to a reader
            # that lookup will be done, but this is only iterated over.  In fact, even a list of
            # pairs is not necessary.  The for loop below can iterate over `responses` and call
            # `extract_function_source_code(response)` within the loop.
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

        # MDE: Is this the original content of the file, as written by the user?  Or does it contain
        # some inserted specifications and, if so, which ones?

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
        parsec_file = ParsecFile(original_file_path)
        callees_to_specs = {
            callee: spec
            for callee in parsec_file.get_callees(function=spec_conversation.function)
            if (spec := proof_state.get_specification(function=callee))
        }

        functions_with_specs = {
            spec_conversation.function: spec_conversation.specification
        } | callees_to_specs

        return function_util.get_source_file_content_with_specifications(
            specified_functions=functions_with_specs,
            parsec_file=parsec_file,
            original_source_file_path=original_file_path,
        )
