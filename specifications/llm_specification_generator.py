"""Module for generating and repairing specifications via LLMs."""

from models import LLMGen, ModelError, get_llm_generation_with_model
from util import (
    BacktrackStrategy,
    FunctionSpecification,
    ParsecFile,
    ParsecFunction,
    extract_function,
    function_util,
)
from verification import PromptBuilder, ProofState, VerificationClient, VerificationResult


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
    _system_prompt: str

    def __init__(
        self,
        model: str,
        system_prompt: str,
        verifier: VerificationClient,
        num_specification_generation_candidates: int,
    ):
        """Create a new LlmSpecificationGenerator."""
        self._llm = get_llm_generation_with_model(model)
        self._system_prompt = system_prompt
        self._verifier = verifier
        self._prompt_builder = PromptBuilder()
        self._num_specification_generation_candidates = num_specification_generation_candidates

    def try_to_specify(self, function: ParsecFunction, hints: str) -> list[FunctionSpecification]:
        # TODO: Somehow incorporate `hints` into the prompt.
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
            return [
                function_util.extract_specification(function.splitlines())
                for function in candidate_specified_functions
            ]

        except ModelError as me:
            msg = f"Failed to generate specifications for '{function.name}'"
            raise RuntimeError(msg) from me

    def choose_next_step(
        self,
        function: ParsecFunction,
        candidate_specs: list[FunctionSpecification],
        proof_state: ProofState,
    ) -> list[tuple[FunctionSpecification, BacktrackStrategy]]:
        """Placeholder for documentation.

        TODO: Document me.

        Args:
            function (ParsecFunction): The function under specification generation/verification.
            candidate_specs (list[FunctionSpecification]): The candidate specifications for the
                function.
            proof_state (ProofState): The proof state associated with the function.

        Returns:
            list[tuple[FunctionSpecification, BacktrackStrategy]]: A specifications and their
                backtracking strategies.
        """
        # TODO: Actually perform some pruning here of the candidate specs first.
        pruned_specs = candidate_specs
        next_steps = []
        for spec in pruned_specs:
            vresult = self._verifier.verify_function_with_spec(
                function_name=function.name, spec=spec, proof_state=proof_state
            )
            if not vresult.succeeded:
                # TODO: Call an LLM and ask it for a list of callees to possibly backtrack to.
                backtrack_strategies = []
                next_steps.extend(
                    (spec, backtrack_strategy) for backtrack_strategy in backtrack_strategies
                )
        return next_steps

    def _repair_spec(
        self,
        function: ParsecFunction,
        spec: FunctionSpecification,
        proof_state: ProofState,
        num_repair_iterations: int,
    ) -> list[FunctionSpecification]:
        observed_specs = []
        verified_specs = []
        current_specs = [spec]
        for _ in range(num_repair_iterations):
            unverified_spec_vresults: list[VerificationResult] = []
            for current_spec in current_specs:
                if current_spec in observed_specs:
                    # We've seen this spec already, move on.
                    continue
                observed_specs.append(current_spec)
                vresult = self._verifier.verify_function_with_spec(function.name, spec, proof_state)
                if vresult.succeeded:
                    verified_specs.append(current_spec)
                else:
                    unverified_spec_vresults.append(vresult)

            current_specs.extend(
                self._call_llm_for_repair(vresult) for vresult in unverified_spec_vresults
            )
        return verified_specs or observed_specs

    def _call_llm_for_repair(
        self, verification_result: VerificationResult
    ) -> FunctionSpecification:
        raise NotImplementedError("Implement me")
