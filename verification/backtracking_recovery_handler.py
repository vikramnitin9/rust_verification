"""Class implementing backtracking for callee specifications."""

from pathlib import Path

from specifications import BacktrackToCallee, CandidateSpecification, LlmSpecificationGenerator
from util import ParsecResult

from .verification_client import VerificationClient
from .verification_result import Success


class BacktrackingRecoveryHandler:
    """Class implementing backtracking for callee specifications.

    Attributes:
        _llm_specification_generator (LlmSpecificationGenerator): The LLM specification generator.
        _verifier (VerificationClient): The verification client.
    """

    _llm_specification_generator: LlmSpecificationGenerator
    _verifier: VerificationClient

    def __init__(
        self, llm_specification_generator: LlmSpecificationGenerator, verifier: VerificationClient
    ):
        self._llm_specification_generator = llm_specification_generator
        self._verifier = verifier

    def execute(
        self,
        candidate_under_recovery: CandidateSpecification,
        backtracking_policy: BacktrackToCallee,
        conversation: list[dict[str, str]],
        trusted_functions: list[str],
        verified_functions: list[str],
        parsec_result: ParsecResult,
        output_file_path: Path,
    ) -> None:
        """Execute the backtracking strategy for a given candidate spec.

        Args:
            candidate_under_recovery (CandidateSpecification): The candidate spec for which to
                execute backtracking.
            backtracking_policy (BacktrackToCallee): The backtracking policy; comprises the
                reasoning given for backtracking and the callee to backtrack to.
            conversation (list[dict[str, str]]): The LLM conversation.
            trusted_functions (list[str]): The list of trusted functions.
            verified_functions (list[str]): The list of verified functions.
            parsec_result (ParsecResult): The ParsecResult.
            output_file_path (Path): The path to the output file, which comprises functions and
                specifications that successfully verify.

        Raises:
            NotImplementedError: TODO: temporary.
        """
        callee = backtracking_policy.callee_to_backtrack_to
        backtracking_response = self._llm_specification_generator.backtrack_to_callee(
            function=candidate_under_recovery.get_parsec_representation(),
            callee_name=callee,
            backtracking_reasoning=backtracking_policy.reasoning,
            conversation=conversation,
        )
        regenerated_callees_and_specs = CandidateSpecification.get_specified_function_candidates(
            function_name=callee,
            llm_invocation_result=backtracking_response,
            parsec_result=parsec_result,
            path_to_file=output_file_path,
        )
        verified_callee_samples = self._get_verifying_function_samples(
            callee_name=callee,
            candidate_function_samples=regenerated_callees_and_specs,
            trusted_functions=trusted_functions,
            verified_functions=verified_functions,
        )
        if not verified_callee_samples:
            # TODO: What should happen? We should not throw away the (verifying) callee spec.
            raise NotImplementedError()
        # Make a copy of the failing function for each candidate callee sample and see if
        # verification succeeds.

    def _get_verifying_function_samples(
        self,
        callee_name: str,
        candidate_function_samples: list[CandidateSpecification],
        trusted_functions: list[str],
        verified_functions: list[str],
    ) -> list[CandidateSpecification]:
        trusted_functions_copy = trusted_functions.copy()
        verified_functions_copy = verified_functions.copy()
        trusted_functions_copy.remove(callee_name)
        verified_functions_copy.remove(callee_name)
        return [
            sample
            for sample in candidate_function_samples
            if isinstance(
                self._verifier.verify(
                    function_name=callee_name,
                    names_of_trusted_functions=trusted_functions_copy,
                    names_of_verified_functions=verified_functions_copy,
                    file_path=sample.path_to_file,
                ),
                Success,
            )
        ]
