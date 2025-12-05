"""Module to construct prompts for LLM calls."""

from pathlib import Path
from string import Template

from util import ParsecFunction, ParsecResult, text_util

from .llm_generate_verify_iteration import LlmGenerateVerifyIteration
from .verification_result import Failure


class PromptBuilder:
    """Encapsulates functions used in constructing prompts for LLM calls."""

    SPECIFICATION_GENERATION_PROMPT_TEMPLATE = Path(
        "./prompts/generate-specifications-prompt-template.txt"
    ).read_text()
    SPECIFICATION_REPAIR_PROMPT_TEMPLATE = Template(
        Path("./prompts/repair-specifications-prompt-template.txt").read_text()
    )
    FAILURE_RECOVERY_CLASSIFICATION_PROMPT_TEMPLATE = Template(
        Path("./prompts/failure-recovery-classification-prompt-template.txt").read_text()
    )
    SOURCE_PLACEHOLDER = "<<SOURCE>>"
    CALLEE_CONTEXT_PLACEHOLDER = "<<CALLEE_CONTEXT>>"

    def specification_generation_prompt(
        self, function: ParsecFunction, parsec_result: ParsecResult
    ) -> str:
        """Return the prompt used for specification generation.

        Args:
            function (ParsecFunction): The function for which to generate specifications.
            parsec_result (ParsecResult): The top-level ParseC result.

        Returns:
            str: The initial used for specification generation.
        """
        source_code = function.get_source_code(include_documentation_comments=True)
        prompt = PromptBuilder.SPECIFICATION_GENERATION_PROMPT_TEMPLATE.replace(
            PromptBuilder.SOURCE_PLACEHOLDER, source_code
        )

        callee_context = ""
        if callees := parsec_result.get_callees(function):
            callees_with_specs = [callee for callee in callees if callee.is_specified()]
            if callees_with_specs:
                callee_context = self._get_callee_specs(function.name, callees_with_specs)

        return prompt.replace(PromptBuilder.CALLEE_CONTEXT_PLACEHOLDER, callee_context)

    def specification_repair_prompt(
        self, failing_function: ParsecFunction, verification_failure: Failure
    ) -> str:
        """Return a prompt directing the model to repair a faulty specification.

        Args:
            failing_function (ParsecFunction): The function that does not verify.
            verification_failure (Failure): The failed result of verifying the function.

        Returns:
            str: A prompt directing the model to repair a faulty specification.
        """
        lines_involving_failure = [
            line for line in verification_failure.stdout.splitlines() if "FAILURE" in line
        ]
        candidate_function_source_code = failing_function.get_source_code(
            include_documentation_comments=True,
            include_line_numbers=True,
            should_uncomment_cbmc_annotations=True,
        )
        return PromptBuilder.SPECIFICATION_REPAIR_PROMPT_TEMPLATE.safe_substitute(
            function_name=failing_function.name,
            function_implementation=candidate_function_source_code,
            failure_lines="\n".join(lines_involving_failure),
            stderr=verification_failure.stderr,
        )

    def failure_recovery_classification_prompt(
        self, function: ParsecFunction, failed_iteration: LlmGenerateVerifyIteration
    ) -> str:
        """Return a prompt directing the model to classify a verification failure.

        Args:
            function (str): The function that does not verify.
            failed_iteration (LlmGenerateVerifyIteration): The failed specification generation
                iteration.

        Returns:
            str: A prompt directing the model to classify a verification failure.
        """
        if not isinstance(failed_iteration.verification_result, Failure):
            msg = (
                f"Unable to create a failure recovery classification prompt for "
                f"'{failed_iteration}'"
            )
            raise TypeError(msg)
        explicit_failure_lines = "\n".join(
            text_util.get_lines_with_suffix(
                failed_iteration.verification_result.stdout, suffix="FAILURE"
            )
        )
        return PromptBuilder.FAILURE_RECOVERY_CLASSIFICATION_PROMPT_TEMPLATE.substitute(
            function_name=function.name,
            function_with_specifications=function.get_source_code(
                include_documentation_comments=True, include_line_numbers=True
            ),
            failure_lines=explicit_failure_lines,
            stderr=failed_iteration.verification_result.stderr,
        )

    def _get_callee_specs(self, caller: str, callees_with_specs: list[ParsecFunction]) -> str:
        """Return the callee specifications to add to a prompt.

        Args:
            caller (str): The caller function.
            callees_with_specs (list[ParsecFunction]): The list of callees with specifications.

        Returns:
            str: The callee specifications to add to a prompt.
        """
        callee_context = "\n".join(str(callee) for callee in callees_with_specs)
        return f"{caller} has the following callees:\n{callee_context}"
