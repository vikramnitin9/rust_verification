"""Module to construct prompts for LLM calls."""

import tempfile
from pathlib import Path
from string import Template

from util import CFunction, ParsecFile, text_util

from .verification_result import VerificationResult


class PromptBuilder:
    """A collection of functions used in constructing prompts for LLM calls."""

    SPECIFICATION_GENERATION_PROMPT_TEMPLATE = Path(
        "./prompts/generate-specifications-prompt-template.txt"
    ).read_text()
    SPECIFICATION_REPAIR_PROMPT_TEMPLATE = Template(
        Path("./prompts/repair-specifications-prompt-template.txt").read_text()
    )
    NEXT_STEP_PROMPT_TEMPLATE = Template(
        Path("./prompts/next-step-prompt-template.txt").read_text()
    )
    SOURCE_PLACEHOLDER = "<<SOURCE>>"
    CALLEE_CONTEXT_PLACEHOLDER = "<<CALLEE_CONTEXT>>"

    def specification_generation_prompt(self, function: CFunction) -> str:
        """Return the prompt used for specification generation.

        The prompt consists of the C function and the "context", which is the specifications of its
        callees.

        Args:
            function (CFunction): The function for which to generate specifications.

        Returns:
            str: The initial prompt used for specification generation.

        """
        source_code = function.get_original_source_code(include_documentation_comments=True)
        prompt = PromptBuilder.SPECIFICATION_GENERATION_PROMPT_TEMPLATE.replace(
            PromptBuilder.SOURCE_PLACEHOLDER, source_code
        )

        callee_context = ""
        if callees := function.parsec_file.get_callees(function):
            if callees_with_specs := [callee for callee in callees if callee.has_specification()]:
                callee_context = self._get_callee_specs(function.name, callees_with_specs)

        return prompt.replace(PromptBuilder.CALLEE_CONTEXT_PLACEHOLDER, callee_context)

    def next_step_prompt(self, verification_result: VerificationResult) -> str:
        """Return prompt text asking the LLM to decide on next steps for a failing specification.

        Args:
            verification_result (VerificationResult): The verification result for a failing spec.

        Returns:
            str: Prompt text asking the LLM to decide on next steps for a failing specification.
        """
        with tempfile.NamedTemporaryFile(mode="w+t", suffix=".c") as tmp_f:
            # The source code might have CBMC annotations, comment them out.
            source_code_lines = verification_result.get_source_code_contents().splitlines()
            source_code_cbmc_commented_out = "\n".join(
                text_util.comment_out_cbmc_annotations(lines=source_code_lines)
            )
            tmp_f.write(source_code_cbmc_commented_out)
            tmp_f.flush()
            parsec_file = ParsecFile(Path(tmp_f.name))
            function = parsec_file.get_function_or_none(
                function_name=verification_result.get_function().name
            )
            if not function:
                msg = (
                    f"Function: {verification_result.get_function().name} "
                    "was missing from the file that failed to verify."
                )
                raise ValueError(msg)
            # TODO: Come up with a way to get the line numbers.
            function_lines_cbmc_commented_out = function.get_source_code().splitlines()
            function_lines = "\n".join(
                text_util.uncomment_cbmc_annotations(function_lines_cbmc_commented_out)
            )

        return PromptBuilder.NEXT_STEP_PROMPT_TEMPLATE.substitute(
            function_name=function.name,
            source_code=function_lines,
            callee_context=verification_result.verification_input.get_callee_context_for_prompt(),
            failure_information=verification_result.failure_messages,
        )

    def _get_callee_specs(self, caller: str, callees_with_specs: list[CFunction]) -> str:
        """Return the specifications of all the callees of `caller`.

        Args:
            caller (str): The calling function.
            callees_with_specs (list[CFunction]): The list of callees with specifications.

        Returns:
            str: The callee specifications to add to a prompt.
        """
        callee_context = "\n".join(callee.get_summary_for_prompt() for callee in callees_with_specs)
        return f"{caller} has the following callees:\n{callee_context}"
