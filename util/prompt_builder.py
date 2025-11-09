"""Module to construct prompts for LLM calls."""

from pathlib import Path
from string import Template

from util import ParsecFunction, ParsecResult


class PromptBuilder:
    """Encapsulates functions used in constructing prompts for LLM calls."""

    PROMPT_FOR_SPECIFICATION_GENERATION = Path("./prompt.txt").read_text()
    SOURCE_PLACEHOLDER = "<<SOURCE>>"
    CALLEE_CONTEXT_PLACEHOLDER = "<<CALLEE_CONTEXT>>"

    REPAIR_PROMPT_TEMPLATE = Template(Path("./repair-prompt-template.txt").read_text())

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
        source_code = function.get_source_code()
        prompt = PromptBuilder.PROMPT_FOR_SPECIFICATION_GENERATION.replace(
            PromptBuilder.SOURCE_PLACEHOLDER, source_code
        )

        callee_context = ""
        if callees := parsec_result.get_callees(function):
            callees_with_specs = [callee for callee in callees if callee.is_specified()]
            if callees_with_specs:
                callee_context = self._get_callee_context_for_prompt(
                    function.name, callees_with_specs
                )

        return prompt.replace(PromptBuilder.CALLEE_CONTEXT_PLACEHOLDER, callee_context)

    def specification_repair_prompt(self, function: ParsecFunction, error_message: str) -> str:
        """Return a prompt directing the model to repair a faulty specification.

        Args:
            function (ParsecFunction): The function that does not verify.
            error_message (str): The error message from running a verifier on `function`.
                Only lines containing "FAILURE" are relevant.

        Returns:
            str: A prompt directing the model to repair a faulty specification.
        """
        lines_involving_failure = [line for line in error_message.splitlines() if "FAILURE" in line]
        return PromptBuilder.REPAIR_PROMPT_TEMPLATE.safe_substitute(
            function_name=function.name,
            failure_lines="\n".join(lines_involving_failure),
            stderr=error_message,
        )

    def _get_callee_context_for_prompt(
        self, caller: str, callees_with_specs: list[ParsecFunction]
    ) -> str:
        """Return the callee context to be added to a prompt.

        Args:
            caller (str): The caller function.
            callees_with_specs (list[ParsecFunction]): The list of callees with specifications.

        Returns:
            str: The callee context to be added to a prompt.
        """
        callee_context = "\n".join(str(callee) for callee in callees_with_specs)
        return f"{caller} has the following callees:\n{callee_context}"
