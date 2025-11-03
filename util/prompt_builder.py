"""Module to construct prompts for LLM calls."""

from pathlib import Path
from string import Template
from subprocess import CompletedProcess

from util import ParsecFunction, ParsecResult


class PromptBuilder:
    """Encapsulates functions used in constructing prompts for LLM calls."""

    INITIAL_PROMPT_FOR_SPECIFICATION_GENERATION = Path("./prompt.txt").read_text()
    SOURCE_DELIMITER = "<<SOURCE>>"
    CALLEE_CONTEXT_DELIMITER = "<<CALLEE_CONTEXT>>"

    REPAIR_PROMPT_TEMPLATE = Template(
        "Error while running verification for function $function_name:\n"
        "STDOUT: $failure_lines\n"
        "STDERR: $stderr\n"
        "Please fix the error and re-generate the function with specifications."
    )

    def build_initial_specification_generation_prompt(
        self, function: ParsecFunction, parsec_result: ParsecResult
    ) -> str:
        """Return the initial prompt used for specification generation.

        Args:
            function (ParsecFunction): The function for which to generate specifications.
            parsec_result (ParsecResult): The top-level ParseC result.

        Returns:
            str: The initial prompt used for specification generation.
        """
        source_code = function.get_source_code()
        prompt = PromptBuilder.INITIAL_PROMPT_FOR_SPECIFICATION_GENERATION.replace(
            PromptBuilder.SOURCE_DELIMITER, source_code
        )

        callee_context = ""
        if callees := parsec_result.get_callees(function):
            callees_with_specs = filter(ParsecFunction.is_specified, callees)
            if callees_with_specs:
                callee_context = self._get_callee_context_for_prompt(
                    function.name, callees_with_specs
                )

        return prompt.replace(PromptBuilder.CALLEE_CONTEXT_DELIMITER, callee_context)

    def build_repair_specification_prompt(
        self, function: ParsecFunction, verification_result: CompletedProcess[str]
    ) -> str:
        """Return a prompt directing the model to repair a faulty specification.

        Args:
            function (ParsecFunction): The function that is failing to verify.
            verification_result (CompletedProcess[str]): The result of running a verifier on the
                function.

        Returns:
            str: A prompt directing the model to repair a faulty specification.
        """
        lines_involving_failure = [
            line for line in verification_result.stdout.splitlines() if "FAILURE" in line
        ]
        return PromptBuilder.REPAIR_PROMPT_TEMPLATE.safe_substitute(
            function_name=function.name,
            failure_lines="\n".join(lines_involving_failure),
            stderr=verification_result.stderr,
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
