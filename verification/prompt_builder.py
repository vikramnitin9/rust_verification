"""Module to construct prompts for LLM calls."""

from pathlib import Path
from string import Template

from util import ParsecFile, ParsecFunction

from .verification_result import Failure, VerificationResult


class PromptBuilder:
    """Encapsulates functions used in constructing prompts for LLM calls."""

    SPECIFICATION_GENERATION_PROMPT_TEMPLATE = Path(
        "./prompts/generate-specifications-prompt-template.txt"
    ).read_text()
    SPECIFICATION_REPAIR_PROMPT_TEMPLATE = Template(
        Path("./prompts/repair-specifications-prompt-template.txt").read_text()
    )
    BACKTRACKING_PROMPT_TEMPLATE = Template(Path("./prompts/backtracking-prompt.txt").read_text())
    SOURCE_PLACEHOLDER = "<<SOURCE>>"
    CALLEE_CONTEXT_PLACEHOLDER = "<<CALLEE_CONTEXT>>"

    def specification_generation_prompt(
        self, function: ParsecFunction, parsec_file: ParsecFile
    ) -> str:
        """Return the prompt used for specification generation.

        Args:
            function (ParsecFunction): The function for which to generate specifications.
            parsec_file (ParsecFile): The top-level ParseC file.

        Returns:
            str: The initial used for specification generation.
        """
        source_code = function.get_source_code(include_documentation_comments=True)
        prompt = PromptBuilder.SPECIFICATION_GENERATION_PROMPT_TEMPLATE.replace(
            PromptBuilder.SOURCE_PLACEHOLDER, source_code
        )

        callee_context = ""
        if callees := parsec_file.get_callees(function):
            callees_with_specs = [callee for callee in callees if callee.has_specification()]
            if callees_with_specs:
                callee_context = self._get_callee_specs(function.name, callees_with_specs)

        return prompt.replace(PromptBuilder.CALLEE_CONTEXT_PLACEHOLDER, callee_context)

    def specification_repair_prompt(self, function_name: str, verification_failure: Failure) -> str:
        """Return a prompt directing the model to repair a faulty specification.

        Args:
            function_name (str): The name of the function that does not verify.
            verification_failure (Failure): The failed result of verifying the function.

        Returns:
            str: A prompt directing the model to repair a faulty specification.
        """
        parsec_file_for_candidate_file = ParsecFile.parse_source_with_cbmc_annotations(
            verification_failure.source
        )
        function = parsec_file_for_candidate_file.get_function(function_name)
        lines_involving_failure = [
            line for line in verification_failure.stdout.splitlines() if "FAILURE" in line
        ]
        candidate_function_source_code = function.get_source_code(
            include_documentation_comments=True,
            include_line_numbers=True,
            should_uncomment_cbmc_annotations=True,
        )
        parsec_file_for_candidate_file.file_path.unlink()
        return PromptBuilder.SPECIFICATION_REPAIR_PROMPT_TEMPLATE.safe_substitute(
            function_name=function.name,
            function_implementation=candidate_function_source_code,
            failure_lines="\n".join(lines_involving_failure),
            stderr=verification_failure.stderr,
        )

    def backtracking_prompt(self, verification_result: VerificationResult) -> str:
        function = verification_result.get_function()
        source_code = function.get_source_code(include_line_numbers=True)
        callee_context_for_prompt = ""
        callees_to_specs = verification_result._input.get_callee_names_to_specs()
        if callees_to_specs:
            callee_summaries = [
                f"Callee: {name}\n{spec.get_prompt_str()}"
                for name, spec in callees_to_specs.items()
            ]
            callee_context_for_prompt = f"{function.name} has the following callees:" + "\n".join(
                callee_summaries
            )

        return PromptBuilder.BACKTRACKING_PROMPT_TEMPLATE.substitute(
            function_name=function.name,
            source_code=source_code,
            callee_context=callee_context_for_prompt if callee_context_for_prompt != "" else "",
            failure_information=verification_result.failure_messages,
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
