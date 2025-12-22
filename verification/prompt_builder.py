"""Module to construct prompts for LLM calls."""

from pathlib import Path
from string import Template

from util import CFunction, ParsecFile

from .verification_result import VerificationResult


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

    def specification_generation_prompt(self, function: CFunction, parsec_file: ParsecFile) -> str:
        """Return the prompt used for specification generation.

        Args:
            function (CFunction): The function for which to generate specifications.
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

    def backtracking_prompt(self, verification_result: VerificationResult) -> str:
        """TODO: document me.

        Args:
            verification_result (VerificationResult): _description_

        Returns:
            str: _description_
        """
        function = verification_result.get_function()

        # There should be no difference between getting the function from the ParsecFile of the
        # verification input and the top-level function in the verification result, but there are
        # places in the code where one is updated (and not the other).
        # TODO: Ensure each CFunction is updated with the latest verification input file.
        if function_from_vinput := verification_result.get_parsec_file().get_function_or_none(
            function_name=function.name
        ):
            source_code = function_from_vinput.get_source_code(include_line_numbers=True)
        else:
            # Temporary fallback.
            source_code = function.get_source_code(include_line_numbers=True)
        callee_context_for_prompt = ""
        callees_to_specs = verification_result.verification_input.get_callee_names_to_specs()
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

    def _get_callee_specs(self, caller: str, callees_with_specs: list[CFunction]) -> str:
        """Return the callee specifications to add to a prompt.

        Args:
            caller (str): The caller function.
            callees_with_specs (list[CFunction]): The list of callees with specifications.

        Returns:
            str: The callee specifications to add to a prompt.
        """
        callee_context = "\n".join(callee.get_summary_for_prompt() for callee in callees_with_specs)
        return f"{caller} has the following callees:\n{callee_context}"
