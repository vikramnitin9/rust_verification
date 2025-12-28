"""Module to construct prompts for LLM calls."""

import tempfile
from pathlib import Path
from string import Template

from util import CFunction, ParsecFile, text_util

from .verification_result import VerificationResult


class PromptBuilder:
    """Encapsulates functions used in constructing prompts for LLM calls."""

    # MDE: Does this class represent something?  If it's just a collection of functions, I would not
    # use the term "encapsulate" above.

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

        The prompt consists of the C function and the "context", which is the specifications of its
        callees.

        Args:
            function (CFunction): The function for which to generate specifications.
            parsec_file (ParsecFile): The top-level ParseC file.
                # MDE: As elsewhere, perhaps the ParsecFile can be a field of the CFunction.

        Returns:
            str: The initial used for specification generation.
                # MDE: noun missing above.  "prompt"?

        """
        source_code = function.get_source_code(include_documentation_comments=True)
        prompt = PromptBuilder.SPECIFICATION_GENERATION_PROMPT_TEMPLATE.replace(
            PromptBuilder.SOURCE_PLACEHOLDER, source_code
        )

        callee_context = ""
        if callees := parsec_file.get_callees(function):
            if callees_with_specs := [callee for callee in callees if callee.has_specification()]:
                callee_context = self._get_callee_specs(function.name, callees_with_specs)

        return prompt.replace(PromptBuilder.CALLEE_CONTEXT_PLACEHOLDER, callee_context)

    def backtracking_prompt(self, verification_result: VerificationResult) -> str:
        """Return prompt text indicating the need to backtrack during verification.

        Args:
            verification_result (VerificationResult): _description_

        Returns:
            str: Prompt text indicating the need to backtrack during verification.
        """
        with tempfile.NamedTemporaryFile(mode="w+t", suffix=".c") as tmp_f:
            # The following might have CBMC annotations, comment them out.
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
            function_lines_cbmc_commented_out = function.get_source_code(
                include_line_numbers=True
            ).splitlines()
            function_lines = "\n".join(
                text_util.uncomment_cbmc_annotations(function_lines_cbmc_commented_out)
            )

        callee_context_for_prompt = ""
        callees_to_specs = verification_result.verification_input.get_callee_names_to_specs()
        if callees_to_specs:
            callee_summaries = [
                f"Callee: {name}\n{spec.get_prompt_str()}"
                for name, spec in callees_to_specs.items()
            ]
            callee_context_for_prompt = f"{function.name} has the following callees:\n" + "\n".join(
                callee_summaries
            )

        return PromptBuilder.BACKTRACKING_PROMPT_TEMPLATE.substitute(
            function_name=function.name,
            source_code=function_lines,
            callee_context=callee_context_for_prompt,
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
