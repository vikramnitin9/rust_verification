"""Module to construct prompts for LLM calls."""

import re
import tempfile
from pathlib import Path
from string import Template

from util import CFunction, ParsecFile, SpecGenGranularity, text_util

from .verification_result import VerificationResult


class PromptBuilder:
    """A collection of functions used in constructing prompts for LLM calls."""

    # Specification generation/repair prompts for clause-level generation.
    CLAUSE_LEVEL_SPECIFICATION_GENERATION_PROMPT_TEMPLATE = Template(
        Path("./prompts/generate-specifications-prompt-template.txt").read_text()
    )
    CLAUSE_LEVEL_SPECIFICATION_REPAIR_PROMPT_TEMPLATE = Template(
        Path("./prompts/repair-specifications-prompt-template.txt").read_text()
    )

    # Specification generation/repair prompts for expression-level generation.
    EXPRESSION_LEVEL_SPECIFICATION_GENERATION_PROMPT_TEMPLATE = Template(
        Path("./prompts/generate-specifications-prompt-with-expressions-template.txt").read_text()
    )
    EXPRESSION_LEVEL_SPECIFICATION_REPAIR_PROMPT_TEMPLATE = Template(
        Path("./prompts/repair-specifications-prompt-with-expressions-template.txt").read_text()
    )

    NEXT_STEP_PROMPT_TEMPLATE = Template(
        Path("./prompts/next-step-prompt-template.txt").read_text()
    )
    CBMC_OUTPUT_FAILURE_MARKER = "FAILURE"

    def specification_generation_prompt(
        self, function: CFunction, specgen_granularity: SpecGenGranularity, parsec_file: ParsecFile
    ) -> str:
        """Return the prompt used for specification generation.

        The prompt consists of the C function and the "context", which is the specifications of its
        callees.

        Args:
            function (CFunction): The function for which to generate specifications.
            specgen_granularity (SpecGenGranularity): The granularity at which specification
                generation occurs.
            parsec_file (ParsecFile): The file that contains `function`.


        Returns:
            str: The initial prompt used for specification generation.

        """
        source_code = function.get_original_source_code(include_documentation_comments=True)
        callee_context = ""
        if callees := parsec_file.get_callees(function):
            if callees_with_specs := [callee for callee in callees if callee.has_specification()]:
                callee_context = self._get_callee_specs(function.name, callees_with_specs)

        template = self._get_generation_prompt_template(specgen_granularity)
        return template.substitute(source=source_code, callee_context=callee_context)

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
            function_lines = source_code_lines[function.start_line - 1 : function.end_line]
            number_with_function_lines = text_util.prepend_line_numbers(
                function_lines, start=function.start_line, end=function.end_line
            )
            function_lines = "\n".join(
                f"{line}: {content}" for line, content in number_with_function_lines
            )

        return PromptBuilder.NEXT_STEP_PROMPT_TEMPLATE.substitute(
            function_name=function.name,
            source_code=function_lines,
            callee_context=verification_result.verification_input.get_callee_context_for_prompt(),
            failure_information=PromptBuilder._normalize_cbmc_output(
                verification_result.stdout + "\n" + verification_result.stderr,
                verification_result.get_function().name,
            ),
        )

    def repair_prompt(
        self, verification_result: VerificationResult, specgen_granularity: SpecGenGranularity
    ) -> str:
        """Return the prompt used in iteratively repairing a specification.

        Args:
            verification_result (VerificationResult): The verification result with failure
                information.
            specgen_granularity (SpecGenGranularity): The granularity at which specification
                generation occurs.

        Returns:
            str: The prompt used in iteratively repairing a specification.
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
            source_code_with_line_numbers = text_util.prepend_line_numbers(
                lines=source_code_lines, start=1, end=len(source_code_lines)
            )
            template = self._get_repair_prompt_template(specgen_granularity)
            return template.substitute(
                function_name=function.name,
                errors="\n".join(
                    line
                    for line in verification_result.stdout.splitlines()
                    if line.endswith(PromptBuilder.CBMC_OUTPUT_FAILURE_MARKER)
                ),
                function_implementation="\n".join(
                    f"{line}: {content}" for line, content in source_code_with_line_numbers
                ),
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

    def _get_generation_prompt_template(self, specgen_granularity: SpecGenGranularity) -> Template:
        """Return the specification generation template for the given granularity.

        Args:
            specgen_granularity (SpecGenGranularity): The specification generation granularity.

        Returns:
            Template: The specification generation template for the given granularity.
        """
        match specgen_granularity:
            case SpecGenGranularity.CLAUSE:
                return PromptBuilder.CLAUSE_LEVEL_SPECIFICATION_GENERATION_PROMPT_TEMPLATE
            case SpecGenGranularity.EXPRESSION:
                return PromptBuilder.EXPRESSION_LEVEL_SPECIFICATION_GENERATION_PROMPT_TEMPLATE
            case _:
                msg = (
                    "Unsupported specification generation/repair granularity: "
                    f"{specgen_granularity}"
                )
                raise ValueError(msg)

    def _get_repair_prompt_template(self, specgen_granularity: SpecGenGranularity) -> Template:
        """Return the specification repair template for the given granularity.

        Args:
            specgen_granularity (SpecGenGranularity): The specification repair granularity.

        Returns:
            Template: The specification repair template for the given granularity.
        """
        match specgen_granularity:
            case SpecGenGranularity.CLAUSE:
                return PromptBuilder.CLAUSE_LEVEL_SPECIFICATION_REPAIR_PROMPT_TEMPLATE
            case SpecGenGranularity.EXPRESSION:
                return PromptBuilder.EXPRESSION_LEVEL_SPECIFICATION_REPAIR_PROMPT_TEMPLATE
            case _:
                msg = (
                    "Unsupported specification generation/repair granularity: "
                    f"{specgen_granularity}"
                )
                raise ValueError(msg)

    @staticmethod
    def _normalize_cbmc_output(output: str, function_name: str) -> str:
        """Return CBMC output with temp file paths replaced by a stable name.

        CBMC error output includes the path to the temporary file that was compiled
        (e.g., '/app/specs/get_min_maxABC123.c'). These random paths make LLM cache
        keys non-deterministic. This method replaces any such path with a stable name
        (e.g., 'get_min_max.c') so that prompts are reproducible across runs.

        Args:
            output (str): The raw CBMC stdout or stderr output.
            function_name (str): The name of the function being verified.

        Returns:
            str: The CBMC output with temp file paths replaced by '{function_name}.c'.
        """
        stable_name = f"{function_name}.c"
        return re.sub(
            r"\S*" + re.escape(function_name) + r"[a-zA-Z0-9_-]+\.c",
            stable_name,
            output,
        )
