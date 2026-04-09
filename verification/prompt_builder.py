"""Module to construct prompts for LLM calls."""

import tempfile
from collections import defaultdict
from pathlib import Path
from string import Template

from loguru import logger

from util import CFunction, CFunctionGraph, FunctionSpecification, SpecGenGranularity, text_util

from .avocado_stub_util import get_stub_implementation_from_parsed_source, load_stub_file
from .external_function_documentation_manager import ExternalFunctionDocumentationManager
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

    # Implementation generation prompt template.
    GENERATE_IMPLEMENTATION_PROMPT_TEMPLATE = Template(
        Path("./prompts/generate-implementation-prompt-template.txt").read_text(encoding="utf-8")
    )

    CBMC_OUTPUT_FAILURE_MARKER = "FAILURE"

    def __init__(
        self, external_function_documentation_manager: ExternalFunctionDocumentationManager
    ) -> None:
        """Create a new PromptBuilder."""
        self._external_function_documentation_manager = external_function_documentation_manager

    def specification_generation_prompt(
        self,
        function: CFunction,
        function_graph: CFunctionGraph,
        specgen_granularity: SpecGenGranularity,
    ) -> str:
        """Return the prompt used for specification generation.

        The prompt consists of the C function and the "context", which is the specifications of its
        callees.

        Args:
            function (CFunction): The function for which to generate specifications.
            function_graph (CFunctionGraph): The function graph that contains `function`.
            specgen_granularity (SpecGenGranularity): The granularity at which specification
                generation occurs.

        Returns:
            str: The initial prompt used for specification generation.

        """
        source_code = function.get_original_source_code(include_documentation_comments=True)
        callee_context = self._get_callee_context(function_graph, function)

        template = self._get_generation_prompt_template(specgen_granularity)
        return template.substitute(source=source_code, callee_context=callee_context)

    def _get_callee_context(self, function_graph: CFunctionGraph, function: CFunction) -> str:
        """Return the callee context for the given function.

        The callee context for each function comprises:

            1. The CBMC function contracts for a callee in the project.
            2. The entire implementation/stub for a callee that is not in the project.

        (2) Is due to the fact that not all external callees have CBMC function contracts, but may
        have CBMC annotations directly written in their implementation (see verification/cbmc_stub).

        Arguments:
            function_graph (CFunctionGraph): The function graph from which the function originates.
            function (CFunction): The function for which to obtain the callee context.

        Returns:
            str: The callee context for the given function.
        """
        project_callee_context = ""
        callees_in_project = function_graph.get_callees(function)
        project_callee_context = self._get_project_callee_context(
            function.name,
            [
                project_callee
                for project_callee in callees_in_project
                if project_callee.has_specification()
            ],
        )

        names_of_callees_in_project = [project_callee.name for project_callee in callees_in_project]
        names_of_external_callees = [
            callee_name
            for callee_name in function.callee_names
            if callee_name not in names_of_callees_in_project
        ]
        external_callee_context = self._get_external_callee_context(
            function.name, names_of_external_callees
        )

        return "\n\n\n".join(
            context for context in (project_callee_context, external_callee_context) if context
        )

    def _get_external_callee_context(
        self, caller_name: str, external_callee_names: list[str]
    ) -> str | None:
        """Return prompt context describing external callees and their stub implementations.

        Not all external functions (see the CBMC stub functions for the ANSI-C library in
        verification/cbmc_stubs for an example) have CBMC function contracts. However, their
        implementations (i.e., their bodies) include CBMC annotations, which we include in the
        context.

        If a header has no stub file or a specific callee has no matching stub implementation,
        a warning is logged and that callee is omitted from the context.

        Args:
            caller_name (str): Name of the function whose external callees are being summarized.
            external_callee_names (list[str]): External callee names.

        Returns:
            str | None: Formatted context text for the prompt when at least one external callee
                stub implementation is found; otherwise None.
        """
        # This maps header base names (e.g., string.h)  to the callees of a given function.
        # it is not a complete mapping (i.e., the mapped value for string.h does not include all
        # the functions it declares, only the ones that are called by the function for which
        # specifications are being generated).
        header_basename_to_external_callee_names: dict[str, list[str]] = defaultdict(list)
        for callee_name in external_callee_names:
            if (
                header_file_basename
                := self._external_function_documentation_manager.get_header_declaring_function(
                    callee_name
                )
            ):
                header_basename_to_external_callee_names[header_file_basename].append(callee_name)

        external_callees_to_stubs: dict[str, str] = {}
        for (
            header_file_basename,
            callee_names_for_header,
        ) in header_basename_to_external_callee_names.items():
            parsed_source = load_stub_file(header_file_basename)
            if parsed_source is None:
                for callee_name in callee_names_for_header:
                    logger.warning(f"Didn't find {callee_name} in file {header_file_basename}")
                continue
            for callee_name in callee_names_for_header:
                if callee_stub_impl := get_stub_implementation_from_parsed_source(
                    callee_name, parsed_source
                ):
                    external_callees_to_stubs[callee_name] = callee_stub_impl
                else:
                    logger.warning(f"Didn't find {callee_name} in file {header_file_basename}")

        if not external_callees_to_stubs:
            return None

        external_callee_context = f"{caller_name} calls the following functions:\n\n"
        external_callee_stub_strs = [
            f"External callee: {external_callee}\n\n{stub_impl}"
            for external_callee, stub_impl in external_callees_to_stubs.items()
        ]

        return external_callee_context + "\n\n\n".join(external_callee_stub_strs)

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
            function_graph = CFunctionGraph(Path(tmp_f.name))
            function = function_graph.get_function_or_none(
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
            failure_information=text_util.normalize_cbmc_output_paths(
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
            function_graph = CFunctionGraph(Path(tmp_f.name))
            function = function_graph.get_function_or_none(
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

    def generate_implementation_prompt(
        self,
        signature: str,
        specification: FunctionSpecification,
    ) -> str:
        """Return the prompt used to generate a C function implementation.

        Args:
            signature (str): The signature for the C function to implement
                (e.g., int add(int a, int b))
            specification (FunctionSpecification): The CBMC pre- and postconditions the
                implementation must satisfy.

        Returns:
            str: The prompt asking the LLM to produce a matching implementation.
        """
        return PromptBuilder.GENERATE_IMPLEMENTATION_PROMPT_TEMPLATE.substitute(
            signature=signature.strip(),
            specification=specification.get_prompt_str(),
        )

    def _get_project_callee_context(
        self, caller: str, callees_with_specs: list[CFunction]
    ) -> str | None:
        """Return the specifications of all the callees of `caller`.

        Args:
            caller (str): The calling function.
            callees_with_specs (list[CFunction]): The list of callees with specifications.

        Returns:
            str | None: The callee specifications to add to a prompt.
        """
        if not callees_with_specs:
            return None
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
