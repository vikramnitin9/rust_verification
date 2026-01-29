"""Utility functions for extracting source code from text."""

from loguru import logger

from .function_specification import FunctionSpecification
from .json_util import parse_object


def extract_function_source_code(text: str) -> str:
    """Extract the source code part of an LLM response.

    An LLM is prompted to return a string in the following JSON format:

        { "function_with_specs": "<SOURCE CODE>" }

    This function extracts the <SOURCE CODE> part.

    Args:
        text (str): The full response from an LLM, in JSON format.

    Returns:
        str: The source code part of an LLM response.
    """
    llm_response = parse_object(text)
    if function := llm_response.get("function_with_specs"):
        return function
    msg = f"The LLM returned valid JSON, but was missing the 'function_with_specs' key: {text}"
    raise RuntimeError(msg)


def parse_specs(text: str) -> FunctionSpecification | None:
    """Parse the specifications in an LLM response.

    An LLM is prompted to return a string in the following JSON format:

        {
            "preconditions": [...],
            "postconditions": [...]
        }

    This function attempts to create an instance of FunctionSpecification with the pre and
    postconditions in the response.

    Args:
        text (str): The full response from an LLM.

    Returns:
        FunctionSpecification | None: The FunctionSpecification comprising the pre and
            postconditions parsed from an LLM response.
    """
    llm_response = parse_object(text)
    preconditions = llm_response.get("preconditions")
    postconditions = llm_response.get("postconditions")

    if preconditions is None or postconditions is None:
        logger.warning(
            "The LLM returned valid JSON, but it was missing the 'preconditions' and/or "
            "'postconditions' key"
        )
        return None

    if not isinstance(preconditions, list) or not all(
        isinstance(item, str) for item in preconditions
    ):
        logger.warning(f"'{preconditions}' did not have the expected type: list[str]")
        return None
    if not isinstance(postconditions, list) or not all(
        isinstance(item, str) for item in postconditions
    ):
        logger.warning(f"'{postconditions}' did not have the expected type: list[str]")
        return None
    if len(preconditions) == 0 and len(postconditions) == 0:
        return None
    return FunctionSpecification(preconditions, postconditions)


def parse_expressions_for_spec(text: str) -> FunctionSpecification | None:
    """Parse the specifications in an LLM response.

    An LLM is prompted to return a string in the following JSON format:

        {
            "precondition_expressions": [...],
            "postcondition_expressions": [...],
            "assigned_variables": []
        }

    This function attempts to create an instance of FunctionSpecification with pre and
        postconditions constructed from the expressions in the response.

    Args:
        text (str): The full response from an LLM.

    Returns:
        FunctionSpecification | None: The FunctionSpecification comprising the pre and
            postconditions parsed from an LLM response.
    """
    llm_response = parse_object(text)
    precondition_exprs = llm_response.get("precondition_expressions")
    postcondition_exprs = llm_response.get("postcondition_expressions")
    assigned_variables = llm_response.get("assigned_variables")

    if precondition_exprs is None or postcondition_exprs is None or assigned_variables is None:
        logger.warning(
            "The LLM returned valid JSON, but it was missing the 'precondition_expressions' and/or "
            "'postcondition_expressions' and/or 'assigned_variables' key"
        )
        return None

    if not isinstance(precondition_exprs, list) or not all(
        isinstance(item, str) for item in precondition_exprs
    ):
        logger.warning(f"'{precondition_exprs}' did not have the expected type: list[str]")
        return None
    if not isinstance(postcondition_exprs, list) or not all(
        isinstance(item, str) for item in postcondition_exprs
    ):
        logger.warning(f"'{postcondition_exprs}' did not have the expected type: list[str]")
        return None
    if len(precondition_exprs) == 0 and len(postcondition_exprs) == 0:
        return None
    preconditions = [f"__CPROVER_requires({expr})" for expr in precondition_exprs]
    postconditions = [f"__CPROVER_ensures({expr})" for expr in precondition_exprs]
    if assigned_variables and all(isinstance(var_name, str) for var_name in assigned_variables):
        assigns_targets = [
            var_name if var_name.startswith("*") else f"*{var_name}"
            for var_name in assigned_variables
        ]
        assigns_clause = f"__CPROVER_assigns({','.join(assigns_targets)})"
        postconditions = [*postconditions, assigns_clause]
    return FunctionSpecification(preconditions, postconditions)
