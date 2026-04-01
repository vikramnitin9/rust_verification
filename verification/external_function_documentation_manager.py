"""Class for managing documentation for external functions and constructs."""

import json
from dataclasses import dataclass
from enum import Enum
from pathlib import Path


class EntityType(str, Enum):
    """Represent the type of entity in the C documentation."""

    FUNCTION = "function"
    MACRO = "macro"
    TYPE = "type"
    OTHER = "other"


@dataclass(frozen=True)
class FunctionParameter:
    """Represent a function parameter in the C documentation.

    Attributes:
        name (str): The parameter name.
        description (str): The description of the parameter.
    """

    name: str
    description: str


@dataclass(frozen=True)
class ParsedDocumentation:
    """Represent structured documentation parsed from the C HTML documentation.

    Attributes:
        entity_type (EntityType): The type of the entity parsed from the HTML.
        description (str): The description parsed from the HTML.
        parameters (list[FunctionParameter]): The documentation for the function parameters,
            empty for all entities except for functions.
        return_value_description (str): The description of the return value.
    """

    entity_type: EntityType
    description: str
    parameters: list[FunctionParameter]
    return_value_description: str


class ExternalFunctionDocumentationManager:
    """Class for managing and exposing documentation for external functions and constructs."""

    def __init__(self, path_to_documentation) -> None:
        """Create a new ExternalFunctionDocumentationManager."""
        self.docs = json.loads(Path(path_to_documentation).read_text(encoding="utf-8"))

    def get_documentation(self, function_name: str) -> ParsedDocumentation | None:
        """Return documentation for the function with the given name.

        Args:
            function_name (str): The function for which to return documentation.

        Returns:
            ParsedDocumentation | None: The documentation for the function with the given name.
        """
        if docs_for_function := self.docs.get(function_name):
            parameters = [FunctionParameter(**p) for p in docs_for_function["parameters"]]
            return ParsedDocumentation(
                docs_for_function["entity_type"],
                description=docs_for_function["description"],
                parameters=parameters,
                return_value_description=docs_for_function["return_value_description"],
            )
        return None
