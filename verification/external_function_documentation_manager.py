"""Class for managing documentation for external functions and constructs."""

import json
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Any


class EntityType(StrEnum):
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

    def __str__(self) -> str:
        """Return the string representation of a function parameter.

        Returns:
            str: The string representation of a function parameter.
        """
        if self.description:
            return f" Parameter @{self.name}: {self.description}"
        return f" @{self.name}"


@dataclass(frozen=True)
class ParsedDocumentation:
    """Represent structured documentation parsed from the C HTML documentation.

    Attributes:
        entity_type (EntityType): The type of the entity parsed from the HTML.
        header_file_basename (str): The base name (i.e., without directory part)
            of the header file in which this entity is declared.
        description (str): The description parsed from the HTML.
        parameters (list[FunctionParameter]): The documentation for the function parameters,
            empty for all entities except for functions.
        return_value_description (str): The description of the return value.
    """

    entity_type: EntityType
    header_file_basename: str
    description: str
    parameters: list[FunctionParameter]
    return_value_description: str

    def __str__(self) -> str:
        """Return the string representation of a parsed documentation entity.

        Returns:
            str: The string representation of a parsed documentation entity.
        """
        lines = [f" Description: {self.description}"]
        for param in self.parameters:
            lines = [*lines, str(param)]
        if self.return_value_description:
            lines = [*lines, f" @return: {self.return_value_description}"]
        return "\n".join(lines)


class ExternalFunctionDocumentationManager:
    """Class for managing and exposing documentation for external functions and constructs."""

    def __init__(self, path_to_documentation: str) -> None:
        """Create a new ExternalFunctionDocumentationManager."""
        self.docs = json.loads(Path(path_to_documentation).read_text(encoding="utf-8"))

    def get_documentation(self, function_name: str) -> ParsedDocumentation | None:
        """Return documentation for the function with the given name.

        Args:
            function_name (str): The function for which to return documentation.

        Returns:
            ParsedDocumentation | None: The documentation for the function with the given name.
        """
        if (
            docs_for_function := self.docs.get(function_name)
        ) and self._is_valid_parsed_documentation(docs_for_function):
            parameters = [FunctionParameter(**p) for p in docs_for_function["parameters"]]
            return ParsedDocumentation(
                docs_for_function["entity_type"],
                docs_for_function["header_file_basename"],
                description=docs_for_function["description"],
                parameters=parameters,
                return_value_description=docs_for_function["return_value_description"],
            )
        return None

    def get_header_declaring_function(self, function_name: str) -> str | None:
        """Return the base name of the header file in which the function with the name is declared.

        Args:
            function_name (str): The function for which to look up the header.

        Returns:
            str | None: The base name (i.e., without directory part) of the header file
                that declares the function, if found. Otherwise None.
        """
        if (
            doc_for_function := self.docs.get(function_name)
        ) and self._is_valid_parsed_documentation(doc_for_function):
            header = doc_for_function["header_file_basename"]
            return header if header != "" else None
        return None

    def _is_valid_parsed_documentation(self, parsed_documentation_json: dict[str, Any]) -> bool:
        """Return True iff the parsed documentation JSON has all fields in ParsedDocumentation.

        Args:
            parsed_documentation_json (dict[str, Any]): The parsed documentation JSON.

        Returns:
            bool: True iff the parsed documentation JSON has all fields in ParsedDocumentation.
        """
        return all(
            doc_field in parsed_documentation_json
            for doc_field in ParsedDocumentation.__annotations__
        )
