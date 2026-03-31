"""Class for managing documentation for external functions and constructs."""

import json
from pathlib import Path


class ExternalFunctionDocumentationManager:
    """Class for managing and exposing documentation for external functions and constructs."""

    def __init__(self, path_to_documentation) -> None:
        """Create a new ExternalFunctionDocumentationManager."""
        self.docs = json.loads(Path(path_to_documentation).read_text(encoding="utf-8"))
