"""Client for verifying source code."""

from pathlib import Path
from typing import Protocol
from .verification_result import Success, Failure


class VerificationClient(Protocol):
    """Client for verifying source code."""

    def verify(
        self,
        function_name: str,
        names_of_verified_functions: list[str],
        names_of_trusted_functions: list[str],
        file_path: Path,
    ) -> Success | Failure: ...
