"""Module to encapsulate inputs to verifiers."""

from dataclasses import dataclass
from pathlib import Path

from util import ParsecResult


@dataclass
class VerificationContext:
    name_of_function_to_verify: str
    src_of_function_to_verify: str
    parsec_analysis: ParsecResult
    names_of_verified_functions: set[str]
    path_to_src: Path
