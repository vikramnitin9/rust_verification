"""Class representing an input to a verifier (e.g., CBMC)."""

from dataclasses import dataclass

from util import FunctionSpecification, ParsecFunction


@dataclass(frozen=True)
class VerificationContext:
    callee_specs: dict[str, FunctionSpecification]
    # I'm unsure if CBMC has a way to write specs for global variables.
    global_variable_specs: dict[str, str]
    hints: str = ""


@dataclass(frozen=True)
class VerificationInput:
    function: ParsecFunction
    spec: FunctionSpecification
    context: VerificationContext
