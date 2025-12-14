"""Class representing an input to a verifier (e.g., CBMC)."""

from dataclasses import dataclass

from util import FunctionSpecification, ParsecFunction


@dataclass(frozen=True)
class VerificationContext:
    """The context for a verification input.

    Attributes:
        callee_specs (dict[str, FunctionSpecification]): The specs for a function's callees.
        global_variable_specs (dict[str, str]): The specs for global program variables.
        hints (str): Hints given to the verifier for specification generation.
    """

    callee_specs: dict[str, FunctionSpecification]
    # I'm unsure if CBMC has a way to write specs for global variables.
    global_variable_specs: dict[str, str]
    hints: str = ""


@dataclass(frozen=True)
class VerificationInput:
    """The input to a verifier.

    Attributes:
        function (ParsecFunction): The function to be verified.
        spec (FunctionSpecification): The spec for the function to be verified.
        context (VerificationContext): The context for the function to be verified.
    """

    function: ParsecFunction
    spec: FunctionSpecification
    context: VerificationContext
