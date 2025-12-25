"""Class representing an input to a verifier (e.g., CBMC)."""

from dataclasses import dataclass

from util import CFunction, FunctionSpecification


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

    def __hash__(self) -> int:
        """Return the hash for this verification context.

        Returns:
            int: The hash for this verification context.
        """
        return hash(
            (
                frozenset(self.callee_specs.items()),
                frozenset(self.global_variable_specs.items()),
                self.hints,
            )
        )


@dataclass(frozen=True)
class VerificationInput:
    """The input to a verifier.

    Attributes:
        function (CFunction): The function to be verified.
        spec (FunctionSpecification): The spec for the function to be verified.
        context (VerificationContext): The context for the function to be verified.
        contents_of_file_to_verify (str): The contents of the file to be verified.
    """

    function: CFunction
    spec: FunctionSpecification
    context: VerificationContext
    contents_of_file_to_verify: str

    def get_callee_names_to_specs(self) -> dict[str, FunctionSpecification]:
        """Return a dictionary of callee names to their specifications.

        Returns:
            dict[str, FunctionSpecification]: A dictionary of callee names to their specifications.
        """
        return self.context.callee_specs

    def get_file_content(self) -> str:
        """Return the content of the file that is to be verified.

        Returns:
            str: The content of the file that is to be verified.
        """
        return self.contents_of_file_to_verify

    def __eq__(self, other) -> bool:
        """Return True iff this input is equal to another.

        Two verification inputs are equal iff they have the same function, specification, context,
        and if the content of the files they are verifying are equal.

        Args:
            other (Any): An object to check equality for.

        Returns:
            bool: True iff this input is equal to another.
        """
        if not isinstance(other, VerificationInput):
            return False
        return (
            self.function == other.function
            and self.spec == other.spec
            and self.context == other.context
            and self.get_file_content() == other.get_file_content()
        )

    def __hash__(self) -> int:
        """Return the hash for this verification input.

        Returns:
            int: The hash for this verification input.
        """
        file_content = self.get_file_content()
        return hash((self.function, self.spec, file_content, self.context))
