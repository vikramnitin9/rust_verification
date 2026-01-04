"""Class representing an input to a verifier (e.g., CBMC)."""

from dataclasses import dataclass

from util import CFunction, FunctionSpecification


@dataclass(frozen=True)
class VerificationContext:
    """The context for a verification input.

    Attributes:
        callee_specs (dict[str, FunctionSpecification]): The specs for a function's callees.
        global_variable_specs (dict[str, str]): The specs for global program variables.
        hints (str): Hints given to the LLM for specification generation and repair.
            # MDE: I don't understand why the `hints` field exists in VerificationContext.
            # It is never used by a verifier, so it seems out of place and does not beling in
            # VerificationInput.  Furthermore, if it differs from one VerificationInput to another,
            # then even though the verifier behavior would be identical, it will suffer a cache miss
            # and cause recomputation (it will cause a real call to the verifier).
    """

    callee_specs: dict[CFunction, FunctionSpecification]
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

    Note: contents_of_file_to_verify is used instead of a path to the file that was verified because
    the file might not always exist. I.e., a temporary file is created during the verification
    process and is then deleted.

    Attributes:
        function (CFunction): The function to be verified.
        spec (FunctionSpecification): The spec for the function to be verified.
        context (VerificationContext): The context for the function to be verified.
        contents_of_file_to_verify (str): The contents of the file that contains `function`.
            # MDE: Is this content exactly as written by the programmer?  Or have all the
            # specifications from the context already been inserted?
    """

    function: CFunction
    spec: FunctionSpecification
    context: VerificationContext
    contents_of_file_to_verify: str

    def get_callees_to_specs(self) -> dict[CFunction, FunctionSpecification]:
        """Return a dictionary of callees to their specifications.

        Returns:
            dict[str, FunctionSpecification]: A dictionary of callees to their specifications.
        """
        return self.context.callee_specs

    def get_file_content(self) -> str:
        """Return the content of the file that is to be verified.

        Returns:
            str: The content of the file that is to be verified.
        """
        return self.contents_of_file_to_verify

    def get_callee_context_for_prompt(self) -> str:
        """Return the specifications of all the callees of this input's function.

        The context is a string in the format below:

        '{self.function}' has the following callees:
        Callee: ...
        Preconditions: ...
        Postconditions: ...

        Returns:
            str: The callee specifications formatted for a prompt.
        """
        callee_context_for_prompt = ""
        if callees_to_specs := self.get_callees_to_specs():
            callee_summaries = [
                f"Callee: {callee.name}\n{spec.get_prompt_str()}"
                for callee, spec in callees_to_specs.items()
            ]
            callee_context_for_prompt = (
                f"{self.function.name} has the following callees:\n" + "\n".join(callee_summaries)
            )
        return callee_context_for_prompt

    def __eq__(self, other: object) -> bool:
        """Return True iff this input is equal to another.

        Two verification inputs are equal iff they have the same function, specification, context,
        and if the content of the files they are verifying are equal.

        Args:
            other (object): An object to check equality for.

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
