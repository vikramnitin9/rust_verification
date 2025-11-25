"""Classes used to represent Kani proof harnesses."""

from dataclasses import dataclass
from string import Template

from util import FunctionSpecification
from util.rust import RustFunction

KANI_PROOF_ANNOS = ["#[cfg(kani)]", "#[kani::proof]"]

KANI_PROOF_HARNESS_TEMPLATE = Template("""$harness_annotations
fn check_$function_name() {
    $variable_declarations

    if ($assumed_expressions) {
        $function_call
    }
}""")


@dataclass
class KaniProofHarness:
    """Represents a Kani proof harness.

    A Kani proof harness is a single function acting as the entry point for verification.
    It comprises a call to the function under verification, and a set of assumptions
    (if applicable).

    Attributes:
        _signature (str): The signature of this harness.
        _nondet_variable_decls (str): The non-deterministic variable declarations in this harness.
        _annotations (list[str]): The annotations of this harness.
        _function_call (str): The call to the function being verified with this harness.
    """

    _rust_candidate: RustFunction
    _nondet_variable_decls: str
    _annotations: list[str]
    _assumed_exprs: list[str]
    _function_call: str

    def __init__(self, rust_candidate: RustFunction, spec: FunctionSpecification):
        self._rust_candidate = rust_candidate
        self._annotations = list(KANI_PROOF_ANNOS)
        self._assumed_exprs = [
            self._get_expression_in_precondition(pre) for pre in spec.preconditions
        ]
        self._nondet_variable_decls = "\n    ".join(
            type_wrapper.declaration(name, val="kani::any();")
            for name, type_wrapper in rust_candidate.param_to_type.items()
        )
        argument_list = ", ".join(
            type_wrapper.to_argument(param_name)
            for param_name, type_wrapper in rust_candidate.param_to_type.items()
        )
        self._function_call = f"{rust_candidate.name}({argument_list})"

    def __str__(self) -> str:
        """Return the source code representation of this proof harness.

        Returns:
            str: The source code representation of this proof harness.
        """
        harness_annotations = "\n".join(self._annotations)
        return KANI_PROOF_HARNESS_TEMPLATE.substitute(
            harness_annotations=harness_annotations,
            function_name=self._rust_candidate.name,
            variable_declarations=self._nondet_variable_decls,
            assumed_expressions=" && ".join(self._assumed_exprs) if self._assumed_exprs else "true",
            function_call=self._function_call,
        )

    def _get_expression_in_precondition(self, precondition: str) -> str:
        """Return the expression in the Kani precondition annotation.

        In more detail, given a Kani precondition, e.g.,

            kani::requires(<EXPR>)

        Return just the <EXPR> part.

        Args:
            precondition (str): The Kani precondition.

        Raises:
            RuntimeError: Raised when matching the expression in the precondition fails.

        Returns:
            str: The expression in the Kani precondition annotation.
        """
        precondition_prefix = "kani::requires"
        if precondition_prefix not in precondition:
            msg = f"Failed to parse precondition expression in: {precondition}"
            raise RuntimeError(msg)
        expr_wrapped_in_parens = precondition[len(precondition_prefix) :].strip()

        paren_count = 0
        expr_start_index = None
        for i, char in enumerate(expr_wrapped_in_parens):
            if char == "(":
                if paren_count == 0:
                    expr_start_index = i + 1
                paren_count += 1
            elif char == ")":
                paren_count -= 1
                if paren_count == 0:
                    return expr_wrapped_in_parens[expr_start_index:i]

        msg = f"Failed to parse precondition expression in: {precondition}"
        raise RuntimeError(msg)
