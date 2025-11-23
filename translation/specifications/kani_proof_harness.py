"""Classes used to represent Kani proof harnesses."""

from dataclasses import dataclass

from util.rust import RustFunction

KANI_PROOF_ANNOS = ["#[cfg(kani)]", "#[kani::proof]"]


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

    _signature: str
    _nondet_variable_decls: str
    _annotations: list[str]
    _function_call: str

    def __init__(self, rust_candidate: RustFunction):
        self._annotations = list(KANI_PROOF_ANNOS)
        harness_function_name = f"check_{rust_candidate.name}"
        self._signature = f"fn {harness_function_name}()"
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
        return (
            f"{harness_annotations}\n{self._signature} {{\n    "
            f"{self._nondet_variable_decls}\n\n    "
            f"{self._function_call}\n}}"
        )
