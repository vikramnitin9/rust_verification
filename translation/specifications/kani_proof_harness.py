"""Classes used to represent Kani proof harnesses."""

from dataclasses import dataclass

from util import ParsecFunction

KANI_PROOF_ANNOS = ["#[cfg(kani)]", "#[kani::proof]"]


@dataclass
class RustTypeWrapper:
    """Lightweight representation of a Rust type.

    Attributes:
        rust_type (str): Represents the base Rust type (e.g., i32)
        is_mutable_reference (bool): True iff the type is a mutable reference
    """

    rust_type: str
    is_mutable_reference: bool

    def __init__(self, rust_type: str, is_mutable_reference: bool = False):
        self.rust_type = rust_type
        self.is_mutable_reference = is_mutable_reference

    def declaration(self, variable_name: str, val: str) -> str:
        """Return a declaration (an inhabitant) for this type.

        Args:
            variable_name (str): The variable to declare for this type.
            val (str): The value to assign to the variable.

        Returns:
            str: The declaration for this type.
        """
        variable_and_type = f"{variable_name}: {self.rust_type}"
        mut = "mut " if self.is_mutable_reference else ""
        return f"let {mut}{variable_and_type} = {val}"

    def to_argument(self, name: str) -> str:
        """Return the given name as if it is an argument to a function.

        This returns either:
            The name itself, or
            The name prefixed by "&mut " for a mutable reference.

        Args:
            name (str): The name to express as an argument to a function.

        Returns:
            str: The name expressed as an argument to function.
        """
        return f"&mut {name}" if self.is_mutable_reference else name


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

    def __init__(self, c_function: ParsecFunction):
        if len(c_function.arg_names) != len(c_function.arg_types):
            msg = (
                f"Mismatch between function parameters '{c_function.arg_names}' "
                "and their types = '{c_function.arg_types}'"
            )
            raise RuntimeError(msg)

        self._annotations = list(KANI_PROOF_ANNOS)
        harness_function_name = f"check_{c_function.name}"
        self._signature = f"fn {harness_function_name}()"

        rust_arguments_to_types = {
            name: self._to_rust_type(c_type)
            for name, c_type in zip(c_function.arg_names, c_function.arg_types, strict=False)
        }
        self._nondet_variable_decls = "\n    ".join(
            rust_type.declaration(name, val="kani::any();")
            for name, rust_type in rust_arguments_to_types.items()
        )
        argument_list = ", ".join(
            type_wrapper.to_argument(param_name)
            for param_name, type_wrapper in rust_arguments_to_types.items()
        )
        self._function_call = f"{c_function.name}({argument_list})"

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

    def _to_rust_type(self, c_type: str) -> RustTypeWrapper:
        """Return the corresponding Rust type, given a C type.

        Args:
            c_type (str): The C type.

        Raises:
            RuntimeError: Raised when a corresponding Rust type is unavailable.

        Returns:
            RustTypeWrapper: A wrapper for the corresponding Rust type.
        """
        match c_type:
            case "int *":
                return RustTypeWrapper("i32", is_mutable_reference=True)
            case "int":
                return RustTypeWrapper("i32")
            case _:
                msg = f"Unsupported translation of C type '{c_type}' to Rust type"
                raise RuntimeError(msg)
