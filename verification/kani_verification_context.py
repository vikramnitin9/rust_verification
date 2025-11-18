"""Class representing a Kani verification context."""

from dataclasses import dataclass

from translation import KaniProofHarness
from util import FunctionSpecification


@dataclass(frozen=True)
class KaniVerificationContext:
    """A verification context for Kani.

    Attributes:
        specifications (FunctionSpecification): The pre and postconditions for a Rust function.
        proof_harness (KaniProofHarness): The proof harness for the Rust function under
            verification.
    """

    specifications: FunctionSpecification
    proof_harness: KaniProofHarness
