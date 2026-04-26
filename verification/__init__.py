"""Modules for verifying C and Rust programs with CBMC and Kani."""

from .avocado_stub_util import (
    AVOCADO_STUB_DIR,
    AvocadoIdentifierRenamer,
    RenameData,
    get_stub_mappings,
)
from .cbmc_verification_client import CbmcVerificationClient
from .external_function_documentation_manager import (
    EntityType,
    ExternalFunctionDocumentationManager,
    FunctionParameter,
    ParsedDocumentation,
)
from .kani_verification_context import KaniVerificationContext
from .prompt_builder import PromptBuilder
from .proof_state import ProofState, WorkItem, WorkStack
from .proof_state_stepper import ProofStateStepper
from .verification_client import VerificationClient
from .verification_input import VerificationContext, VerificationInput
from .verification_result import VerificationResult, VerificationStatus

__all__ = [
    "AVOCADO_STUB_DIR",
    "AvocadoIdentifierRenamer",
    "CbmcVerificationClient",
    "EntityType",
    "ExternalFunctionDocumentationManager",
    "FunctionParameter",
    "KaniVerificationContext",
    "ParsedDocumentation",
    "PromptBuilder",
    "ProofState",
    "ProofStateStepper",
    "RenameData",
    "VerificationClient",
    "VerificationContext",
    "VerificationInput",
    "VerificationResult",
    "VerificationStatus",
    "WorkItem",
    "WorkStack",
    "get_stub_mappings",
]
