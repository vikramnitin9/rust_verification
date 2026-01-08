"""Enums to represent the next step to take during specification generation."""

from enum import StrEnum


class SpecificationGenerationNextStep(StrEnum):
    """Enum to represent the next step to take during specification generation."""

    ACCEPT_VERIFIED_SPEC = "ACCEPT_VERIFIED_SPEC"
    ASSUME_SPEC_AS_IS = "ASSUME_SPEC_AS_IS"
    REGENERATE_CALLEE_SPEC = "REGENERATE_CALLEE_SPEC"
