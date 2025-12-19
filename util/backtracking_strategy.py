"""Enums to represent backtracking strategies."""

from enum import StrEnum


class BacktrackingStrategy(StrEnum):
    """Enums to represent backtracking strategies."""

    ASSUME_SPEC = "ASSUME_SPEC"
    REPAIR_SPEC = "REPAIR_SPEC"
    REGENERATE_CALLEE_SPEC = "REGENERATE_CALLEE_SPEC"
