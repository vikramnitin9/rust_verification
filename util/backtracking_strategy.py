"""Enums to represent backtracking strategies."""

from enum import StrEnum


class BacktrackingStrategy(StrEnum):
    """Enums to represent backtracking strategies."""

    ASSUME_SPEC = "ASSUME_SPEC"
    REPAIR_SPEC = "REPAIR_SPEC"
    REGENERATE_CALLEE_SPEC = "REGENERATE_CALLEE_SPEC"

    @property
    def is_regenerate_strategy(self) -> bool:
        """True iff this strategy involves specification regeneration.

        For now, the only strategies that involve specification regeneration are REPAIR_SPEC and
        REGENERATE_CALLEE_SPEC.

        Returns:
            bool: True iff this strategy involves the regeneration of a specification.
        """
        return self in frozenset(
            {BacktrackingStrategy.REPAIR_SPEC, BacktrackingStrategy.REGENERATE_CALLEE_SPEC}
        )
