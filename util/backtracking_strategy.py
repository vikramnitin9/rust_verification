"""Enums to represent backtracking strategies."""

from enum import StrEnum


# MDE: Currently, clients use "None" to represent successful verification.
# I think it would be clearer to add an enum item for that.
# Then maybe "BacktrackingStrategy" would be renamed to "NextStep", "NextStepStrategy", or the like.
class BacktrackingStrategy(StrEnum):
    """Enum to represent backtracking strategies."""

    ASSUME_SPEC = "ASSUME_SPEC"
    REPAIR_SPEC = "REPAIR_SPEC"
    REGENERATE_CALLEE_SPEC = "REGENERATE_CALLEE_SPEC"

    @property
    def is_regenerate_strategy(self) -> bool:
        """True iff this strategy involves specification regeneration.

        # MDE: define "specification regeneration".  I think it means: anytime that the current spec
        # is not accepted as is (which might be because it verifies or might be because it is
        # assumed).

        For now, the only strategies that involve specification regeneration are REPAIR_SPEC and
        REGENERATE_CALLEE_SPEC.

        Returns:
            bool: True iff this strategy involves the regeneration of a specification.

        """
        return self in frozenset(
            {BacktrackingStrategy.REPAIR_SPEC, BacktrackingStrategy.REGENERATE_CALLEE_SPEC}
        )
