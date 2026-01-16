"""Enums to represent the next step to take during specification generation."""

from enum import StrEnum


class SpecificationGenerationNextStep(StrEnum):
    """Enum to represent the next step to take during specification generation."""

    ACCEPT_VERIFIED_SPEC = "ACCEPT_VERIFIED_SPEC"
    ASSUME_SPEC_AS_IS = "ASSUME_SPEC_AS_IS"
    REPAIR_SPEC = "REPAIR_SPEC"
    REGENERATE_CALLEE_SPEC = "REGENERATE_CALLEE_SPEC"

    # MDE: As mentioned elsewhere, the REGENERATE_CALLEE_SPEC strategy leads to a change in the
    # workstack, but the REPAIR_SPEC strategy does not lead to a change in the workstack (only a
    # change to the SpecConversation).  Therefore, I think that a routine that lumps them together
    # is not needed or desirable.  I suggest that clients should separately handle those two cases
    # rather than lumping them together.
    @property
    def is_regenerate_strategy(self) -> bool:
        """True iff this strategy involves specification regeneration.

        Note: A specification is said to be "regenerated" if the current specification is not
        accepted as-is by a verifier. A specification may be accepted as-is by a verifier if it
        successfully verifies, or is assumed.

        For now, the only strategies that involve specification regeneration are REPAIR_SPEC and
        REGENERATE_CALLEE_SPEC.

        Returns:
            bool: True iff this strategy involves the regeneration of a specification.

        """
        return self in frozenset(
            {
                SpecificationGenerationNextStep.REPAIR_SPEC,
                SpecificationGenerationNextStep.REGENERATE_CALLEE_SPEC,
            }
        )
