"""Classes to represent the next step to take during specification generation."""

from dataclasses import dataclass


@dataclass(frozen=True)
class SpecificationGenerationNextStep:
    """Base class for next step strategies."""

    def __post_init__(self) -> None:
        """Prevent creating instances of SpecificationGenerationNextStep (abstract class).

        Raises:
            RuntimeError: Raised when an instance of SpecificationGenerationNextStep is created.
        """
        if type(self) is SpecificationGenerationNextStep:
            msg = f"'{self.__class__.__name__}' is an abstract class"
            raise RuntimeError(msg)


@dataclass(frozen=True)
class AcceptVerifiedSpec(SpecificationGenerationNextStep):
    """Represent the case when a spec is successfully verified."""


@dataclass(frozen=True)
class AssumeSpecAsIs(SpecificationGenerationNextStep):
    """Represent the case when a spec is assumed, regardless of its correctness."""


@dataclass(frozen=True)
class BacktrackToCallee(SpecificationGenerationNextStep):
    """Represent the case when the next step is to backtrack and regenerate specs for a callee.

    Attributes:
        callee (str): The callee to backtrack to.
        hint (str): The description of how the callee specification should be strengthened.
    """

    callee: str
    hint: str
