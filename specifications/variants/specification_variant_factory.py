"""Class for symbolically generating variants of a specification."""

from util import FunctionSpecification

from .transformations import (
    MovePreconditionsToAssignsAndEnsures,
    RemovePreconditions,
    SpecificationTransformation,
)


class SpecificationVariantFactory:
    """Class for symbolically generating variants of a specification.

    Attributes:
        (_transformations): tuple[SpecificationTransformation, ...]: The transformations to apply
            to a specification to generate variants.

    """

    _transformations: tuple[SpecificationTransformation, ...]

    def __init__(self) -> None:
        """Create a new SpecificationVariantFactory."""
        self._transformations = (MovePreconditionsToAssignsAndEnsures(), RemovePreconditions())

    def get_variants(self, spec: FunctionSpecification) -> tuple[FunctionSpecification, ...]:
        """Return the variants of the given specification.

        Args:
            spec (FunctionSpecification): The specifications for which to generate variants.

        Returns:
            tuple[FunctionSpecification, ...]: The variants of the given specification.
        """
        variants = set()
        for transformation in self._transformations:
            variants.update(transformation.apply(spec))
        return tuple(variants)
