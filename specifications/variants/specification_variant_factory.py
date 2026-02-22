"""Class for symbolically generating variants of a specification."""

from util import FunctionSpecification

from .transformations import MovePreconditionsToAssignsAndEnsures, SpecificationTransformation


class SpecificationVariantFactory:
    """Class for symbolically generating variants of a specification.

    Attributes:
        (_transformations): tuple[SpecificationTransformation, ...]: The transformations to apply
            to a specification to generate variants.

    """

    _transformations: tuple[SpecificationTransformation, ...]

    def __init__(self) -> None:
        """Create a new SpecificationVariantFactory."""
        self._transformations = (MovePreconditionsToAssignsAndEnsures(),)

    def get_variants(self, spec: FunctionSpecification) -> tuple[FunctionSpecification, ...]:
        """Return the variants of the given specification.

        Args:
            spec (FunctionSpecification): The specifications for which to generate variants.

        Returns:
            tuple[FunctionSpecification, ...]: The variants of the given specification.
        """
        return tuple(transformation.apply(spec) for transformation in self._transformations)
