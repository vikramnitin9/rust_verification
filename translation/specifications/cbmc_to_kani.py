from translation import Parser, CBMCAst
from lark.exceptions import UnexpectedToken


class TranslationError(Exception):
    """Represents an error in translating CBMC to Kani specifications."""

    pass


class CBMCToKani:
    """Translator from CBMC to Kani specifications.

    Attributes:
        parser (Parser[CBMCAst]): Parser for CBMC specifications.
    """

    parser: Parser[CBMCAst]

    def __init__(self, parser: Parser[CBMCAst]):
        self.parser = parser

    def translate(self, cprover_specs: list[str]) -> list[str]:
        """Return a list of Kani specifications translated from a list of CBMC specifications.

        Args:
            cprover_specs (list[str]): _description_

        Returns:
            list[str]: _description_
        """
        if not cprover_specs:
            return []
        kani_specs = []
        for spec in cprover_specs:
            try:
                cbmc_ast = self.parser.parse(spec)
                kani_specs.append(self._to_kani_str(cbmc_ast))
            except UnexpectedToken as ut:
                print(f"Failed to parse: '{spec}' with error: '{ut}'")
                continue
            except TranslationError as te:
                print(
                    f"Successfully parsed '{spec}', but failed to convert it to a Kani specification: '{te}'"
                )
                continue

        return kani_specs

    def _to_kani_str(self, spec: CBMCAst) -> str:
        """Return a Kani specification (as a string) that maps to the given CBMC specification.

        Args:
            spec (CBMCAst): The CBMC specification to convert to a a Kani specification.

        Raises:
            TranslationError: Raised when translation from CBMC to Kani fails (or is unsupported).

        Returns:
            str: The Kani specification.
        """
        raise NotImplementedError()
