"""Script to translate CBMC specifications for C functions into equivalents in Kani."""

import argparse
import json
import pickle as pkl
from dataclasses import asdict
from pathlib import Path
from typing import cast

from loguru import logger

from translation import CBMCAst, CBMCToKani, Parser, ToAst
from util import FunctionSpecification, ParsecFunction


def main() -> None:
    """Entry point for translating CBMC specs to their equivalents in Kani."""
    parser = argparse.ArgumentParser(
        description="Script to translate CBMC specifications for C "
        "functions into their Kani equivalents."
    )
    parser.add_argument(
        "--functions",
        required=True,
        help="Path to the .pkl file containing the "
        "list of ParsecFunction objects with specifications to translate.",
    )

    args = parser.parse_args()

    path_to_functions = Path(args.functions)
    with path_to_functions.open("rb") as f:
        data = [cast("ParsecFunction", d) for d in pkl.load(f)]
        functions = {f.name: f for f in data}

    if not functions:
        msg = f"{path_to_functions} contained no valid functions."
        raise RuntimeError(msg)

    logger.debug(f"Starting specification translation for functions in: '{path_to_functions}'")

    cbmc_parser: Parser[CBMCAst] = Parser(
        path_to_grammar_defn="translation/grammar/cbmc.txt",
        start="cbmc_clause",
        transformer=ToAst(),
    )
    functions_to_translated_specs: dict[str, FunctionSpecification] = {}
    translator = CBMCToKani(parser=cbmc_parser)

    for function_name, function in functions.items():
        functions_to_translated_specs[function_name] = _translate_specifications(
            translator, function
        )

    _save_translated_specifications(
        functions_to_translated_specs=functions_to_translated_specs,
        path_to_functions=path_to_functions,
    )


def _translate_specifications(
    translator: CBMCToKani, function: ParsecFunction
) -> FunctionSpecification:
    """Return the translated specifications originating from the given function.

    Args:
        translator (CBMCToKani): The translator to use for specification translation.
        function (ParsecFunction): The function to obtain the specifications to translate.

    Returns:
        FunctionSpecification: A translated function specification.
    """
    return FunctionSpecification(
        preconditions=translator.translate(function.preconditions),
        postconditions=translator.translate(function.postconditions),
    )


def _save_translated_specifications(
    functions_to_translated_specs: dict[str, FunctionSpecification], path_to_functions: Path
) -> None:
    """Save translated specifications to disk.

    Args:
        functions_to_translated_specs (dict[str, FunctionSpecification]): A map from function names
            to their translated specifications.
        path_to_functions (Path): The path to the original functions file.
    """
    result_file = path_to_functions.with_suffix("")
    with Path(f"{result_file}-translated-specs.json").open("w") as f:
        data_to_write = {
            name: asdict(specs) for name, specs in functions_to_translated_specs.items()
        }
        f.write(json.dumps(data_to_write, indent=4))


if __name__ == "__main__":
    main()
