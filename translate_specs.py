"""Script to translate CBMC specifications for C functions into equivalents in Kani."""

import argparse
import pickle as pkl
from pathlib import Path
from typing import cast

from loguru import logger

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
        help="Path to the .pkl file containing the"
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
    functions_to_translated_specs: dict[str, FunctionSpecification] = {}

    for function_name, function in functions.items():
        functions_to_translated_specs[function_name] = _translate_specifications(function)


def _translate_specifications(function: ParsecFunction) -> FunctionSpecification:
    """TODO: fill me in.

    Args:
        function (ParsecFunction): _description_

    Returns:
        FunctionSpecification: _description_
    """
    translated_preconditions: list[str] = []
    translated_postconditions: list[str] = []
    for _ in function.preconditions:
        pass
    for _ in function.postconditions:
        pass
    return FunctionSpecification(
        preconditions=translated_preconditions, postconditions=translated_postconditions
    )


if __name__ == "__main__":
    main()
