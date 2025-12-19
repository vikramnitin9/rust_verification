#!/opt/miniconda3/bin/python

"""Script to translate CBMC specifications for C functions into equivalents in Kani."""

import argparse
import json
import pickle as pkl
from dataclasses import asdict
from pathlib import Path
from typing import cast

from loguru import logger

from translation import CBMCAst, CBMCToKani, KaniProofHarness, Parser, ToAst, TranslationError
from util import CFunction, FunctionSpecification
from util.rust import RustFunction, RustParser, TsRustParser
from verification import KaniVerificationContext


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
        "list of CFunction objects with specifications to translate.",
    )

    parser.add_argument(
        "--rust-file",
        required=True,
        help="Path to the Rust (.rs) file compiled from the source C program.",
    )

    args = parser.parse_args()

    path_to_functions = Path(args.functions)
    with path_to_functions.open("rb") as f:
        c_functions = [cast("CFunction", d) for d in pkl.load(f)]

    if not c_functions:
        msg = f"{path_to_functions} contained no valid functions."
        raise RuntimeError(msg)

    rust_parser: RustParser = TsRustParser()
    candidate_rust_functions = rust_parser.get_functions_defined_in_file(args.rust_file)

    _check_translation_preconditions(
        c_functions=c_functions, rust_function_name_to_function=candidate_rust_functions
    )
    logger.debug(f"Starting specification translation for functions in: '{path_to_functions}'")

    cbmc_parser: Parser[CBMCAst] = Parser(
        path_to_grammar_defn="translation/grammar/cbmc.txt",
        start="cbmc_clause",
        transformer=ToAst(),
    )
    functions_to_verification_contexts: dict[str, KaniVerificationContext] = {}
    translator = CBMCToKani(parser=cbmc_parser)

    for c_function in c_functions:
        specs = _translate_specifications(translator, c_function)
        rust_candidate = candidate_rust_functions[c_function.name]
        proof_harness = KaniProofHarness(rust_candidate, specs)
        functions_to_verification_contexts[c_function.name] = KaniVerificationContext(
            specification=specs, proof_harness=proof_harness
        )

    _save_translated_specifications(
        functions_to_verification_contexts=functions_to_verification_contexts,
        path_to_functions=path_to_functions,
    )


def _translate_specifications(translator: CBMCToKani, function: CFunction) -> FunctionSpecification:
    """Return the translated specifications originating from the given function.

    Args:
        translator (CBMCToKani): The translator to use for specification translation.
        function (CFunction): The function to obtain the specifications to translate.

    Returns:
        FunctionSpecification: A translated function specification.
    """
    return FunctionSpecification(
        preconditions=translator.translate(function.preconditions),
        postconditions=translator.translate(function.postconditions),
    )


def _save_translated_specifications(
    functions_to_verification_contexts: dict[str, KaniVerificationContext], path_to_functions: Path
) -> None:
    """Save translated specifications to disk.

    Args:
        functions_to_verification_contexts (dict[str, KaniVerificationContext]): A map from function
            names to their Kani verification contexts.
        path_to_functions (Path): The path to the original functions file.
    """
    result_file = path_to_functions.with_suffix("")
    data_to_write = {
        name: asdict(specs) for name, specs in functions_to_verification_contexts.items()
    }
    Path(f"{result_file}-translated-specs.json").write_text(json.dumps(data_to_write, indent=4))


def _check_translation_preconditions(
    c_functions: list[CFunction], rust_function_name_to_function: dict[str, RustFunction]
) -> None:
    """Check preconditions that must be met for specification translation.

    Args:
        c_functions (list[CFunction]): The C functions for which to translate specifications.
        rust_function_name_to_function (dict[str, RustFunction]): A map of candidate Rust functions
            (i.e., translated from the C functions).

    The following preconditions must be met for specification translation to occur:

    1. There exists a 1:1 mapping from a C function to a Rust function.
    2. Each Rust function must maintain the same signature of its C equivalent, i.e., equivalent
       return type, function name, argument list.

    The current implementation checks only (1).

    Raises:
        TranslationError: Raised when the first precondition is not satisfied.
    """
    if len(c_functions) != len(rust_function_name_to_function):
        msg = (
            f"Mismatch between C functions ({len(c_functions)}) "
            f"and Rust functions ({len(rust_function_name_to_function)})"
        )
        raise TranslationError(msg)
    if {f.name for f in c_functions} != set(rust_function_name_to_function.keys()):
        c_funcs = ", ".join(f.name for f in c_functions)
        rust_funcs = ", ".join(fn_name for fn_name in rust_function_name_to_function)
        msg = f"Mismatch between C functions ({c_funcs}) and Rust functions ({rust_funcs})"
        raise TranslationError(msg)
    # TODO: additional check(s) on the parameter names and types is necessary for a complete check.


if __name__ == "__main__":
    main()
