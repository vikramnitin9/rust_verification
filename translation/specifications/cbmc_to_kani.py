"""Deterministic compiler from CBMC to Kani specifications."""

import pathlib
from typing import Any

from lark.exceptions import UnexpectedToken, VisitError
from loguru import logger

from translation import CBMCAst, Parser, cbmc_ast

RUST_KEYWORDS: set[str] = set()
with pathlib.Path("translation/specifications/rust_keywords.txt").open(encoding="utf-8") as f:
    RUST_KEYWORDS = {kw.strip() for kw in f}

# These are obtained from C's limits.h header file, will be expanded as we build out the translator.
C_LIMITS_TO_RUST = {"INT_MAX": "i32::MAX", "INT_MIN": "i32::MIN"}


class TranslationError(Exception):
    """Represents an error in translating CBMC to Kani specifications."""


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
            except UnexpectedToken as ut:  # noqa: PERF203
                logger.error(f"Failed to parse: '{spec}' with error: '{ut}'")
                continue
            except TranslationError as te:
                logger.warning(
                    f"Successfully parsed '{spec}', but failed to convert it to a Kani "
                    f"specification: '{te}'"
                )
                continue
            except VisitError as ve:
                logger.warning(f"Encountered visit error: {ve}")
                if ve.orig_exc:
                    raise ve.orig_exc from ve
                raise

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
        match spec:
            case cbmc_ast.RequiresClause(_, expr):
                kani_condition = self._to_kani_str(expr)
                kani_condition = self._replace_cbmc_macros(kani_condition)
                return f"kani::requires({kani_condition})"
            case cbmc_ast.EnsuresClause(_, expr):
                kani_condition = self._to_kani_str(expr)
                kani_condition = self._replace_cbmc_macros(kani_condition)
                return f"kani::ensures({kani_condition})"
            case cbmc_ast.AssignsExpr(condition=cond, targets=target_list):
                if cond:
                    msg = f"Conditional assignment(s) in: {spec} are not supported in Kani"
                    raise TranslationError(msg)
                kani_writeable_set = self._to_kani_str(target_list)
                return f"kani::modifies({kani_writeable_set})"
            case cbmc_ast.AssignsTargetList(targets):
                return self._to_kani_str(targets)
            case cbmc_ast.ExprList(items):
                return ", ".join(self._to_kani_str(item) for item in items)
            case cbmc_ast.IndexOp(value, index):
                kani_value = self._to_kani_str(value)
                kani_index = self._to_kani_str(index)
                return f"{kani_value}[{kani_index}]"
            case cbmc_ast.Quantifier(_, range_expr, expr, kind):
                kani_quantifier_macro = f"{kind}!"
                kani_body_expr = self._to_kani_str(expr)
                return (
                    "kani::"
                    f"{kani_quantifier_macro}("
                    f"|{self._to_kani_range(range_expr)}| {kani_body_expr})"
                )
            case cbmc_ast.CallOp(func, args):
                rust_func = self._to_kani_str(func)
                rust_args = self._to_kani_str(args) if args else ""
                return f"{rust_func}({rust_args})"
            case cbmc_ast.DerefOp(operand):
                rust_operand = self._to_kani_str(operand)
                return f"*{rust_operand}"
            case cbmc_ast.MemberOp(value, attr):
                return f"{self._to_kani_str(value)}.{self._to_kani_str(attr)}"
            case cbmc_ast.Bool(v):
                return "true" if v else "false"
            case cbmc_ast.Name(v):
                if v in RUST_KEYWORDS:
                    msg = f"Specification '{spec}' contains a Rust keyword: '{v}'"
                    raise TranslationError(msg)
                return C_LIMITS_TO_RUST.get(str(v), str(v))
            case cbmc_ast.BinOp(left, right):
                return f"{self._to_kani_str(left)} {spec.operator()} {self._to_kani_str(right)}"
            case cbmc_ast.Number(v):
                return str(v)
            case unsupported_spec:
                msg = f"Failed to translate CBMC spec: {unsupported_spec}"
                raise TranslationError(msg)

    def _to_kani_range(self, cbmc_range_expr: Any) -> str:
        """Translate a range expression in CBMC to the equivalent Kani range as a string.

        E.g., `10 <= i && i < 20` translates to `i in (10, 20)`; Rust ranges are closed.

        Args:
            cbmc_range_expr (Any): A CBMC range expression.

        Raises:
            TranslationError: Raised when an invalid CBMC range is encountered.

        Returns:
            str: A string representation of the equivalent Kani range.
        """
        match cbmc_range_expr:
            case cbmc_ast.AndOp(cbmc_ast.LeOp(lower_bound, i), cbmc_ast.LtOp(j, upper_bound)):
                if i.name != j.name:
                    bound_mismatch = (
                        f"Invalid CBMC range (index must be the same in each bound): "
                        f"{cbmc_range_expr}"
                    )
                    raise TranslationError(bound_mismatch)
                kani_lower_bound = self._to_kani_str(lower_bound)
                kani_upper_bound = self._to_kani_str(upper_bound)
                return f"{self._to_kani_str(i)} in ({kani_lower_bound}, {kani_upper_bound})"
            case _:
                msg = f"Invalid CBMC range: {cbmc_range_expr}"
                raise TranslationError(msg)

    def _replace_cbmc_macros(self, cbmc_str: str) -> str:
        """Replace CBMC macros (e.g., __CPROVER_result, __CPROVER_old) with their Kani equivalents.

        Args:
            cbmc_str (str): The string on which to perform macro placement.

        Returns:
            str: The string with CBMC macros replaced with Kani equivalents.
        """
        result = cbmc_str
        if "__CPROVER_result" in cbmc_str:
            result = f"|result| {cbmc_str.replace('__CPROVER_result', 'result')}"
        if "__CPROVER_old" in cbmc_str:
            result = result.replace("__CPROVER_old", "old")
        return result
