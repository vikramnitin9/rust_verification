# ruff: noqa: N802, D102
# There are warnings in this file which cannot be avoided; the names of methods are directly
# mapped to the CBMC AST class names (the implementation requires this as it uses reflection),
# and the ruff requirement for snake_case conflicts with this.

"""Normalization logic for CBMC specifications."""

from pathlib import Path

from translation import Parser
from translation.ast import cbmc_ast
from translation.ast.cbmc_ast import ToAst
from util.function_specification import FunctionSpecification


class CBMCNormalizer:
    """Visitor that implements normalization of CBMC ASTs.

    Attributes:
        _scopes (list[dict[str, str]]): A stack of dictionaries for variables in specs, from their
            names as they appear in the unnormalized spec to their normalized names. Each dictionary
            corresponds to one scope level (within a quantifier, if necessary).
        _counter (int): A counter used to generate unique normalized variable names.

    This normalizer enforces:

        1. Consistent whitespace.
        2. Basic alpha-equivalence for bound variables in quantifiers.
        3. Parenthesizes expressions to avoid ambiguity.
    """

    def __init__(self) -> None:
        """Create a new CBMCNormalizer."""
        self._scopes: list[dict[str, str]] = []
        self._counter = 0

    def normalize(self, node: cbmc_ast.CBMCAst) -> str:
        """Return the normalized string representation of a CBMC AST.

        Args:
            node (cbmc_ast.CBMCAst): A CBMC AST node.

        Returns:
            str: The normalized string representation of the given CBMC AST node.
        """
        self._scopes = []
        self._counter = 0
        return self.visit(node)

    def visit(self, node: cbmc_ast.CBMCAst) -> str:
        """Return the result of visiting (and applying normalization to) a CBMC AST node.

        Args:
            node (cbmc_ast.CBMCAst): A CBMC AST node.

        Returns:
            str: The normalized string representation of the given CBMC AST Node.
        """
        if node is None:
            return ""

        method_name = f"visit_{node.__class__.__name__}"
        visitor = getattr(self, method_name, self.generic_visit)
        return visitor(node)

    def generic_visit(self, node: cbmc_ast.CBMCAst) -> str:
        msg = f"Unimplemented visitor for {node.__class__.__name__}"
        raise NotImplementedError(msg)

    def visit_RequiresClause(self, node: cbmc_ast.RequiresClause) -> str:
        return f"__CPROVER_requires({self.visit(node.expr)})"

    def visit_EnsuresClause(self, node: cbmc_ast.EnsuresClause) -> str:
        return f"__CPROVER_ensures({self.visit(node.expr)})"

    def visit_Name(self, node: cbmc_ast.Name) -> str:
        # Check scopes in reverse order for bound variable replacement
        for scope in reversed(self._scopes):
            if node.name in scope:
                return scope[node.name]
        return node.name

    def visit_Number(self, node: cbmc_ast.Number) -> str:
        return str(node.value)

    def visit_Bool(self, node: cbmc_ast.Bool) -> str:
        return "1" if node.value else "0"

    def visit_StringLit(self, node: cbmc_ast.StringLit) -> str:
        # The grammar already quotes string literals, there is no need to quote here again.
        return f"{node.value}"

    # --- Operations ---

    def _visit_binop(self, node: cbmc_ast.BinOp) -> str:
        # Enforce parentheses for strict canonical form.
        return f"({self.visit(node.left)} {node.operator()} {self.visit(node.right)})"

    def visit_OrOp(self, node: cbmc_ast.OrOp) -> str:
        return self._visit_binop(node)

    def visit_AndOp(self, node: cbmc_ast.AndOp) -> str:
        return self._visit_binop(node)

    def visit_EqOp(self, node: cbmc_ast.EqOp) -> str:
        return self._visit_binop(node)

    def visit_NeqOp(self, node: cbmc_ast.NeqOp) -> str:
        return self._visit_binop(node)

    def visit_LtOp(self, node: cbmc_ast.LtOp) -> str:
        return self._visit_binop(node)

    def visit_LeOp(self, node: cbmc_ast.LeOp) -> str:
        return self._visit_binop(node)

    def visit_GtOp(self, node: cbmc_ast.GtOp) -> str:
        return self._visit_binop(node)

    def visit_GeOp(self, node: cbmc_ast.GeOp) -> str:
        return self._visit_binop(node)

    def visit_AddOp(self, node: cbmc_ast.AddOp) -> str:
        return self._visit_binop(node)

    def visit_SubOp(self, node: cbmc_ast.SubOp) -> str:
        return self._visit_binop(node)

    def visit_MulOp(self, node: cbmc_ast.MulOp) -> str:
        return self._visit_binop(node)

    def visit_DivOp(self, node: cbmc_ast.DivOp) -> str:
        return self._visit_binop(node)

    def visit_ModOp(self, node: cbmc_ast.ModOp) -> str:
        return self._visit_binop(node)

    def visit_NotOp(self, node: cbmc_ast.NotOp) -> str:
        return f"!{self.visit(node.operand)}"

    def visit_AddrOp(self, node: cbmc_ast.AddrOp) -> str:
        return f"&{self.visit(node.operand)}"

    def visit_DerefOp(self, node: cbmc_ast.DerefOp) -> str:
        return f"*{self.visit(node.operand)}"

    def visit_NegOp(self, node: cbmc_ast.NegOp) -> str:
        return f"-({self.visit(node.operand)})"

    def visit_PosOp(self, node: cbmc_ast.PosOp) -> str:
        return f"+({self.visit(node.operand)})"

    def visit_MemberOp(self, node: cbmc_ast.MemberOp) -> str:
        attr = node.attr.name if isinstance(node.attr, cbmc_ast.Name) else self.visit(node.attr)
        return f"{self.visit(node.value)}.{attr}"

    def visit_PtrMemberOp(self, node: cbmc_ast.PtrMemberOp) -> str:
        # attr is a string in PtrMemberOp according to cbmc_ast.py
        return f"{self.visit(node.value)}->{node.attr}"

    def visit_IndexOp(self, node: cbmc_ast.IndexOp) -> str:
        return f"{self.visit(node.value)}[{self.visit(node.index)}]"

    def visit_CallOp(self, node: cbmc_ast.CallOp) -> str:
        return f"{self.visit(node.func)}({self.visit(node.args)})"

    def visit_ArgList(self, node: cbmc_ast.ArgList) -> str:
        return ", ".join(self.visit(item) for item in node.items)

    # --- Types and Quantifiers ---

    def visit_BuiltinType(self, node: cbmc_ast.BuiltinType) -> str:
        return node.name

    def visit_NamedType(self, node: cbmc_ast.NamedType) -> str:
        return self.visit(node.name)

    def visit_QuantifierDecl(self, node: cbmc_ast.QuantifierDecl) -> str:
        typ_str = self.visit(node.typenode)
        # The variable in the quantifier declaration (i.e., the bound) should use the current
        # scope's normalized name, so we look it up in the scopes.
        name_str = node.name.name
        if self._scopes and name_str in self._scopes[-1]:
            name_str = self._scopes[-1][name_str]

        return f"{typ_str} {name_str}"

    def visit_ForallExpr(self, node: cbmc_ast.ForallExpr) -> str:
        return self._visit_quantifier(node, "__CPROVER_forall", "==>")

    def visit_ExistsExpr(self, node: cbmc_ast.ExistsExpr) -> str:
        return self._visit_quantifier(node, "__CPROVER_exists", "&&")

    def _visit_quantifier(self, node: cbmc_ast.Quantifier, key: str, op: str) -> str:
        old_name = node.decl.name.name
        new_name = f"_bound_{self._counter}"
        self._counter += 1

        self._scopes.append({old_name: new_name})
        try:
            decl_str = self.visit(node.decl)
            range_str = self.visit(node.range_expr)
            expr_str = self.visit(node.expr)
            return f"{key} {{ {decl_str}; ({range_str}) {op} {expr_str} }}"
        finally:
            self._scopes.pop()

    def visit_Old(self, node: cbmc_ast.Old) -> str:
        return f"__CPROVER_old({self.visit(node.expr)})"  # Assuming standard old syntax

    def visit_ReturnValue(self, node: cbmc_ast.ReturnValue) -> str:
        del node  # This is unused.
        return "__CPROVER_return_value"

    def visit_Assigns(self, node: cbmc_ast.Assigns) -> str:
        # This processes the top-level `__CPROVER_assigns` clause. Ideally, it would be named
        # visit_AssignsClause. However, the AST node must be named `Assigns` since naming it
        # `AssignsClause` will conflict with Lark's auto-generated class names used under the hood
        # for its parser. The same issue does not occur with `EnsuresClause` and `RequiresClause`
        # because we do not define our own methods for them (i.e., the auto-generated ones are
        # adequate for our needs).
        targets = self.visit(node.targets)
        if node.condition:
            cond = self.visit(node.condition)
            return f"__CPROVER_assigns({cond} : {targets})"
        return f"__CPROVER_assigns({targets})"

    def visit_AssignsTargetList(self, node: cbmc_ast.AssignsTargetList) -> str:
        return self.visit(node.items)

    def visit_ExprList(self, node: cbmc_ast.ExprList) -> str:
        return ", ".join(self.visit(item) for item in node.items)


grammar_path = Path(__file__).parent / "grammar/cbmc.txt"
_PARSER: Parser[cbmc_ast.CBMCAst] = Parser(
    path_to_grammar_defn=str(grammar_path),
    start="cbmc_clause",
    transformer=ToAst(),
)


def normalize_cbmc_spec(spec_string: str) -> str:
    """Return a normalized CBMC specification.

    Args:
        spec_string (str): The CBMC specification, as a string.

    Returns:
        str: The normalized CBMC specification.
    """
    try:
        cbmc_ast_node = _PARSER.parse(spec_string)

        # A per-call instance of normalizer is required due to scope counting.
        return CBMCNormalizer().normalize(cbmc_ast_node)
    except Exception as e:
        msg = f"Failed to normalize specification '{spec_string}': {e}"
        raise RuntimeError(msg) from e


def normalize_function_specification(spec: FunctionSpecification) -> FunctionSpecification:
    """Return a normalized function specification.

    Args:
        spec (FunctionSpecification): Normalizes the CBMC specifications in a given function spec.

    Returns:
        FunctionSpecification: A new function spec with normalized pre and postconditions.
    """
    normalized_preconditions = [normalize_cbmc_spec(p) for p in spec.preconditions]
    normalized_postconditions = [normalize_cbmc_spec(p) for p in spec.postconditions]
    return FunctionSpecification(
        preconditions=normalized_preconditions, postconditions=normalized_postconditions
    )
