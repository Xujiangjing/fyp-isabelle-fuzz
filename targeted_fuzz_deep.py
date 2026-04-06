#!/usr/bin/env python3
"""
targeted_fuzz_deep.py — Deep source-informed fuzzing for Zipperposition internals.

Round 2: Targets BEYOND the parser — type inference, term construction,
superposition engine, and proof search internals.

These inputs are syntactically valid TPTP that passes the parser, but aims
to trigger crashes in deeper layers:

  D1. TYPE INFERENCE assert false — TypeInference.ml
      Lines 211, 377, 640, 661, 670, 703
      Targets: polymorphic type mismatch, bad binder types, $distinct edge cases

  D2. TYPE CONSTRUCTION — Type.ml
      Lines 42, 44, 330, 335, 362, 562, 568, 576
      Targets: malformed arrow types, record types, multiset types

  D3. TERM CONSTRUCTION — InnerTerm.ml, Term.ml
      assert false on NoType (line 290), empty App (line 304),
      bad Arrow (line 328, 1097, 1193)
      Targets: complex higher-order terms that stress internal representation

  D4. FRAGMENT CHECKING — Term.ml in_pfho_fragment / in_lfho_fragment
      Lines 552-590: Failure() on out-of-fragment types
      Already known (Family A/B/C) but test with new patterns

  D5. SUPERPOSITION ENGINE — superposition.ml (42 crash points)
      Targets: formulas that cause unusual clause structures

  D6. ORDERING — Ordering.ml (13 crash points)
      Targets: terms that stress the term ordering (KBO/RPO)

  D7. UNIFICATION — Unif.ml (22 crash points), PatternUnif.ml (17)
      Targets: unification problems with complex type structures

  D8. BUILTIN ARITHMETIC — Builtin.ml
      Targets: arithmetic operations at boundaries (division by zero, overflow)

  D9. HIGHER-ORDER — Higher_order.ml (14 crash points)
      Targets: lambda terms, partial application, boolean extensionality

  D10. REAL SLEDGEHAMMER PATTERNS
       Complex formulas mimicking real Sledgehammer output with type classes,
       group theory axioms, etc.

Usage:
    python3 targeted_fuzz_deep.py full \
        --zp /path/to/zipperposition \
        --output-dir ~/fyp-isabelle-fuzz/deep_results
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path


# ═══════════════════════════════════════════════════════════════════════
#  DEEP TEST CASE GENERATORS
# ═══════════════════════════════════════════════════════════════════════

def d1_type_inference() -> list[tuple[str, str]]:
    """D1: Type inference crash points."""
    cases = []

    # Polymorphic type variable used inconsistently
    cases.append((
        "d1_poly_mismatch",
        "% D1: polymorphic type used at two incompatible types\n"
        "thf(decl_f, type, f : !>[A:$tType]: (A > A)).\n"
        "thf(conj, conjecture, (f @ $o @ $true) = (f @ $i @ $true)).\n"
    ))

    # Deeply nested polymorphic quantification
    cases.append((
        "d1_poly_deep",
        "% D1: deeply nested polymorphic quantification\n"
        "thf(decl, type, f : !>[A:$tType, B:$tType]: (A > B > A)).\n"
        "thf(decl2, type, g : !>[A:$tType]: (A > $o)).\n"
        "thf(conj, conjecture, ![X:$i]: (g @ $i @ (f @ $i @ $o @ X @ $true))).\n"
    ))

    # Type application with wrong number of arguments
    cases.append((
        "d1_type_arity_mismatch",
        "% D1: type constructor with wrong arity\n"
        "thf(decl_t, type, pair : $tType > $tType > $tType).\n"
        "thf(decl_f, type, f : (pair @ $i) > $o).\n"
        "thf(conj, conjecture, f = f).\n"
    ))

    # Equality between terms of different types
    cases.append((
        "d1_eq_type_mismatch",
        "% D1: equality between different types\n"
        "thf(decl_a, type, a : $i).\n"
        "thf(decl_b, type, b : $o).\n"
        "thf(conj, conjecture, a = b).\n"
    ))

    # Variable with function type in quantifier
    cases.append((
        "d1_func_type_var",
        "% D1: quantified variable with function type\n"
        "thf(conj, conjecture, ![F: $i > $o, X: $i]: (F @ X)).\n"
    ))

    # Applying a non-function
    cases.append((
        "d1_apply_non_func",
        "% D1: applying a non-function term\n"
        "thf(decl, type, a : $i).\n"
        "thf(decl2, type, b : $i).\n"
        "thf(conj, conjecture, (a @ b) = b).\n"
    ))

    # $distinct with single element
    cases.append((
        "d1_distinct_single",
        "% D1: $distinct with single argument\n"
        "thf(decl, type, a : $i).\n"
        "thf(conj, conjecture, $distinct(a)).\n"
    ))

    # $distinct with many mixed-type elements
    cases.append((
        "d1_distinct_mixed",
        "% D1: $distinct with terms that need type unification\n"
        "thf(d1, type, a : $i).\n"
        "thf(d2, type, b : $i).\n"
        "thf(d3, type, c : $i).\n"
        "thf(d4, type, d : $i).\n"
        "thf(d5, type, e : $i).\n"
        "thf(d6, type, f : $i).\n"
        "thf(d7, type, g : $i).\n"
        "thf(d8, type, h : $i).\n"
        "thf(conj, conjecture, $distinct(a,b,c,d,e,f,g,h)).\n"
    ))

    # Nested equality with complex types
    cases.append((
        "d1_nested_eq",
        "% D1: nested equality\n"
        "thf(decl, type, f : ($i > $i) > $i).\n"
        "thf(decl2, type, g : $i > $i).\n"
        "thf(conj, conjecture, f @ g = f @ g).\n"
    ))

    # Higher-order unification challenge
    cases.append((
        "d1_ho_unif",
        "% D1: higher-order unification\n"
        "thf(decl, type, f : ($i > $o) > $o).\n"
        "thf(decl2, type, a : $i).\n"
        "thf(conj, conjecture, f @ (^[X:$i]: X = a)).\n"
    ))

    return cases


def d2_type_construction() -> list[tuple[str, str]]:
    """D2: Type.ml edge cases."""
    cases = []

    # Type with star (product type) — might not be fully supported
    cases.append((
        "d2_product_type",
        "% D2: product type\n"
        "thf(decl, type, f : ($i * $i) > $o).\n"
        "thf(conj, conjecture, f = f).\n"
    ))

    # Arrow type with many arguments
    args = " > ".join(["$i"] * 20) + " > $o"
    cases.append((
        "d2_many_arg_arrow",
        f"% D2: arrow type with 20 arguments\n"
        f"thf(decl, type, f : {args}).\n"
        f"thf(conj, conjecture, f = f).\n"
    ))

    # Type variable used as a type and as a term
    cases.append((
        "d2_type_term_confusion",
        "% D2: type variable in term position\n"
        "thf(decl, type, f : !>[A:$tType]: (A > $o)).\n"
        "thf(conj, conjecture, ![X:$i]: (f @ $i @ X)).\n"
    ))

    # Recursive-looking type
    cases.append((
        "d2_recursive_type",
        "% D2: self-referential type pattern\n"
        "thf(decl_t, type, list : $tType > $tType).\n"
        "thf(decl_nil, type, nil : !>[A:$tType]: (list @ A)).\n"
        "thf(decl_cons, type, cons : !>[A:$tType]: (A > (list @ A) > (list @ A))).\n"
        "thf(conj, conjecture, (cons @ $i @ nil @ $i) = (cons @ $i @ nil @ $i)).\n"
    ))

    return cases


def d3_term_construction() -> list[tuple[str, str]]:
    """D3: InnerTerm/Term edge cases."""
    cases = []

    # Very deeply nested term
    depth = 100
    term = "$true"
    for i in range(depth):
        term = f"(^[X{i}:$o]: X{i}) @ ({term})"
    cases.append((
        "d3_deep_nested_100",
        f"% D3: 100-deep nested lambda application\n"
        f"thf(conj, conjecture, {term}).\n"
    ))

    # Large disjunction
    atoms = " | ".join([f"p{i}" for i in range(100)])
    decls = "\n".join([f"thf(d{i}, type, p{i} : $o)." for i in range(100)])
    cases.append((
        "d3_large_disjunction",
        f"% D3: 100-way disjunction\n"
        f"{decls}\n"
        f"thf(conj, conjecture, {atoms}).\n"
    ))

    # Large conjunction
    atoms_and = " & ".join([f"q{i}" for i in range(100)])
    decls_and = "\n".join([f"thf(dq{i}, type, q{i} : $o)." for i in range(100)])
    cases.append((
        "d3_large_conjunction",
        f"% D3: 100-way conjunction\n"
        f"{decls_and}\n"
        f"thf(conj, conjecture, {atoms_and}).\n"
    ))

    # Application of lambda to wrong type argument
    cases.append((
        "d3_lambda_type_error",
        "% D3: lambda applied to wrong type\n"
        "thf(decl, type, a : $i).\n"
        "thf(conj, conjecture, (^[X:$o]: X) @ a).\n"
    ))

    # Partial application chain
    cases.append((
        "d3_partial_app_chain",
        "% D3: partial application chain\n"
        "thf(decl, type, f : $i > $i > $i > $o).\n"
        "thf(decl2, type, a : $i).\n"
        "thf(conj, conjecture, f @ a @ a @ a).\n"
    ))

    # Boolean term used as individual
    cases.append((
        "d3_bool_as_term",
        "% D3: boolean formula used as term argument\n"
        "thf(decl, type, f : $o > $o).\n"
        "thf(decl2, type, p : $o).\n"
        "thf(decl3, type, q : $o).\n"
        "thf(conj, conjecture, f @ (p & q)).\n"
    ))

    # Negation of complex term
    cases.append((
        "d3_complex_negation",
        "% D3: negation of complex higher-order term\n"
        "thf(decl, type, f : ($i > $o) > $o).\n"
        "thf(decl2, type, p : $i > $o).\n"
        "thf(conj, conjecture, ~ (f @ (^[X:$i]: ~ (p @ X)))).\n"
    ))

    return cases


def d4_fragment_checking() -> list[tuple[str, str]]:
    """D4: Fragment checking edge cases (in_pfho_fragment)."""
    cases = []

    # Term with prop-typed subterm (triggers type_ok check)
    cases.append((
        "d4_prop_subterm",
        "% D4: prop-typed argument in non-top-level position\n"
        "thf(decl, type, f : $o > $i).\n"
        "thf(decl2, type, g : $i > $o).\n"
        "thf(conj, conjecture, g @ (f @ $true)).\n"
    ))

    # Skolem symbol with complex type
    cases.append((
        "d4_complex_skolem",
        "% D4: complex term that might confuse fragment check\n"
        "thf(decl, type, f : ($i > $o) > $i).\n"
        "thf(decl2, type, p : $i > $o).\n"
        "thf(ax, axiom, ![P: $i > $o]: ?[X: $i]: (P @ X)).\n"
        "thf(conj, conjecture, ?[X: $i]: (p @ X)).\n"
    ))

    # Int-typed terms (type_ok rejects int/rat/prop)
    cases.append((
        "d4_int_term",
        "% D4: integer arithmetic terms\n"
        "thf(decl, type, f : $int > $int > $o).\n"
        "thf(conj, conjecture, f @ ($sum @ 1 @ 2) @ ($product @ 3 @ 4)).\n"
    ))

    # Rat-typed terms
    cases.append((
        "d4_rat_term",
        "% D4: rational arithmetic terms\n"
        "thf(decl, type, f : $rat > $o).\n"
        "thf(conj, conjecture, f @ ($sum @ 1/2 @ 1/3)).\n"
    ))

    return cases


def d5_superposition_stress() -> list[tuple[str, str]]:
    """D5: Formulas that stress the superposition engine."""
    cases = []

    # Many equalities
    eqs = " & ".join([f"(f @ c{i}) = c{(i+1) % 20}" for i in range(20)])
    decls = "thf(df, type, f : $i > $i).\n"
    decls += "\n".join([f"thf(dc{i}, type, c{i} : $i)." for i in range(20)])
    cases.append((
        "d5_equality_chain",
        f"% D5: chain of equalities\n"
        f"{decls}\n"
        f"thf(ax, axiom, {eqs}).\n"
        f"thf(conj, conjecture, c0 = c0).\n"
    ))

    # Contradictory axioms
    cases.append((
        "d5_contradiction",
        "% D5: direct contradiction\n"
        "thf(decl, type, p : $o).\n"
        "thf(ax1, axiom, p).\n"
        "thf(ax2, axiom, ~p).\n"
        "thf(conj, conjecture, $false).\n"
    ))

    # Commutativity + associativity (known to be hard)
    cases.append((
        "d5_comm_assoc",
        "% D5: commutativity + associativity\n"
        "thf(decl, type, f : $i > $i > $i).\n"
        "thf(decl2, type, a : $i).\n"
        "thf(decl3, type, b : $i).\n"
        "thf(decl4, type, c : $i).\n"
        "thf(ax_comm, axiom, ![X:$i, Y:$i]: ((f @ X @ Y) = (f @ Y @ X))).\n"
        "thf(ax_assoc, axiom, ![X:$i, Y:$i, Z:$i]: ((f @ (f @ X @ Y) @ Z) = (f @ X @ (f @ Y @ Z)))).\n"
        "thf(conj, conjecture, (f @ (f @ a @ b) @ c) = (f @ a @ (f @ c @ b))).\n"
    ))

    # Many variables
    vars_decl = ", ".join([f"X{i}:$i" for i in range(30)])
    eq_chain = " & ".join([f"X{i} = X{(i+1) % 30}" for i in range(30)])
    cases.append((
        "d5_many_vars",
        f"% D5: many quantified variables\n"
        f"thf(conj, conjecture, ![{vars_decl}]: ({eq_chain})).\n"
    ))

    return cases


def d6_ordering_stress() -> list[tuple[str, str]]:
    """D6: Terms that stress KBO/RPO ordering."""
    cases = []

    # Deeply nested function application
    term = "a"
    for i in range(50):
        term = f"f @ ({term})"
    cases.append((
        "d6_deep_func",
        f"% D6: deeply nested function application\n"
        f"thf(decl_f, type, f : $i > $i).\n"
        f"thf(decl_a, type, a : $i).\n"
        f"thf(conj, conjecture, ({term}) = a).\n"
    ))

    # Many different function symbols
    decls = "\n".join([f"thf(df{i}, type, f{i} : $i > $i)." for i in range(50)])
    chain = "a"
    for i in range(50):
        chain = f"f{i} @ ({chain})"
    cases.append((
        "d6_many_funcs",
        f"% D6: many different function symbols\n"
        f"thf(decl_a, type, a : $i).\n"
        f"{decls}\n"
        f"thf(conj, conjecture, ({chain}) = a).\n"
    ))

    return cases


def d7_unification() -> list[tuple[str, str]]:
    """D7: Unification edge cases."""
    cases = []

    # Occurs check scenario
    cases.append((
        "d7_occurs_check",
        "% D7: occurs check\n"
        "thf(decl, type, f : $i > $i).\n"
        "thf(conj, conjecture, ![X:$i]: (X = f @ X)).\n"
    ))

    # Higher-order unification with flex-flex pair
    cases.append((
        "d7_flex_flex",
        "% D7: flex-flex unification pair\n"
        "thf(decl, type, a : $i).\n"
        "thf(conj, conjecture, ?[F: $i > $i, G: $i > $i]: (F @ a = G @ a)).\n"
    ))

    # Flex-rigid with lambda
    cases.append((
        "d7_flex_rigid_lambda",
        "% D7: flex-rigid with lambda\n"
        "thf(decl, type, a : $i).\n"
        "thf(decl2, type, b : $i).\n"
        "thf(conj, conjecture, ?[F: $i > $i]: (F @ a = b)).\n"
    ))

    return cases


def d8_arithmetic() -> list[tuple[str, str]]:
    """D8: Arithmetic edge cases."""
    cases = []

    # Integer arithmetic
    cases.append((
        "d8_int_arith",
        "% D8: integer arithmetic\n"
        "thf(conj, conjecture, $less @ 1 @ 2).\n"
    ))

    # Rational arithmetic
    cases.append((
        "d8_rat_arith",
        "% D8: rational arithmetic\n"
        "thf(conj, conjecture, $less @ 1/3 @ 2/3).\n"
    ))

    # Very large numbers in arithmetic
    cases.append((
        "d8_large_nums",
        "% D8: large number arithmetic\n"
        f"thf(conj, conjecture, $less @ {'9' * 100} @ {'9' * 101}).\n"
    ))

    # Sum with many terms
    cases.append((
        "d8_sum_chain",
        "% D8: chain of sums\n"
        "thf(conj, conjecture, $less @ ($sum @ ($sum @ ($sum @ 1 @ 2) @ 3) @ 4) @ 100).\n"
    ))

    return cases


def d9_higher_order() -> list[tuple[str, str]]:
    """D9: Higher-order specific edge cases."""
    cases = []

    # Boolean extensionality
    cases.append((
        "d9_bool_ext",
        "% D9: boolean extensionality\n"
        "thf(decl, type, p : $o).\n"
        "thf(decl2, type, q : $o).\n"
        "thf(ax, axiom, (p => q) & (q => p)).\n"
        "thf(conj, conjecture, p = q).\n"
    ))

    # Functional extensionality
    cases.append((
        "d9_func_ext",
        "% D9: functional extensionality\n"
        "thf(decl_f, type, f : $i > $i).\n"
        "thf(decl_g, type, g : $i > $i).\n"
        "thf(ax, axiom, ![X:$i]: ((f @ X) = (g @ X))).\n"
        "thf(conj, conjecture, f = g).\n"
    ))

    # Lambda with capture
    cases.append((
        "d9_lambda_capture",
        "% D9: lambda with variable capture scenario\n"
        "thf(decl, type, f : $i > $i > $o).\n"
        "thf(decl2, type, a : $i).\n"
        "thf(conj, conjecture, (^[X:$i]: (^[Y:$i]: (f @ X @ Y))) @ a @ a).\n"
    ))

    # Nested quantifiers with higher-order
    cases.append((
        "d9_nested_quant_ho",
        "% D9: nested quantifiers in HO context\n"
        "thf(decl, type, p : $i > $i > $o).\n"
        "thf(conj, conjecture, "
        "(![X:$i]: ?[Y:$i]: (p @ X @ Y)) => (?[F:$i > $i]: ![X:$i]: (p @ X @ (F @ X)))).\n"
    ))

    # Choice axiom
    cases.append((
        "d9_choice",
        "% D9: choice principle\n"
        "thf(decl, type, p : $i > $o).\n"
        "thf(ax, axiom, ?[X:$i]: (p @ X)).\n"
        "thf(conj, conjecture, p @ (@@+ @ (^[X:$i]: (p @ X)))).\n"
    ))

    return cases


def d10_sledgehammer_like() -> list[tuple[str, str]]:
    """D10: Realistic Sledgehammer-like problems."""
    cases = []

    # Group theory axioms (common in Isabelle)
    cases.append((
        "d10_group_theory",
        "% D10: group theory axioms\n"
        "thf(decl_g, type, g : $tType).\n"
        "thf(decl_op, type, op : g > g > g).\n"
        "thf(decl_inv, type, inv : g > g).\n"
        "thf(decl_e, type, e : g).\n"
        "thf(ax_assoc, axiom, ![X:g, Y:g, Z:g]: ((op @ (op @ X @ Y) @ Z) = (op @ X @ (op @ Y @ Z)))).\n"
        "thf(ax_id_l, axiom, ![X:g]: ((op @ e @ X) = X)).\n"
        "thf(ax_inv_l, axiom, ![X:g]: ((op @ (inv @ X) @ X) = e)).\n"
        "thf(conj, conjecture, ![X:g]: ((op @ X @ e) = X)).\n"
    ))

    # Nat-like induction pattern
    cases.append((
        "d10_nat_induction",
        "% D10: natural number induction pattern\n"
        "thf(decl_nat, type, nat : $tType).\n"
        "thf(decl_zero, type, zero : nat).\n"
        "thf(decl_suc, type, suc : nat > nat).\n"
        "thf(decl_plus, type, plus : nat > nat > nat).\n"
        "thf(ax_plus_z, axiom, ![X:nat]: ((plus @ X @ zero) = X)).\n"
        "thf(ax_plus_s, axiom, ![X:nat, Y:nat]: ((plus @ X @ (suc @ Y)) = (suc @ (plus @ X @ Y)))).\n"
        "thf(conj, conjecture, ![X:nat]: ((plus @ zero @ X) = X)).\n"
    ))

    # Many background axioms (typical Sledgehammer problem)
    bg_axioms = []
    for i in range(50):
        bg_axioms.append(
            f"thf(bg{i}, axiom, ![X:$i]: ((f{i} @ X) = (f{(i+1) % 50} @ X)))."
        )
    decls = "\n".join([f"thf(df{i}, type, f{i} : $i > $i)." for i in range(50)])
    cases.append((
        "d10_many_bg_axioms",
        f"% D10: many background axioms (Sledgehammer-like)\n"
        f"thf(decl_a, type, a : $i).\n"
        f"{decls}\n"
        f"{chr(10).join(bg_axioms)}\n"
        f"thf(conj, conjecture, (f0 @ a) = (f49 @ a)).\n"
    ))

    # Mixed quantifier problem
    cases.append((
        "d10_mixed_quant",
        "% D10: mixed quantifier Skolemization stress\n"
        "thf(decl_r, type, r : $i > $i > $o).\n"
        "thf(ax, axiom, ![X:$i]: ?[Y:$i]: ![Z:$i]: ?[W:$i]: (r @ X @ Y) & (r @ Z @ W)).\n"
        "thf(conj, conjecture, ?[F: $i > $i]: ![X:$i]: (r @ X @ (F @ X))).\n"
    ))

    return cases


# ═══════════════════════════════════════════════════════════════════════
#  RUNNER (same as targeted_fuzz.py)
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class FuzzResult:
    file: str
    target: str
    exit_code: int
    timed_out: bool
    output: str
    bug_type: str
    is_new_bug: bool
    description: str


def run_zp(zp: str, filepath: Path, timeout: int = 30) -> tuple[int, str, bool]:
    cmd = [zp, "--input", "tptp", "--output", "none", "--timeout", "20",
           "--steps", "5000", str(filepath)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return proc.returncode, (proc.stdout + proc.stderr)[:2000], False
    except subprocess.TimeoutExpired:
        return -1, "TIMEOUT", True
    except Exception as e:
        return -2, f"EXCEPTION: {e}", False


def classify_output(name: str, exit_code: int, output: str, timed_out: bool) -> FuzzResult:
    target = name.split("_")[0]

    if timed_out:
        return FuzzResult(name, target, exit_code, True, output[:500],
                          "hang", True, "Timed out — potential hang")

    out_lower = output.lower()

    if "parse error" in out_lower or "syntax error" in out_lower:
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "parse_error", False, f"Parse error (exit {exit_code})")

    # Uncaught exception / crash — THE MAIN TARGET
    if re.search(r'Failure\(|Fatal|Segmentation|Stack_overflow', output):
        exc_match = re.search(r'(Failure\([^)]*\)|Fatal[^\n]*|Stack_overflow)', output)
        exc_text = exc_match.group(0) if exc_match else "unknown exception"
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "crash", True, f"CRASH: {exc_text}")

    if re.search(r'Invalid_argument', output):
        exc_match = re.search(r'Invalid_argument\([^)]*\)', output)
        exc_text = exc_match.group(0) if exc_match else "Invalid_argument"
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "crash", True, f"CRASH: {exc_text}")

    if "assert" in out_lower and exit_code != 0:
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "crash", True, f"CRASH: assertion failure (exit {exit_code})")

    if "not a proper tptp role" in out_lower:
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "crash", True, "CRASH: failwith in role_of_string")

    if "error" in out_lower and exit_code != 0:
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "error_graceful", False, f"Graceful error (exit {exit_code})")

    if exit_code == 0:
        status = "unknown"
        if "theorem" in out_lower:
            status = "Theorem"
        elif "satisfiable" in out_lower or "gaveup" in out_lower or "gave up" in out_lower:
            status = "GaveUp/Sat"
        elif "timeout" in out_lower:
            status = "Timeout"
        return FuzzResult(name, target, exit_code, False, output[:300],
                          "ok", False, f"OK ({status})")

    return FuzzResult(name, target, exit_code, False, output[:500],
                      "error_graceful", False, f"Non-zero exit ({exit_code})")


def generate_all() -> list[tuple[str, str]]:
    all_cases = []
    all_cases.extend(d1_type_inference())
    all_cases.extend(d2_type_construction())
    all_cases.extend(d3_term_construction())
    all_cases.extend(d4_fragment_checking())
    all_cases.extend(d5_superposition_stress())
    all_cases.extend(d6_ordering_stress())
    all_cases.extend(d7_unification())
    all_cases.extend(d8_arithmetic())
    all_cases.extend(d9_higher_order())
    all_cases.extend(d10_sledgehammer_like())
    return all_cases


def cmd_generate(args):
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    cases = generate_all()
    for name, content in cases:
        (out / f"{name}.p").write_text(content, encoding="utf-8")
    print(f"[*] Generated {len(cases)} deep test cases → {out}")
    targets = {}
    for name, _ in cases:
        t = name.split("_")[0]
        targets[t] = targets.get(t, 0) + 1
    for t, count in sorted(targets.items()):
        print(f"    {t}: {count} cases")


def cmd_run(args):
    zp = args.zp
    input_dir = Path(args.input_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    files = sorted(input_dir.glob("*.p"))
    print(f"[*] Running {len(files)} deep test cases against {zp}")
    print(f"[*] Timeout: {args.timeout}s per test (deeper tests need more time)")

    results = []
    bugs = []

    for idx, f in enumerate(files, 1):
        name = f.stem
        exit_code, output, timed_out = run_zp(zp, f, timeout=args.timeout)
        result = classify_output(name, exit_code, output, timed_out)
        results.append(result)

        indicator = {
            "ok": ".", "parse_error": "P", "crash": "!",
            "hang": "H", "error_graceful": "e",
        }.get(result.bug_type, "?")
        print(indicator, end="", flush=True)
        if idx % 60 == 0:
            print(f"  [{idx}/{len(files)}]")

        if result.is_new_bug:
            bugs.append(result)

    print(f"\n\n{'='*60}")
    print(f"  DEEP FUZZING RESULTS: {len(results)} tests")
    print(f"{'='*60}")

    by_type = {}
    for r in results:
        by_type.setdefault(r.bug_type, []).append(r)

    for btype in ["crash", "hang", "parse_error", "error_graceful", "ok"]:
        items = by_type.get(btype, [])
        if items:
            print(f"\n  {btype}: {len(items)}")
            for r in items[:15]:
                marker = " ** NEW BUG **" if r.is_new_bug else ""
                print(f"    {r.file}: {r.description}{marker}")
            if len(items) > 15:
                print(f"    ... and {len(items) - 15} more")

    report = {
        "total": len(results),
        "summary": {k: len(v) for k, v in by_type.items()},
        "new_bugs": [asdict(b) for b in bugs],
        "all_results": [asdict(r) for r in results],
    }
    report_path = output_dir / "deep_fuzz_report.json"
    with open(report_path, "w") as fp:
        json.dump(report, fp, indent=2)

    summary_path = output_dir / "deep_fuzz_summary.txt"
    with open(summary_path, "w") as fp:
        fp.write(f"Deep Fuzzing Summary\n{'='*60}\n\n")
        fp.write(f"Total tests: {len(results)}\n")
        for btype, items in sorted(by_type.items()):
            fp.write(f"  {btype}: {len(items)}\n")
        fp.write(f"\nNew bugs/hangs found: {len(bugs)}\n\n")
        for b in bugs:
            fp.write(f"  [{b.target}] {b.file}\n")
            fp.write(f"    Type: {b.bug_type}\n")
            fp.write(f"    Desc: {b.description}\n")
            fp.write(f"    Exit: {b.exit_code}\n")
            fp.write(f"    Output: {b.output[:300]}\n\n")

    print(f"\n[*] Report: {report_path}")
    print(f"[*] Summary: {summary_path}")

    if bugs:
        print(f"\n{'!'*60}")
        print(f"  {len(bugs)} POTENTIAL NEW BUGS/HANGS FOUND!")
        print(f"{'!'*60}")
        for b in bugs:
            print(f"  [{b.target}] {b.file}: {b.description}")


def cmd_full(args):
    gen_dir = Path(args.output_dir) / "inputs"
    args_gen = argparse.Namespace(output_dir=str(gen_dir))
    cmd_generate(args_gen)
    args_run = argparse.Namespace(
        zp=args.zp, input_dir=str(gen_dir),
        output_dir=args.output_dir, timeout=args.timeout,
    )
    cmd_run(args_run)


def main():
    parser = argparse.ArgumentParser(
        description="Deep source-informed fuzzing for Zipperposition internals"
    )
    sub = parser.add_subparsers(dest="cmd")

    p_gen = sub.add_parser("generate")
    p_gen.add_argument("--output-dir", required=True)

    p_run = sub.add_parser("run")
    p_run.add_argument("--zp", default="zipperposition")
    p_run.add_argument("--timeout", type=int, default=30)
    p_run.add_argument("--input-dir", required=True)
    p_run.add_argument("--output-dir", default="./deep_results")

    p_full = sub.add_parser("full")
    p_full.add_argument("--zp", default="zipperposition")
    p_full.add_argument("--timeout", type=int, default=30)
    p_full.add_argument("--output-dir", default="./deep_results")

    args = parser.parse_args()
    if args.cmd == "generate":
        cmd_generate(args)
    elif args.cmd == "run":
        cmd_run(args)
    elif args.cmd == "full":
        cmd_full(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
