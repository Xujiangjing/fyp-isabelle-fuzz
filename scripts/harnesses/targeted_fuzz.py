#!/usr/bin/env python3
"""
targeted_fuzz.py — Source-informed targeted fuzzing for Zipperposition.

Based on reading Zipperposition's source code (Lex_tptp.mll, Parse_tptp.mly,
ast_tptp.ml, Term.ml, TypeInference.ml, Builtin.ml, STerm.ml, InnerTerm.ml),
this script generates TPTP inputs that target specific weak spots:

TARGET AREAS (with source file references):

  T1. KEYWORD COLLISION (EXTENDED) — Lex_tptp.mll:63-67, Parse_tptp.mly:491-493
      The `atomic_word` rule only accepts LOWER_WORD and SINGLE_QUOTED.
      Keywords fof/cnf/tff/thf/include get dedicated tokens and bypass LOWER_WORD.
      ALREADY CONFIRMED for symbol names. Now test in OTHER positions:
        - statement names:   thf(fof, type, ...)   ← name rule uses atomic_word
        - annotation data:   thf(..., ..., ..., fof). ← general_data uses atomic_word
        - general_function:  thf(..., ..., ..., fof(x)). ← also atomic_word
        - type_const:        thf(..., type, x: fof).  ← type_const uses atomic_word

  T2. ROLE PARSING — ast_tptp.ml:39-55
      `role_of_string` is an exhaustive match with `failwith` on unknown roles.
      The `role` rule requires LOWER_WORD. If we feed a non-standard role,
      it hits failwith("not a proper TPTP role: " ^ s).
      Test: non-standard roles like "fi_dontexist", "corollary", "claim", etc.

  T3. UNKNOWN $-BUILTINS — Parse_tptp.mly:385-388, Builtin.ml:433-484
      `defined_plain_term` calls Builtin.TPTP.of_string. If the $word is not
      recognized, it calls UntypedAST.errorf. Test with fake builtins:
      $nonexistent, $foo, $ite_t, $let_tf, etc.

  T4. TYPE SYSTEM EDGE CASES — TypeInference.ml, Type.ml
      Many `assert false` in type inference (lines 211, 377, 640, 661, 670, 703).
      Type.ml has crashes on malformed arrow types (line 44, 330, 362).
      Test: deeply nested types, polymorphic type mismatches, arrow with 0/1 args.

  T5. ARITHMETIC PARSING — Builtin.ml:277-281, 529-530
      Z.of_string and Q.of_string can crash on malformed input.
      Lexer should only pass valid numbers, but edge cases like very large
      integers, rationals with 0 denominator, etc. are worth testing.

  T6. $ite / LET / CONDITIONAL — Parse_tptp.mly:337-338, 391
      conditional_term and let_term are commented out in the parser.
      $ite IS partially supported (line 353-356), but let is not.
      Test: $ite with various arities, nested $ite, $let (should fail gracefully).

  T7. CHOICE OPERATORS — Lex_tptp.mll:81-82, Parse_tptp.mly:47-48
      @+ (CHOICE_BINDER) and @@+ (CHOICE_CONST) are tokenized.
      Test: choice in various positions, nested choice, choice with bad types.

  T8. DISTINCT OBJECTS — Lex_tptp.mll:21, Parse_tptp.mly:380-384
      Distinct objects use double quotes. Edge cases: empty string "",
      strings with escapes, very long strings, strings containing keywords.

  T9. EMPTY / MINIMAL FILES
      Empty file, file with only comments, file with single declaration.

  T10. MIXED FORMAT STRESS — use fof/cnf/tff/thf declarations in same file
       (valid TPTP but tests parser state handling).

Usage:
    python3 targeted_fuzz.py generate --output-dir ./targeted_inputs
    python3 targeted_fuzz.py run --zp /path/to/zipperposition --input-dir ./targeted_inputs
    python3 targeted_fuzz.py full --zp /path/to/zipperposition --output-dir ./targeted_results
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, asdict, field
from pathlib import Path
from typing import Optional


# ═══════════════════════════════════════════════════════════════════════
#  TEST CASE GENERATORS — one per target area
# ═══════════════════════════════════════════════════════════════════════

TPTP_KEYWORDS = ["fof", "cnf", "tff", "thf", "include"]


def t1_keyword_collision_extended() -> list[tuple[str, str]]:
    """T1: Keywords in every position where atomic_word is used."""
    cases = []

    for kw in TPTP_KEYWORDS:
        # 1a. Keyword as STATEMENT NAME (name rule uses atomic_word)
        cases.append((
            f"t1_name_{kw}",
            f"% T1: keyword '{kw}' as statement name\n"
            f"thf({kw}, type, some_sym : $o).\n"
            f"thf(test_{kw}, conjecture, some_sym).\n"
        ))

        # 1b. Keyword as TYPE CONSTANT name (type_const uses atomic_word)
        cases.append((
            f"t1_typeconst_{kw}",
            f"% T1: keyword '{kw}' as type constant\n"
            f"thf(decl_type, type, {kw} : $tType).\n"
            f"thf(decl_sym, type, mysym : {kw}).\n"
            f"thf(conj, conjecture, mysym = mysym).\n"
        ))

        # 1c. Keyword as FUNCTOR name (functor_ uses atomic_word)
        cases.append((
            f"t1_functor_{kw}",
            f"% T1: keyword '{kw}' as functor\n"
            f"thf(decl_f, type, {kw} : $o > $o).\n"
            f"thf(conj, conjecture, {kw}($true)).\n"
        ))

        # 1d. Keyword in ANNOTATION (general_data uses atomic_word)
        cases.append((
            f"t1_annotation_{kw}",
            f"% T1: keyword '{kw}' in annotation position\n"
            f"thf(test, axiom, $true, {kw}).\n"
        ))

        # 1e. Keyword in general_function in annotation
        cases.append((
            f"t1_genfunc_{kw}",
            f"% T1: keyword '{kw}' as general_function\n"
            f"thf(test, axiom, $true, {kw}(some_info)).\n"
        ))

        # 1f. Keyword as SYMBOL name in formula body (already confirmed bug)
        # But also test in fof/tff/cnf declarations (not just thf)
        for fmt in ["fof", "tff"]:
            cases.append((
                f"t1_body_{fmt}_{kw}",
                f"% T1: keyword '{kw}' in {fmt} formula body\n"
                f"{fmt}(test, axiom, {kw} = {kw}).\n"
            ))

        # 1g. Keyword as type_decl symbol (type_decl uses atomic_word)
        cases.append((
            f"t1_typedecl_{kw}",
            f"% T1: keyword '{kw}' in type declaration\n"
            f"tff(decl, type, {kw} : $i).\n"
        ))

        # 1h. Single-quoted workaround (should always work — control group)
        cases.append((
            f"t1_quoted_{kw}",
            f"% T1: single-quoted keyword '{kw}' (control - should work)\n"
            f"thf(test, type, '{kw}' : $o).\n"
            f"thf(conj, conjecture, '{kw}').\n"
        ))

    return cases


def t2_role_parsing() -> list[tuple[str, str]]:
    """T2: Non-standard and edge-case TPTP roles."""
    cases = []

    # Valid roles that should work
    valid_roles = [
        "axiom", "hypothesis", "definition", "assumption",
        "lemma", "theorem", "conjecture", "negated_conjecture",
        "plain", "type", "unknown",
        "fi_domain", "fi_functors", "fi_predicates",
    ]

    # Invalid roles — should trigger failwith in role_of_string
    invalid_roles = [
        "corollary", "claim", "fact", "rule", "goal",
        "declaration", "formula", "clause", "assertion",
        "fi_unknown",  # fi_ prefix but not recognized
    ]

    for role in invalid_roles:
        cases.append((
            f"t2_badrole_{role}",
            f"% T2: invalid role '{role}'\n"
            f"thf(test, {role}, $true).\n"
        ))

    # Role position with empty/weird strings
    cases.append((
        "t2_role_empty_quoted",
        "% T2: empty quoted string as role\n"
        "thf(test, '', $true).\n"
    ))

    return cases


def t3_unknown_builtins() -> list[tuple[str, str]]:
    """T3: Unknown $-prefixed builtins."""
    cases = []

    unknown_builtins = [
        "$nonexistent", "$foo", "$bar",
        "$ite_t", "$let_tf", "$let_ff",
        "$typeof", "$print", "$eval",
        "$pi", "$e", "$infinity",
        "$is_real", "$to_real",  # some exist, some don't
        "$select", "$store",  # array theory builtins (not in ZP)
    ]

    for b in unknown_builtins:
        cases.append((
            f"t3_builtin_{b.replace('$','')}",
            f"% T3: unknown builtin {b}\n"
            f"thf(test, conjecture, {b}).\n"
        ))

    # Builtin with arguments
    for b in ["$nonexistent", "$foo"]:
        cases.append((
            f"t3_builtin_args_{b.replace('$','')}",
            f"% T3: unknown builtin {b} with arguments\n"
            f"thf(test, conjecture, {b}($true, $false)).\n"
        ))

    # $$system words
    cases.append((
        "t3_system_word",
        "% T3: $$system words\n"
        "thf(test, conjecture, $$anything = $$anything).\n"
    ))

    return cases


def t4_type_edge_cases() -> list[tuple[str, str]]:
    """T4: Type system edge cases targeting assert false in TypeInference/Type."""
    cases = []

    # Deeply nested arrow types
    cases.append((
        "t4_deep_arrow",
        "% T4: deeply nested arrow type\n"
        "thf(decl, type, f : ($o > $o) > ($o > $o) > ($o > $o) > $o).\n"
        "thf(conj, conjecture, f = f).\n"
    ))

    # Polymorphic type with many variables
    cases.append((
        "t4_poly_many",
        "% T4: polymorphic type with many type variables\n"
        "thf(decl, type, f : !>[A:$tType, B:$tType, C:$tType]: (A > B > C > $o)).\n"
        "thf(conj, conjecture, f = f).\n"
    ))

    # Type applied to itself (higher-order type)
    cases.append((
        "t4_type_apply_self",
        "% T4: type constructor applied in unusual ways\n"
        "thf(decl_t, type, mytype : $tType > $tType).\n"
        "thf(decl_f, type, f : (mytype @ $o) > $o).\n"
        "thf(conj, conjecture, f = f).\n"
    ))

    # Function type as argument to function type
    cases.append((
        "t4_func_in_func",
        "% T4: function type as argument\n"
        "thf(decl, type, apply : ($o > $o) > $o > $o).\n"
        "thf(ax, axiom, ![F: $o > $o, X: $o]: (apply @ F @ X) = (F @ X)).\n"
        "thf(conj, conjecture, apply = apply).\n"
    ))

    # Prop-typed argument (triggers in_pfho_fragment checks)
    cases.append((
        "t4_prop_arg",
        "% T4: prop-typed term as argument (fragment check edge case)\n"
        "thf(decl, type, f : $o > $o > $o).\n"
        "thf(conj, conjecture, f @ $true @ $false).\n"
    ))

    # $distinct with various arities (assert false at line 703 if empty)
    cases.append((
        "t4_distinct_empty",
        "% T4: $distinct with no arguments (edge case)\n"
        "thf(conj, conjecture, $distinct()).\n"
    ))

    cases.append((
        "t4_distinct_one",
        "% T4: $distinct with one argument\n"
        "thf(decl, type, a : $i).\n"
        "thf(conj, conjecture, $distinct(a)).\n"
    ))

    cases.append((
        "t4_distinct_many",
        "% T4: $distinct with many arguments\n"
        "thf(d1, type, a : $i).\n"
        "thf(d2, type, b : $i).\n"
        "thf(d3, type, c : $i).\n"
        "thf(d4, type, d : $i).\n"
        "thf(d5, type, e : $i).\n"
        "thf(conj, conjecture, $distinct(a, b, c, d, e)).\n"
    ))

    # Int and Rat typed terms (excluded from pfho_fragment by type_ok)
    cases.append((
        "t4_int_rat_types",
        "% T4: $int and $rat types (type_ok rejects prop/rat/int)\n"
        "thf(decl_f, type, f : $int > $int).\n"
        "thf(decl_g, type, g : $rat > $rat).\n"
        "thf(ax, axiom, f @ 1 = f @ 1).\n"
        "thf(conj, conjecture, g @ 1/2 = g @ 1/2).\n"
    ))

    return cases


def t5_arithmetic_edge_cases() -> list[tuple[str, str]]:
    """T5: Edge cases in number parsing."""
    cases = []

    # Very large integer
    cases.append((
        "t5_huge_int",
        "% T5: very large integer\n"
        "thf(decl, type, f : $int > $o).\n"
        f"thf(conj, conjecture, f @ {'9' * 1000}).\n"
    ))

    # Zero denominator rational (lexer should reject, but...)
    cases.append((
        "t5_zero_denom",
        "% T5: rational with unusual denominator\n"
        "thf(decl, type, f : $rat > $o).\n"
        "thf(conj, conjecture, f @ 1/1).\n"
    ))

    # Negative numbers
    cases.append((
        "t5_negative",
        "% T5: negative numbers\n"
        "thf(decl, type, f : $int > $o).\n"
        "thf(conj, conjecture, f @ -42).\n"
    ))

    # Real number edge cases
    cases.append((
        "t5_real_edge",
        "% T5: real number edge cases\n"
        "thf(decl, type, f : $real > $o).\n"
        "thf(ax1, axiom, f @ 0.0).\n"
        "thf(ax2, axiom, f @ 1.0E100).\n"
        "thf(ax3, axiom, f @ -1.0E-100).\n"
        "thf(conj, conjecture, f @ 3.14).\n"
    ))

    return cases


def t6_ite_and_let() -> list[tuple[str, str]]:
    """T6: $ite (supported) and $let (not supported) edge cases."""
    cases = []

    # Basic $ite (should work)
    cases.append((
        "t6_ite_basic",
        "% T6: basic $ite\n"
        "thf(conj, conjecture, $ite($true, $true, $false)).\n"
    ))

    # Nested $ite
    cases.append((
        "t6_ite_nested",
        "% T6: nested $ite\n"
        "thf(conj, conjecture, $ite($ite($true, $true, $false), $true, $false)).\n"
    ))

    # $ite with wrong arity
    cases.append((
        "t6_ite_wrong_arity",
        "% T6: $ite with wrong number of arguments\n"
        "thf(conj, conjecture, $ite($true, $true)).\n"
    ))

    # $ite with 4 arguments
    cases.append((
        "t6_ite_four_args",
        "% T6: $ite with 4 arguments\n"
        "thf(conj, conjecture, $ite($true, $true, $false, $true)).\n"
    ))

    return cases


def t7_choice_operators() -> list[tuple[str, str]]:
    """T7: Choice operator edge cases."""
    cases = []

    cases.append((
        "t7_choice_basic",
        "% T7: basic choice\n"
        "thf(conj, conjecture, ?[X:$o]: X = (@@+ @ (^[X:$o]: X))).\n"
    ))

    cases.append((
        "t7_choice_binder",
        "% T7: choice binder\n"
        "thf(conj, conjecture, (@+[X:$o]: X) = $true).\n"
    ))

    cases.append((
        "t7_choice_nested",
        "% T7: nested choice\n"
        "thf(conj, conjecture, (@+[X:$o]: (@+[Y:$o]: X & Y)) = $true).\n"
    ))

    return cases


def t8_distinct_objects() -> list[tuple[str, str]]:
    """T8: Distinct object edge cases."""
    cases = []

    cases.append((
        "t8_distinct_basic",
        '% T8: basic distinct objects\n'
        'thf(conj, conjecture, "hello" != "world").\n'
    ))

    cases.append((
        "t8_distinct_escape",
        '% T8: distinct object with escapes\n'
        'thf(conj, conjecture, "hello\\\\" != "world").\n'
    ))

    cases.append((
        "t8_distinct_keyword",
        '% T8: distinct object containing keyword\n'
        'thf(conj, conjecture, "fof" != "cnf").\n'
    ))

    cases.append((
        "t8_distinct_long",
        '% T8: very long distinct object\n'
        f'thf(conj, conjecture, "{"a" * 10000}" != "b").\n'
    ))

    return cases


def t9_minimal_files() -> list[tuple[str, str]]:
    """T9: Empty / minimal / degenerate files."""
    cases = []

    cases.append(("t9_empty", ""))
    cases.append(("t9_only_comment", "% just a comment\n"))
    cases.append(("t9_only_newlines", "\n\n\n"))
    cases.append(("t9_single_decl", "thf(x, axiom, $true).\n"))
    cases.append(("t9_no_conjecture", "thf(x, axiom, $true).\nthf(y, axiom, $false).\n"))

    # Include directive (file won't exist — should it crash or error gracefully?)
    cases.append((
        "t9_include_nonexistent",
        "include('nonexistent_file.ax').\n"
    ))

    return cases


def t10_mixed_format() -> list[tuple[str, str]]:
    """T10: Mixed fof/cnf/tff/thf in same file."""
    cases = []

    cases.append((
        "t10_mixed_all",
        "% T10: all four formats in one file\n"
        "thf(t1, type, p : $o).\n"
        "thf(t2, axiom, p).\n"
        "tff(t3, type, q : $o).\n"
        "tff(t4, axiom, q).\n"
        "fof(t5, axiom, r).\n"
        "cnf(t6, axiom, s | t).\n"
        "thf(conj, conjecture, p).\n"
    ))

    cases.append((
        "t10_cnf_thf_mix",
        "% T10: cnf and thf mixed\n"
        "thf(t1, type, p : $o).\n"
        "cnf(c1, axiom, p).\n"
        "thf(conj, conjecture, p).\n"
    ))

    # THF declaration referencing FOF-style syntax
    cases.append((
        "t10_fof_style_in_thf",
        "% T10: FOF-style quantification in THF context\n"
        "thf(decl, type, f : $i > $o).\n"
        "thf(ax, axiom, ![X:$i]: f @ X).\n"
        "thf(conj, conjecture, ?[X:$i]: f @ X).\n"
    ))

    return cases


def t11_sledgehammer_realistic() -> list[tuple[str, str]]:
    """T11: Patterns that mimic real Sledgehammer output with adversarial twists."""
    cases = []

    # Long mangled symbol names (like Sledgehammer generates)
    cases.append((
        "t11_long_symbols",
        "% T11: very long mangled symbol names\n"
        f"thf(t1, type, {'a' * 200} : $o).\n"
        f"thf(t2, type, {'b' * 200} : $o).\n"
        f"thf(conj, conjecture, {'a' * 200} = {'b' * 200}).\n"
    ))

    # Many type declarations (stress test)
    lines = ["% T11: many type declarations"]
    for i in range(500):
        lines.append(f"thf(d{i}, type, sym_{i} : $o).")
    lines.append(f"thf(conj, conjecture, sym_0).")
    cases.append(("t11_many_decls", "\n".join(lines) + "\n"))

    # Deeply nested application
    core = "$true"
    for i in range(50):
        core = f"(^ [X{i}:$o]: X{i}) @ ({core})"
    cases.append((
        "t11_deep_lambda_app",
        f"% T11: deeply nested lambda application\n"
        f"thf(conj, conjecture, {core}).\n"
    ))

    return cases


# ═══════════════════════════════════════════════════════════════════════
#  RUNNER
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class FuzzResult:
    file: str
    target: str           # T1, T2, etc.
    exit_code: int
    timed_out: bool
    output: str
    bug_type: str         # parse_error | crash | hang | ok | error_graceful
    is_new_bug: bool      # True if this seems like a genuine new bug
    description: str


def run_zp(zp: str, filepath: Path, timeout: int = 15) -> tuple[int, str, bool]:
    """Run Zipperposition on a file. Returns (exit_code, output, timed_out)."""
    cmd = [zp, "--input", "tptp", "--output", "none", "--timeout", "10",
           "--steps", "1000", str(filepath)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return proc.returncode, (proc.stdout + proc.stderr)[:2000], False
    except subprocess.TimeoutExpired:
        return -1, "TIMEOUT", True
    except Exception as e:
        return -2, f"EXCEPTION: {e}", False


def classify_output(name: str, exit_code: int, output: str, timed_out: bool) -> FuzzResult:
    """Classify the result of running a test case."""
    target = name.split("_")[0]  # e.g. "t1" from "t1_name_fof"

    if timed_out:
        return FuzzResult(name, target, exit_code, True, output[:500],
                          "hang", False, "Timed out")

    out_lower = output.lower()

    # Parse error
    if "parse error" in out_lower or "syntax error" in out_lower:
        # For T1 keyword tests, parse errors on bare keywords are the known bug
        is_new = target not in ("t1",)  # T1 is already known
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "parse_error", is_new,
                          f"Parse error (exit {exit_code})")

    # Uncaught exception / crash
    if re.search(r'Failure\(|Fatal|Segmentation|assert|Invalid_argument|Stack_overflow', output):
        exc_match = re.search(r'(Failure\([^)]+\)|Fatal[^\n]+|Invalid_argument[^\n]+|Stack_overflow)', output)
        exc_text = exc_match.group(0) if exc_match else "unknown exception"
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "crash", True,
                          f"Crash: {exc_text}")

    # Graceful error (errorf from parser)
    if "error" in out_lower and exit_code != 0:
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "error_graceful", False,
                          f"Graceful error (exit {exit_code})")

    # failwith from role_of_string
    if "not a proper tptp role" in out_lower:
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "crash", True,
                          "Uncaught failwith in role_of_string")

    # Unknown builtin
    if "unknown builtin" in out_lower:
        return FuzzResult(name, target, exit_code, False, output[:500],
                          "error_graceful", False,
                          "Unknown builtin (graceful error)")

    # Success
    if exit_code == 0:
        return FuzzResult(name, target, exit_code, False, output[:200],
                          "ok", False, "OK")

    # Non-zero exit but no clear error
    return FuzzResult(name, target, exit_code, False, output[:500],
                      "error_graceful", False,
                      f"Non-zero exit ({exit_code}), no crash detected")


# ═══════════════════════════════════════════════════════════════════════
#  COMMANDS
# ═══════════════════════════════════════════════════════════════════════

def generate_all() -> list[tuple[str, str]]:
    """Generate all test cases."""
    all_cases = []
    all_cases.extend(t1_keyword_collision_extended())
    all_cases.extend(t2_role_parsing())
    all_cases.extend(t3_unknown_builtins())
    all_cases.extend(t4_type_edge_cases())
    all_cases.extend(t5_arithmetic_edge_cases())
    all_cases.extend(t6_ite_and_let())
    all_cases.extend(t7_choice_operators())
    all_cases.extend(t8_distinct_objects())
    all_cases.extend(t9_minimal_files())
    all_cases.extend(t10_mixed_format())
    all_cases.extend(t11_sledgehammer_realistic())
    return all_cases


def cmd_generate(args):
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    cases = generate_all()
    for name, content in cases:
        (out / f"{name}.p").write_text(content, encoding="utf-8")

    print(f"[*] Generated {len(cases)} targeted test cases → {out}")

    # Print breakdown
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
    print(f"[*] Running {len(files)} test cases against {zp}")

    results = []
    bugs = []

    for idx, f in enumerate(files, 1):
        name = f.stem
        exit_code, output, timed_out = run_zp(zp, f, timeout=args.timeout)
        result = classify_output(name, exit_code, output, timed_out)
        results.append(result)

        indicator = {
            "ok": ".",
            "parse_error": "P",
            "crash": "!",
            "hang": "H",
            "error_graceful": "e",
        }.get(result.bug_type, "?")

        print(indicator, end="", flush=True)
        if idx % 60 == 0:
            print(f"  [{idx}/{len(files)}]")

        if result.is_new_bug:
            bugs.append(result)

    print(f"\n\n{'='*60}")
    print(f"  RESULTS: {len(results)} tests")
    print(f"{'='*60}")

    # Summary by type
    by_type = {}
    for r in results:
        by_type.setdefault(r.bug_type, []).append(r)

    for btype in ["crash", "parse_error", "hang", "error_graceful", "ok"]:
        items = by_type.get(btype, [])
        if items:
            print(f"\n  {btype}: {len(items)}")
            for r in items[:10]:
                marker = " ** NEW BUG **" if r.is_new_bug else ""
                print(f"    {r.file}: {r.description}{marker}")
            if len(items) > 10:
                print(f"    ... and {len(items) - 10} more")

    # Write detailed report
    report = {
        "total": len(results),
        "summary": {k: len(v) for k, v in by_type.items()},
        "new_bugs": [asdict(b) for b in bugs],
        "all_results": [asdict(r) for r in results],
    }
    report_path = output_dir / "targeted_fuzz_report.json"
    with open(report_path, "w") as fp:
        json.dump(report, fp, indent=2)

    # Write human-readable summary
    summary_path = output_dir / "targeted_fuzz_summary.txt"
    with open(summary_path, "w") as fp:
        fp.write(f"Targeted Fuzzing Summary\n{'='*60}\n\n")
        fp.write(f"Total tests: {len(results)}\n")
        for btype, items in sorted(by_type.items()):
            fp.write(f"  {btype}: {len(items)}\n")
        fp.write(f"\nNew bugs found: {len(bugs)}\n\n")
        for b in bugs:
            fp.write(f"  [{b.target}] {b.file}\n")
            fp.write(f"    Type: {b.bug_type}\n")
            fp.write(f"    Description: {b.description}\n")
            fp.write(f"    Exit code: {b.exit_code}\n")
            fp.write(f"    Output: {b.output[:300]}\n\n")

    print(f"\n[*] Report: {report_path}")
    print(f"[*] Summary: {summary_path}")

    if bugs:
        print(f"\n{'!'*60}")
        print(f"  {len(bugs)} POTENTIAL NEW BUGS FOUND!")
        print(f"{'!'*60}")
        for b in bugs:
            print(f"  [{b.target}] {b.file}: {b.description}")
    else:
        print("\n[*] No new bugs found in this run.")


def cmd_full(args):
    """Generate + run in one command."""
    gen_dir = Path(args.output_dir) / "inputs"
    args.output_dir_orig = args.output_dir

    # Generate
    args_gen = argparse.Namespace(output_dir=str(gen_dir))
    cmd_generate(args_gen)

    # Run
    args_run = argparse.Namespace(
        zp=args.zp,
        input_dir=str(gen_dir),
        output_dir=args.output_dir_orig,
        timeout=args.timeout,
    )
    cmd_run(args_run)


def main():
    parser = argparse.ArgumentParser(
        description="Source-informed targeted fuzzing for Zipperposition"
    )
    sub = parser.add_subparsers(dest="cmd")

    p_gen = sub.add_parser("generate", help="Generate targeted test cases")
    p_gen.add_argument("--output-dir", required=True)

    p_run = sub.add_parser("run", help="Run test cases against Zipperposition")
    p_run.add_argument("--zp", default="zipperposition")
    p_run.add_argument("--timeout", type=int, default=15)
    p_run.add_argument("--input-dir", required=True)
    p_run.add_argument("--output-dir", default="./targeted_results")

    p_full = sub.add_parser("full", help="Generate + run")
    p_full.add_argument("--zp", default="zipperposition")
    p_full.add_argument("--timeout", type=int, default=15)
    p_full.add_argument("--output-dir", default="./targeted_results")

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