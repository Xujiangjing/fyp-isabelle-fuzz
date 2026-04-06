#!/usr/bin/env python3
"""
edge_case_generator.py — Generate handcrafted TPTP edge cases to stress-test
Zipperposition's parser and type-checker.

Categories:
  1. Symbol name edge cases (keywords, special chars, length)
  2. Type system edge cases (deep nesting, polymorphism, higher-order)
  3. Formula structure edge cases (deep nesting, empty, degenerate)
  4. Annotation field edge cases (source, useful_info)
  5. Mixed dialect edge cases (thf/tff/fof in same file)
  6. Encoding edge cases (Unicode, whitespace, line endings)
"""

import os
from pathlib import Path

CASES = {}

# ══════════════════════════════════════════════════════════════════════
#  Category 1: Symbol name edge cases
# ══════════════════════════════════════════════════════════════════════

# 1a. TPTP keywords as symbol names (your confirmed bug — extend to more keywords)
CASES["kw_fof"] = """\
thf(t1, type, fof: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (fof = b)).
"""

CASES["kw_tff"] = """\
thf(t1, type, tff: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (tff = b)).
"""

CASES["kw_cnf"] = """\
thf(t1, type, cnf: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (cnf = b)).
"""

CASES["kw_thf"] = """\
thf(t1, type, thf: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (thf = b)).
"""

CASES["kw_include"] = """\
thf(t1, type, include: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (include = b)).
"""

CASES["kw_tcf"] = """\
thf(t1, type, tcf: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (tcf = b)).
"""

# 1b. TPTP role names as symbol names
CASES["role_axiom"] = """\
thf(t1, type, axiom: $i).
thf(t2, type, b: $i).
thf(ax1, axiom, (axiom = b)).
thf(conj, conjecture, (axiom = b)).
"""

CASES["role_type"] = """\
thf(t1, type, type: $i).
thf(conj, conjecture, (type = type)).
"""

CASES["role_conjecture"] = """\
thf(t1, type, conjecture: $i).
thf(conj, conjecture, (conjecture = conjecture)).
"""

# 1c. Built-in symbols as user symbols
CASES["builtin_true"] = """\
thf(t1, type, true: $i).
thf(conj, conjecture, (true = true)).
"""

CASES["builtin_false"] = """\
thf(t1, type, false: $i).
thf(conj, conjecture, (false = false)).
"""

# 1d. Single character names
CASES["single_char"] = """\
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(t3, type, c: $i).
thf(t4, type, o: $i).
thf(t5, type, i: $i).
thf(t6, type, p: $i > $o).
thf(conj, conjecture, (a = b)).
"""

# 1e. Very long symbol name
CASES["long_name"] = """\
thf(t1, type, %s: $i).
thf(conj, conjecture, (%s = %s)).
""" % ("a" * 1000, "a" * 1000, "a" * 1000)

# 1f. Name starting with underscore
CASES["underscore_name"] = """\
thf(t1, type, _hidden: $i).
thf(conj, conjecture, (_hidden = _hidden)).
"""

# 1g. Name with digits only (after first lowercase letter)
CASES["numeric_name"] = """\
thf(t1, type, x0123456789: $i).
thf(conj, conjecture, (x0123456789 = x0123456789)).
"""

# ══════════════════════════════════════════════════════════════════════
#  Category 2: Type system edge cases
# ══════════════════════════════════════════════════════════════════════

# 2a. Deeply nested function types
CASES["deep_func_type"] = """\
thf(t1, type, f: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $i).
thf(t2, type, a: $i).
thf(conj, conjecture, ((f @ a @ a @ a @ a @ a @ a @ a @ a @ a @ a) = a)).
"""

# 2b. Higher-order: function returning function
CASES["ho_func_return"] = """\
thf(t1, type, f: $i > ($i > $i)).
thf(t2, type, a: $i).
thf(conj, conjecture, ((f @ a @ a) = a)).
"""

# 2c. Predicate returning $o
CASES["pred_type"] = """\
thf(t1, type, p: $i > $o).
thf(t2, type, a: $i).
thf(conj, conjecture, (p @ a)).
"""

# 2d. Type with $tType (type constructor)
CASES["type_constructor"] = """\
thf(t1, type, list: $tType > $tType).
thf(t2, type, nat: $tType).
thf(t3, type, nil: (list @ nat)).
thf(t4, type, cons: nat > (list @ nat) > (list @ nat)).
thf(t5, type, a: nat).
thf(conj, conjecture, ((cons @ a @ nil) = (cons @ a @ nil))).
"""

# 2e. Polymorphic type
CASES["polymorphic"] = """\
thf(t1, type, id: !>[A: $tType]: (A > A)).
thf(t2, type, a: $i).
thf(conj, conjecture, ((id @ $i @ a) = a)).
"""

# 2f. Boolean as first-class type
CASES["bool_firstclass"] = """\
thf(t1, type, f: $o > $i).
thf(t2, type, a: $i).
thf(conj, conjecture, ((f @ $true) = a)).
"""

# ══════════════════════════════════════════════════════════════════════
#  Category 3: Formula structure edge cases
# ══════════════════════════════════════════════════════════════════════

# 3a. Deeply nested formula
CASES["deep_nesting"] = """\
thf(t1, type, p: $o).
thf(conj, conjecture, (((((((((p <=> p) <=> p) <=> p) <=> p) <=> p) <=> p) <=> p) <=> p) <=> p)).
"""

# 3b. $true as conjecture
CASES["trivial_true"] = """\
thf(conj, conjecture, $true).
"""

# 3c. $false as conjecture
CASES["trivial_false"] = """\
thf(conj, conjecture, $false).
"""

# 3d. Empty quantification domain
CASES["empty_quant"] = """\
thf(t1, type, a: $i).
thf(conj, conjecture, (![]: (a = a))).
"""

# 3e. Nested quantifiers same variable
CASES["shadow_var"] = """\
thf(conj, conjecture, (![X: $i]: (![X: $i]: (X = X)))).
"""

# 3f. Lambda in formula
CASES["lambda_formula"] = """\
thf(t1, type, f: ($i > $i) > $i).
thf(t2, type, a: $i).
thf(conj, conjecture, ((f @ (^[X: $i]: X)) = a)).
"""

# 3g. Applied lambda
CASES["applied_lambda"] = """\
thf(t1, type, a: $i).
thf(conj, conjecture, ((^[X: $i]: X) @ a) = a).
"""

# 3h. Very large disjunction
CASES["large_disjunction"] = """\
thf(t1, type, p: $i > $o).
""" + "".join(f"thf(t{i+2}, type, a{i}: $i).\n" for i in range(50)) + """\
thf(conj, conjecture, (""" + " | ".join(f"(p @ a{i})" for i in range(50)) + """)).
"""

# 3i. If-then-else (ITE)
CASES["ite_formula"] = """\
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, ($ite($true, a, b) = a)).
"""

# 3j. Let expression
CASES["let_formula"] = """\
thf(t1, type, a: $i).
thf(conj, conjecture, ($let(f: $i > $i, f = (^[X:$i]: X), (f @ a)) = a)).
"""

# ══════════════════════════════════════════════════════════════════════
#  Category 4: Annotation edge cases
# ══════════════════════════════════════════════════════════════════════

# 4a. Empty source list (Isabelle style)
CASES["annot_empty_source"] = """\
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(ax1, axiom, (a = b), []).
thf(conj, conjecture, (a = b)).
"""

# 4b. Source with useful_info
CASES["annot_useful_info"] = """\
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(ax1, axiom, (a = b), [], [some_info, other_info]).
thf(conj, conjecture, (a = b)).
"""

# 4c. File source annotation
CASES["annot_file_source"] = """\
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(ax1, axiom, (a = b), file('test.p', ax1)).
thf(conj, conjecture, (a = b)).
"""

# 4d. Inference annotation
CASES["annot_inference"] = """\
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(ax1, axiom, (a = b)).
thf(ax2, axiom, (a = b), inference(magic, [status(thm)], [ax1])).
thf(conj, conjecture, (a = b)).
"""

# 4e. Nested annotation lists
CASES["annot_nested_list"] = """\
thf(t1, type, a: $i).
thf(ax1, axiom, (a = a), [], [[nested, [deep, [deeper]]]]).
thf(conj, conjecture, (a = a)).
"""

# 4f. Isabelle-style annotation (real world)
CASES["annot_isabelle_style"] = """\
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(fact_0, axiom,
    (a = b), [], [isabelle_non_rec_def, isabelle_rank(900)]).
thf(conj, conjecture, (a = b)).
"""

# ══════════════════════════════════════════════════════════════════════
#  Category 5: Mixed dialect edge cases
# ══════════════════════════════════════════════════════════════════════

# 5a. Mix thf and tff
CASES["mixed_thf_tff"] = """\
tff(t1, type, a: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (a = b)).
"""

# 5b. Mix thf and fof
CASES["mixed_thf_fof"] = """\
fof(ax1, axiom, a = b).
thf(t1, type, a: $i).
thf(t2, type, b: $i).
thf(conj, conjecture, (a = b)).
"""

# 5c. CNF clause in THF file
CASES["mixed_cnf_thf"] = """\
cnf(ax1, axiom, p(a)).
thf(t1, type, a: $i).
thf(t2, type, p: $i > $o).
thf(conj, conjecture, (p @ a)).
"""

# ══════════════════════════════════════════════════════════════════════
#  Category 6: Whitespace and encoding edge cases
# ══════════════════════════════════════════════════════════════════════

# 6a. No newlines (everything on one line)
CASES["one_line"] = (
    "thf(t1, type, a: $i). "
    "thf(t2, type, b: $i). "
    "thf(conj, conjecture, (a = b))."
)

# 6b. Excessive whitespace
CASES["extra_whitespace"] = """\
thf(  t1  ,  type  ,  a  :  $i  )  .
thf(  t2  ,  type  ,  b  :  $i  )  .
thf(  conj  ,  conjecture  ,  (  a  =  b  )  )  .
"""

# 6c. Tab characters
CASES["tabs"] = "thf(t1,\ttype,\ta:\t$i).\nthf(conj,\tconjecture,\t(a\t=\ta)).\n"

# 6d. Empty file
CASES["empty_file"] = ""

# 6e. Only comments
CASES["only_comments"] = """\
% This file has no declarations
% Just comments
% Nothing to prove
"""

# 6f. Statement name with dots/special chars in quoted form
CASES["quoted_name"] = """\
thf('my.weird.name', type, a: $i).
thf('another-name', type, b: $i).
thf('name with spaces', conjecture, (a = b)).
"""

# 6g. Duplicate declaration names
CASES["duplicate_names"] = """\
thf(t1, type, a: $i).
thf(t1, type, b: $i).
thf(t1, conjecture, (a = b)).
"""

# 6h. Very long line
CASES["long_line"] = (
    "thf(t1, type, a: $i).\n"
    "thf(conj, conjecture, (" + " & ".join(["(a = a)"] * 200) + ")).\n"
)


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Generate TPTP edge cases")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--zp", default=None, help="If provided, run each case and report results")
    parser.add_argument("--timeout", type=int, default=10)
    args = parser.parse_args()

    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    for name, content in sorted(CASES.items()):
        (out / f"edge_{name}.p").write_text(content, encoding="utf-8")

    print(f"[*] Generated {len(CASES)} edge case files → {out}")

    if args.zp:
        import subprocess
        print(f"\n[*] Running Zipperposition on all edge cases...\n")

        crashes = []
        parse_errors = []
        unexpected = []

        for name in sorted(CASES.keys()):
            f = out / f"edge_{name}.p"
            try:
                proc = subprocess.run(
                    [args.zp, "--input", "tptp", "--output", "tptp",
                     "--timeout", str(args.timeout), str(f)],
                    capture_output=True, text=True, timeout=args.timeout + 5
                )
                output = proc.stdout + proc.stderr
                exit_code = proc.returncode

                # Extract SZS status
                import re
                m = re.search(r"SZS status\s+(\w+)", output)
                szs = m.group(1) if m else "NoStatus"

                # Detect issues
                has_crash = bool(re.search(r"Failure\(|exception|Fatal|Segmentation", output))
                has_parse = "parse error" in output.lower()

                status = f"exit={exit_code} SZS={szs}"
                if has_crash:
                    status += " *** CRASH ***"
                    crashes.append((name, output[:300]))
                elif has_parse:
                    status += " [parse error]"
                    parse_errors.append((name, output[:300]))
                elif exit_code not in (0, 1) and szs not in ("Theorem", "CounterSatisfiable",
                    "Satisfiable", "Unknown", "GaveUp", "ResourceOut", "Timeout"):
                    status += " [unexpected]"
                    unexpected.append((name, output[:300]))

                print(f"  {name:30s} {status}")

            except subprocess.TimeoutExpired:
                print(f"  {name:30s} *** TIMEOUT ***")
                crashes.append((name, "TIMEOUT"))

        print(f"\n{'='*60}")
        print(f"SUMMARY")
        print(f"{'='*60}")
        print(f"  Total cases:   {len(CASES)}")
        print(f"  Crashes:       {len(crashes)}")
        print(f"  Parse errors:  {len(parse_errors)}")
        print(f"  Unexpected:    {len(unexpected)}")

        if crashes:
            print(f"\nCRASHES:")
            for name, out in crashes:
                print(f"  {name}: {out[:200]}")

        if parse_errors:
            print(f"\nPARSE ERRORS:")
            for name, out in parse_errors:
                print(f"  {name}: {out[:200]}")


if __name__ == "__main__":
    main()
