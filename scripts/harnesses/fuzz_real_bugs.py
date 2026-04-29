#!/usr/bin/env python3
"""
fuzz_real_bugs.py — Find genuine bugs in Zipperposition's normal operation modes.

Bug types we look for:
  1. CRASH:     Zipperposition throws an exception or segfaults on valid TPTP input
  2. SOUNDNESS: Zipperposition claims "Theorem" on a known NON-theorem
  3. HANG:      Zipperposition does not terminate in reasonable time
  4. PARSE:     Zipperposition fails to parse valid TPTP (e.g. keyword collision)

Strategy:
  - Generate .thy files with a mix of TRUE and FALSE lemmas
  - Export via Sledgehammer to get .p files
  - Run Zipperposition in normal mode (as Sledgehammer would)
  - Check: does ZP crash? does ZP claim "Theorem" on a false lemma?

Usage:
    # Generate test theories with true/false lemmas
    python3 fuzz_real_bugs.py generate --output-dir ~/fyp-isabelle-fuzz/soundness_session --count 10

    # Test existing .p files for crashes in normal mode
    python3 fuzz_real_bugs.py test-crash --zp /path/to/zipperposition --input-dir ~/fyp-isabelle-fuzz/unique_inputs

    # Test existing .p files with various Zipperposition flag combinations
    python3 fuzz_real_bugs.py test-flags --zp /path/to/zipperposition --input-dir ~/fyp-isabelle-fuzz/unique_inputs
"""

import argparse
import json
import random
import re
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Optional


# ── Lemma templates ──────────────────────────────────────────────────

# TRUE lemmas: always provable
TRUE_LEMMAS = [
    # Arithmetic
    ('"{v} + 0 = ({v}::nat)"', "true"),
    ('"({v}::nat) + {w} = {w} + {v}"', "true"),
    ('"({v}::nat) * 1 = {v}"', "true"),
    ('"0 + ({v}::nat) = {v}"', "true"),
    ('"({v}::nat) \\<le> {v}"', "true"),
    ('"({v}::nat) < {v} + 1"', "true"),
    # Lists
    ('"length [{v}] = (1::nat)"', "true"),
    ('"hd [{v}] = ({v}::nat)"', "true"),
    ('"rev (rev xs) = (xs::nat list)"', "true"),
    ('"length (xs @ ys) = length xs + length (ys::nat list)"', "true"),
    # Logic
    ('"({v}::nat) = {v} \\<or> False"', "true"),
    ('"True \\<longrightarrow> ({v}::nat) = {v}"', "true"),
    # Sets — avoid curly braces (conflict with Python format)
    ('"({v}::nat) \\<in> set [{v}, {w}]"', "true"),
    ('"set [{v}, {w}] = set [{w}, ({v}::nat)]"', "true"),
]

# FALSE lemmas: should NEVER be provable
# If Zipperposition claims "Theorem" on these, that's a soundness bug
FALSE_LEMMAS = [
    ('"(0::nat) = 1"', "false"),
    ('"(0::nat) = Suc 0"', "false"),
    ('"Suc ({v}::nat) = {v}"', "false"),
    ('"({v}::nat) + 1 = {v}"', "false"),
    ('"({v}::nat) < {v}"', "false"),
    ('"length ([(1::nat)]) = 0"', "false"),
    ('"True = False"', "false"),
    ('"\\<forall>x::nat. x = 0"', "false"),
    ('"\\<exists>x::nat. x < 0"', "false"),
    ('"rev [(1::nat), 2] = [1, 2]"', "false"),
]

# TPTP keywords as variable names (parse error bug, already confirmed)
KEYWORD_LEMMAS = [
    ('"fof = (fof :: nat)"', "keyword_fof"),
    ('"tff = (tff :: nat)"', "keyword_tff"),
    ('"cnf = (cnf :: nat)"', "keyword_cnf"),
    ('"thf = (thf :: nat)"', "keyword_thf"),
    ('"tcf = (tcf :: nat)"', "keyword_tcf"),
    ('"include = (include :: nat)"', "keyword_include"),
]

SAFE_VARS = ["x", "y", "z", "a", "b", "m", "n", "u", "v", "w"]


# ── Zipperposition flag combinations that Sledgehammer actually uses ──
# These mimic real Sledgehammer slices
REAL_FLAG_COMBOS = [
    # Basic normal mode (most common)
    ["--steps", "10000", "--timeout", "30"],
    # Higher-order mode
    ["--ho", "--steps", "10000", "--timeout", "30"],
    # Lambda-free higher-order (from the paper)
    ["--no-ho", "--steps", "10000", "--timeout", "30"],
    # With different term orders
    ["--ord", "rpo6", "--steps", "10000", "--timeout", "30"],
    ["--ord", "kbo", "--steps", "10000", "--timeout", "30"],
    # Avatar splitting on/off
    ["--no-avatar", "--steps", "10000", "--timeout", "30"],
    ["--avatar", "on", "--steps", "10000", "--timeout", "30"],
    # Combinations
    ["--ho", "--ord", "kbo", "--no-avatar", "--steps", "10000", "--timeout", "30"],
    ["--ho", "--ord", "rpo6", "--steps", "10000", "--timeout", "30"],
]


@dataclass
class BugReport:
    file: str
    bug_type: str         # crash | soundness | hang | parse_error
    flags: str
    exit_code: int
    output_snippet: str
    severity: str         # critical | high | medium | low
    description: str


def run_zp(zp: str, filepath: Path, extra_args: list[str], timeout: int = 60):
    """Run Zipperposition and return (exit_code, stdout+stderr, timed_out)."""
    cmd = [zp, "--input", "tptp", "--output", "tptp"] + extra_args + [str(filepath)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return proc.returncode, proc.stdout + proc.stderr, False
    except subprocess.TimeoutExpired:
        return -1, "", True


# ══════════════════════════════════════════════════════════════════════
#  GENERATE: Create .thy files with true/false lemmas
# ══════════════════════════════════════════════════════════════════════

def cmd_generate(args):
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    theories = []
    for i in range(args.count):
        name = f"FuzzTest{i:03d}"
        lines = [f"theory {name}", "imports Main", "begin", ""]

        lemma_id = 0

        # Mix of true, false, and keyword lemmas
        all_lemmas = []
        for _ in range(random.randint(3, 6)):
            template, label = random.choice(TRUE_LEMMAS)
            v = random.choice(SAFE_VARS)
            w = random.choice([x for x in SAFE_VARS if x != v])
            formula = template.format(v=v, w=w)
            all_lemmas.append((formula, label))

        for _ in range(random.randint(2, 4)):
            template, label = random.choice(FALSE_LEMMAS)
            v = random.choice(SAFE_VARS)
            w = random.choice([x for x in SAFE_VARS if x != v])
            formula = template.format(v=v, w=w)
            all_lemmas.append((formula, label))

        # Occasionally add keyword collision tests
        if random.random() < 0.3:
            template, label = random.choice(KEYWORD_LEMMAS)
            all_lemmas.append((template, label))

        random.shuffle(all_lemmas)

        for formula, label in all_lemmas:
            lemma_id += 1
            # Encode the expected truth value in the lemma name
            # so we can check soundness later
            lines.append(f'lemma {label}_{lemma_id}: {formula}')
            lines.append(f'  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]')
            lines.append("  oops")
            lines.append("")

        lines.append("end")
        (out / f"{name}.thy").write_text("\n".join(lines), encoding="utf-8")
        theories.append(name)

    # Write ROOT
    root = ['session FuzzTests = HOL +', '  theories']
    for th in theories:
        root.append(f'    {th}')
    (out / "ROOT").write_text("\n".join(root) + "\n")

    print(f"[*] Generated {len(theories)} theories with true/false/keyword lemmas → {out}")
    print(f"[*] After running Isabelle build, check the .p files for soundness bugs")
    print(f"[*] Files named 'false_*' should NEVER produce 'Theorem' status")


# ══════════════════════════════════════════════════════════════════════
#  TEST-CRASH: Find crashes in normal mode
# ══════════════════════════════════════════════════════════════════════

def cmd_test_crash(args):
    zp = args.zp
    input_dir = Path(args.input_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    files = sorted(input_dir.glob("*.p"))
    print(f"[*] Testing {len(files)} files for crashes in normal mode")

    bugs = []
    for idx, f in enumerate(files, 1):
        for flags in REAL_FLAG_COMBOS:
            flag_str = " ".join(flags)
            exit_code, output, timed_out = run_zp(zp, f, flags, timeout=args.timeout)

            print(f"\r  [{idx}/{len(files)}] {f.name} | {flag_str[:40]}", end="", flush=True)

            if timed_out:
                bugs.append(BugReport(
                    file=f.name, bug_type="hang", flags=flag_str,
                    exit_code=-1, output_snippet="TIMEOUT",
                    severity="medium",
                    description=f"Zipperposition did not terminate within {args.timeout}s"
                ))
                continue

            # Check for crashes (not just "no proof found")
            has_exception = bool(re.search(r'Failure\(|exception|Fatal|Segmentation', output))
            has_parse_err = "parse error" in output.lower()

            if has_exception and not has_parse_err:
                bugs.append(BugReport(
                    file=f.name, bug_type="crash", flags=flag_str,
                    exit_code=exit_code,
                    output_snippet=output[:500],
                    severity="high",
                    description="Uncaught exception in normal solving mode"
                ))
            elif has_parse_err:
                bugs.append(BugReport(
                    file=f.name, bug_type="parse_error", flags=flag_str,
                    exit_code=exit_code,
                    output_snippet=output[:500],
                    severity="high",
                    description="Parse error on Sledgehammer-generated TPTP"
                ))

            # Check for soundness: if the file name contains "false" and ZP says Theorem
            if "false" in f.name.lower() and "SZS status Theorem" in output:
                bugs.append(BugReport(
                    file=f.name, bug_type="soundness", flags=flag_str,
                    exit_code=exit_code,
                    output_snippet=output[:500],
                    severity="critical",
                    description="Zipperposition claims Theorem on a known FALSE lemma!"
                ))

    print()

    # Write report
    report_path = output_dir / "crash_report.json"
    with open(report_path, "w") as fp:
        json.dump([asdict(b) for b in bugs], fp, indent=2)

    # Summary
    txt_path = output_dir / "crash_summary.txt"
    lines = ["=" * 60, "CRASH/BUG TESTING SUMMARY", "=" * 60, ""]
    by_type = {}
    for b in bugs:
        by_type.setdefault(b.bug_type, []).append(b)

    for btype, items in sorted(by_type.items()):
        lines.append(f"{btype}: {len(items)} occurrences")
        for b in items[:5]:  # Show first 5 of each
            lines.append(f"  [{b.severity}] {b.file} | {b.flags[:60]}")
            lines.append(f"    {b.description}")
        if len(items) > 5:
            lines.append(f"  ... and {len(items)-5} more")
        lines.append("")

    if not bugs:
        lines.append("No bugs found in this run.")

    txt_path.write_text("\n".join(lines) + "\n")

    print(f"\n{'='*60}")
    print(f"  Bugs found: {len(bugs)}")
    for btype, items in sorted(by_type.items()):
        print(f"    {btype}: {len(items)}")
    print(f"{'='*60}")
    print(f"[*] Report: {report_path}")
    print(f"[*] Summary: {txt_path}")


# ══════════════════════════════════════════════════════════════════════
#  TEST-FLAGS: Systematically test different flag combinations
# ══════════════════════════════════════════════════════════════════════

def cmd_test_flags(args):
    """Same as test-crash but focused on finding flag combos that cause issues."""
    # Reuse test-crash logic
    cmd_test_crash(args)


def main():
    parser = argparse.ArgumentParser(description="Find genuine Zipperposition bugs")
    parser.add_argument("--zp", default="zipperposition")
    parser.add_argument("--timeout", type=int, default=60)
    sub = parser.add_subparsers(dest="cmd")

    p_gen = sub.add_parser("generate", help="Generate .thy files with true/false lemmas")
    p_gen.add_argument("--output-dir", required=True)
    p_gen.add_argument("--count", type=int, default=10)

    p_crash = sub.add_parser("test-crash", help="Test .p files for crashes in normal mode")
    p_crash.add_argument("--input-dir", required=True)
    p_crash.add_argument("--output-dir", default=str(Path.home() / "fyp-isabelle-fuzz" / "real_bugs"))

    p_flags = sub.add_parser("test-flags", help="Test different flag combinations")
    p_flags.add_argument("--input-dir", required=True)
    p_flags.add_argument("--output-dir", default=str(Path.home() / "fyp-isabelle-fuzz" / "real_bugs"))

    args = parser.parse_args()
    if args.cmd == "generate":
        cmd_generate(args)
    elif args.cmd in ("test-crash", "test-flags"):
        cmd_test_crash(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()