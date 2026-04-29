#!/usr/bin/env python3
"""
smt_diff_fuzz.py — SMT-LIB Differential Fuzzer for Isabelle-Sledgehammer interface.

Takes Sledgehammer-generated .smt_in seed files, applies targeted mutations,
and runs each mutant through Z3 and CVC5. Flags:
  - Soundness bugs:  one says sat, the other says unsat
  - Crashes:         segfault / non-zero exit on valid-looking input
  - Parser divergence: one parses OK, the other rejects

Seeds come from Isabelle's overlord mode:
    ~/.isabelle/Isabelle2025/prob_z3.smt_in
    ~/.isabelle/Isabelle2025/prob_cvc5.smt_in

Usage:
    python3 smt_diff_fuzz.py \\
        --seeds ~/smt_seeds/ \\
        --z3 /path/to/z3 \\
        --cvc5 /path/to/cvc5 \\
        --rounds 500 \\
        --timeout 30 \\
        --output-dir ~/smt_fuzz_results/
"""

import argparse
import hashlib
import json
import os
import random
import re
import subprocess
import sys
import time
from copy import deepcopy
from dataclasses import dataclass, asdict, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# ═══════════════════════════════════════════════════════════════════════
#  SMT-LIB MUTATION STRATEGIES
# ═══════════════════════════════════════════════════════════════════════

# SMT-LIB keywords that might cause parser issues if used as symbols
SMTLIB_KEYWORDS = [
    "assert", "check-sat", "declare-fun", "declare-sort", "define-fun",
    "set-logic", "set-option", "get-unsat-core", "get-model", "get-proof",
    "push", "pop", "forall", "exists", "let", "ite", "and", "or", "not",
    "true", "false", "Bool", "Int", "Real", "Array", "BitVec",
    "par", "match", "as", "NUMERAL", "STRING", "DECIMAL",
]

# Sort names to inject / swap
SORT_NAMES = [
    "Int", "Bool", "Real", "String",
    "Array", "BitVec",
    "MySortThatDoesNotExist",
]

# Logic names to try
LOGIC_NAMES = [
    "QF_LIA", "QF_LRA", "QF_NIA", "QF_NRA", "QF_UF", "QF_UFLIA",
    "AUFLIA", "AUFLIRA", "AUFNIRA", "LIA", "LRA", "NIA", "NRA",
    "UF", "UFLIA", "UFLRA", "UFNIA",
    "ALL", "HORN",
    "INVALID_LOGIC",  # should trigger graceful error
]


def mutate_smt(content: str, mutation_count: int = None) -> str:
    """Apply random mutations to SMT-LIB content."""
    mutations = [
        _mut_swap_logic,
        _mut_remove_assert,
        _mut_duplicate_assert,
        _mut_negate_assert,
        _mut_swap_symbol_name,
        _mut_inject_keyword_symbol,
        _mut_add_extra_sort,
        _mut_swap_sort_in_decl,
        _mut_flip_quantifier,
        _mut_add_redundant_assert,
        _mut_permute_asserts,
        _mut_change_option,
        _mut_inject_push_pop,
        _mut_swap_connective,
        _mut_duplicate_declare,
        _mut_corrupt_numeral,
    ]

    if mutation_count is None:
        mutation_count = random.randint(1, 3)

    for _ in range(mutation_count):
        mut = random.choice(mutations)
        try:
            content = mut(content)
        except Exception:
            pass  # mutation failed, skip

    return content


# ── Individual mutations ─────────────────────────────────────────────

def _split_lines(content: str) -> list[str]:
    return content.splitlines(keepends=True)


def _find_assert_lines(lines: list[str]) -> list[int]:
    """Find indices of lines that start an (assert ...) block."""
    indices = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("(assert"):
            indices.append(i)
    return indices


def _find_assert_blocks(content: str) -> list[str]:
    """Extract full (assert ...) blocks using paren matching."""
    blocks = []
    i = 0
    while i < len(content):
        if content[i:i+7] == "(assert":
            depth = 0
            start = i
            while i < len(content):
                if content[i] == "(":
                    depth += 1
                elif content[i] == ")":
                    depth -= 1
                    if depth == 0:
                        blocks.append(content[start:i+1])
                        break
                i += 1
        i += 1
    return blocks


def _mut_swap_logic(content: str) -> str:
    """Change the (set-logic ...) declaration."""
    new_logic = random.choice(LOGIC_NAMES)
    return re.sub(r'\(set-logic\s+\w+\)', f'(set-logic {new_logic})', content)


def _mut_remove_assert(content: str) -> str:
    """Remove a random (assert ...) block."""
    blocks = _find_assert_blocks(content)
    if len(blocks) <= 2:
        return content  # keep at least some structure
    target = random.choice(blocks)
    return content.replace(target, "", 1)


def _mut_duplicate_assert(content: str) -> str:
    """Duplicate a random assertion."""
    blocks = _find_assert_blocks(content)
    if not blocks:
        return content
    target = random.choice(blocks)
    # Insert duplicate right after original
    return content.replace(target, target + "\n" + target, 1)


def _mut_negate_assert(content: str) -> str:
    """Wrap a random assertion's body in (not ...)."""
    blocks = _find_assert_blocks(content)
    if not blocks:
        return content
    target = random.choice(blocks)

    # Extract the body: (assert (! BODY :named ...)) or (assert BODY)
    # Simple approach: find the inner expression
    inner = target[7:-1].strip()  # remove "(assert" and final ")"

    # If it uses (! ... :named ...), wrap the formula part
    if inner.startswith("(!"):
        # (! FORMULA :named NAME)
        # Negate: (! (not FORMULA) :named NAME)
        named_match = re.search(r':named\s+\w+', inner)
        if named_match:
            formula_end = named_match.start()
            formula = inner[2:formula_end].strip()  # skip "(!"
            named_part = inner[formula_end:].rstrip(")")
            negated = f"(assert (! (not {formula}) {named_part}))"
            return content.replace(target, negated, 1)

    # Simple assert: just negate
    negated = f"(assert (not {inner}))"
    return content.replace(target, negated, 1)


def _mut_swap_symbol_name(content: str) -> str:
    """Replace a random declared symbol with a different name."""
    decls = re.findall(r'\(declare-fun\s+(\w+\$?\w*)\s', content)
    if not decls:
        return content
    old = random.choice(decls)
    new = f"mut_{random.randint(0,9999)}"
    # Replace all occurrences
    return content.replace(old, new)


def _mut_inject_keyword_symbol(content: str) -> str:
    """Inject a declaration using an SMT-LIB keyword as the name."""
    kw = random.choice(SMTLIB_KEYWORDS)
    sort = random.choice(["Int", "Bool"])
    injection = f"(declare-fun {kw} () {sort})\n"
    # Insert after (set-logic ...)
    match = re.search(r'\(set-logic\s+\w+\)\s*\n', content)
    if match:
        pos = match.end()
        return content[:pos] + injection + content[pos:]
    return injection + content


def _mut_add_extra_sort(content: str) -> str:
    """Add a new uninterpreted sort declaration."""
    name = f"FuzzSort{random.randint(0, 999)}$"
    arity = random.choice([0, 1, 2])
    decl = f"(declare-sort {name} {arity})\n"
    # Insert after existing declare-sort block
    last_sort = content.rfind("(declare-sort")
    if last_sort >= 0:
        eol = content.index("\n", last_sort)
        return content[:eol+1] + decl + content[eol+1:]
    return decl + content


def _mut_swap_sort_in_decl(content: str) -> str:
    """Swap a sort reference in a declare-fun to a different sort."""
    # Find user-defined sorts
    user_sorts = re.findall(r'\(declare-sort\s+(\w+\$?)\s+\d+\)', content)
    if len(user_sorts) < 2:
        return content
    old = random.choice(user_sorts)
    new = random.choice([s for s in user_sorts if s != old])
    # Only swap in one random declare-fun line (not globally)
    decl_funs = [m for m in re.finditer(r'\(declare-fun\s+[^)]+\)', content)]
    if not decl_funs:
        return content
    target_match = random.choice(decl_funs)
    target = target_match.group()
    if old in target:
        swapped = target.replace(old, new, 1)
        return content[:target_match.start()] + swapped + content[target_match.end():]
    return content


def _mut_flip_quantifier(content: str) -> str:
    """Replace a random forall with exists or vice versa."""
    if random.random() < 0.5:
        # Only replace one occurrence
        idx = content.find("forall")
        if idx >= 0:
            return content[:idx] + "exists" + content[idx+6:]
    else:
        idx = content.find("exists")
        if idx >= 0:
            return content[:idx] + "forall" + content[idx+6:]
    return content


def _mut_add_redundant_assert(content: str) -> str:
    """Add a tautology assertion."""
    tautologies = [
        "(assert (= 0 0))",
        "(assert (or true true))",
        "(assert (=> false true))",
        "(assert (not false))",
        "(assert (<= 0 0))",
        "(assert (forall ((?x Int)) (= ?x ?x)))",
    ]
    taut = random.choice(tautologies)
    # Insert before (check-sat)
    return content.replace("(check-sat)", f"{taut}\n(check-sat)", 1)


def _mut_permute_asserts(content: str) -> str:
    """Shuffle the order of assertions."""
    blocks = _find_assert_blocks(content)
    if len(blocks) < 3:
        return content
    # Only shuffle a random subset
    n = random.randint(2, min(10, len(blocks)))
    chosen_indices = random.sample(range(len(blocks)), n)
    chosen_blocks = [blocks[i] for i in chosen_indices]
    shuffled = chosen_blocks[:]
    random.shuffle(shuffled)
    result = content
    for orig, new in zip(chosen_blocks, shuffled):
        result = result.replace(orig, f"__PLACEHOLDER_{id(orig)}__", 1)
    for orig, new in zip(chosen_blocks, shuffled):
        result = result.replace(f"__PLACEHOLDER_{id(orig)}__", new, 1)
    return result


def _mut_change_option(content: str) -> str:
    """Modify or add a set-option."""
    options = [
        "(set-option :produce-models true)",
        "(set-option :produce-proofs true)",
        "(set-option :produce-unsat-cores true)",
        "(set-option :random-seed 42)",
        "(set-option :produce-assignments true)",
    ]
    opt = random.choice(options)
    # Insert at the start (after any comment lines)
    lines = content.splitlines(keepends=True)
    insert_pos = 0
    for i, line in enumerate(lines):
        if line.strip().startswith(";"):
            insert_pos = i + 1
        else:
            break
    lines.insert(insert_pos, opt + "\n")
    return "".join(lines)


def _mut_inject_push_pop(content: str) -> str:
    """Inject (push)/(pop) around a random assertion."""
    blocks = _find_assert_blocks(content)
    if not blocks:
        return content
    target = random.choice(blocks)
    wrapped = f"(push 1)\n{target}\n(pop 1)"
    return content.replace(target, wrapped, 1)


def _mut_swap_connective(content: str) -> str:
    """Swap a logical connective: and↔or, =>↔<=>, etc."""
    swaps = [("and", "or"), ("or", "and"), ("=>", "="), ("<=", ">=")]
    old, new = random.choice(swaps)
    # Find all occurrences and replace one random one
    indices = [m.start() for m in re.finditer(re.escape(f"({old} "), content)]
    if not indices:
        return content
    idx = random.choice(indices)
    return content[:idx] + f"({new} " + content[idx + len(f"({old} "):]


def _mut_duplicate_declare(content: str) -> str:
    """Duplicate a random declare-fun (should be harmless or error)."""
    decls = list(re.finditer(r'\(declare-fun\s+[^)]+\)\s*\n', content))
    if not decls:
        return content
    target = random.choice(decls)
    return content[:target.end()] + target.group() + content[target.end():]


def _mut_corrupt_numeral(content: str) -> str:
    """Replace a numeral with something odd."""
    replacements = ["999999999999999999999", "-1", "0", "1",
                    "2147483647", "2147483648", "-2147483648"]
    # Find a numeral in an assert
    nums = list(re.finditer(r'(?<=\s)(\d+)(?=[\s)])', content))
    if not nums:
        return content
    target = random.choice(nums)
    new_num = random.choice(replacements)
    return content[:target.start()] + new_num + content[target.end():]


# ═══════════════════════════════════════════════════════════════════════
#  SOLVER HARNESS
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class SolverResult:
    solver: str
    exit_code: int
    answer: str           # "sat" | "unsat" | "unknown" | "error" | "timeout" | "crash"
    raw_output: str
    elapsed_ms: int
    error_msg: Optional[str] = None


def run_solver(solver_path: str, solver_name: str, input_file: Path,
               timeout: int = 30, extra_args: list[str] = None) -> SolverResult:
    """Run an SMT solver and parse its output."""
    cmd = [solver_path] + (extra_args or []) + [str(input_file)]

    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        elapsed = int((time.monotonic() - start) * 1000)

        stdout = proc.stdout.strip()
        stderr = proc.stderr.strip()
        combined = stdout + "\n" + stderr

        # Parse answer
        answer = "unknown"
        for line in stdout.splitlines():
            line = line.strip()
            if line == "sat":
                answer = "sat"
                break
            elif line == "unsat":
                answer = "unsat"
                break
            elif line == "unknown":
                answer = "unknown"
                break

        # Detect crashes
        error_msg = None
        if proc.returncode < 0:
            # Killed by signal (e.g., SIGSEGV = -11)
            answer = "crash"
            error_msg = f"signal {-proc.returncode}"
        elif proc.returncode != 0 and answer not in ("sat", "unsat"):
            # Some solvers exit non-zero on error but still print sat/unsat
            if "error" in combined.lower() or "fatal" in combined.lower():
                answer = "error"
                # Extract first error line
                for line in combined.splitlines():
                    if "error" in line.lower():
                        error_msg = line.strip()[:200]
                        break

        return SolverResult(
            solver=solver_name,
            exit_code=proc.returncode,
            answer=answer,
            raw_output=combined[:2000],
            elapsed_ms=elapsed,
            error_msg=error_msg,
        )

    except subprocess.TimeoutExpired:
        elapsed = int((time.monotonic() - start) * 1000)
        return SolverResult(
            solver=solver_name,
            exit_code=-1,
            answer="timeout",
            raw_output="TIMEOUT",
            elapsed_ms=elapsed,
            error_msg=f"timeout after {timeout}s",
        )


# ═══════════════════════════════════════════════════════════════════════
#  DIFFERENTIAL COMPARISON
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class DiffResult:
    mutant_id: str
    seed_file: str
    mutation_hash: str
    z3: SolverResult
    cvc5: SolverResult
    category: str        # "agree_sat" | "agree_unsat" | "agree_unknown" |
                         # "soundness_bug" | "z3_crash" | "cvc5_crash" |
                         # "both_crash" | "z3_error" | "cvc5_error" |
                         # "disagree_other" | "both_timeout"
    severity: str        # "critical" | "high" | "medium" | "low" | "info"
    notes: str = ""


def classify_diff(z3r: SolverResult, cvc5r: SolverResult) -> tuple[str, str, str]:
    """Classify the difference between two solver results.
    Returns (category, severity, notes)."""

    a1, a2 = z3r.answer, cvc5r.answer

    # Both agree
    if a1 == a2:
        if a1 == "sat":
            return "agree_sat", "info", ""
        elif a1 == "unsat":
            return "agree_unsat", "info", ""
        elif a1 == "timeout":
            return "both_timeout", "info", ""
        elif a1 == "crash":
            return "both_crash", "high", "Both solvers crashed"
        elif a1 == "error":
            return "both_error", "low", "Both solvers rejected input"
        else:
            return "agree_unknown", "info", ""

    # SOUNDNESS BUG: one says sat, other says unsat
    if {a1, a2} == {"sat", "unsat"}:
        return ("soundness_bug", "critical",
                f"Z3={a1}, CVC5={a2} — at least one solver has a soundness bug!")

    # Crashes
    if a1 == "crash" and a2 != "crash":
        return "z3_crash", "high", f"Z3 crashed: {z3r.error_msg}"
    if a2 == "crash" and a1 != "crash":
        return "cvc5_crash", "high", f"CVC5 crashed: {cvc5r.error_msg}"

    # Errors (parse errors, etc.)
    if a1 == "error" and a2 not in ("error", "crash"):
        return "z3_error", "medium", f"Z3 error but CVC5 gave {a2}: {z3r.error_msg}"
    if a2 == "error" and a1 not in ("error", "crash"):
        return "cvc5_error", "medium", f"CVC5 error but Z3 gave {a1}: {cvc5r.error_msg}"

    # One answers, the other doesn't
    if a1 in ("sat", "unsat") and a2 in ("timeout", "unknown"):
        return "disagree_other", "low", f"Z3={a1} but CVC5={a2}"
    if a2 in ("sat", "unsat") and a1 in ("timeout", "unknown"):
        return "disagree_other", "low", f"CVC5={a2} but Z3={a1}"

    return "disagree_other", "low", f"Z3={a1}, CVC5={a2}"


# ═══════════════════════════════════════════════════════════════════════
#  SEED PREPARATION
# ═══════════════════════════════════════════════════════════════════════

def strip_solver_specific_header(content: str) -> str:
    """Remove solver-specific command-line options from the first line comment.

    Sledgehammer puts Z3/CVC5-specific CLI flags in a `;` comment on line 1.
    We strip that so the same core SMT-LIB can go to both solvers.
    """
    lines = content.splitlines(keepends=True)
    if lines and lines[0].strip().startswith(";"):
        # Remove the first comment line (solver-specific flags)
        lines = lines[1:]
    return "".join(lines)


def ensure_check_sat(content: str) -> str:
    """Make sure the file ends with (check-sat)."""
    if "(check-sat)" not in content:
        content = content.rstrip() + "\n(check-sat)\n"
    return content


def prepare_seed(content: str) -> str:
    """Prepare a raw .smt_in seed for use with both solvers."""
    content = strip_solver_specific_header(content)
    content = ensure_check_sat(content)
    # Remove (get-unsat-core) as it causes issues when result is sat
    content = content.replace("(get-unsat-core)", "")
    return content


# ═══════════════════════════════════════════════════════════════════════
#  MAIN FUZZER LOOP
# ═══════════════════════════════════════════════════════════════════════

def run_fuzz_campaign(
    seed_dir: Path,
    z3_path: str,
    cvc5_path: str,
    output_dir: Path,
    rounds: int = 500,
    timeout: int = 30,
    z3_args: list[str] = None,
    cvc5_args: list[str] = None,
):
    """Main fuzzing loop."""

    output_dir.mkdir(parents=True, exist_ok=True)
    mutants_dir = output_dir / "mutants"
    mutants_dir.mkdir(exist_ok=True)
    interesting_dir = output_dir / "interesting"
    interesting_dir.mkdir(exist_ok=True)

    # Load seeds
    seeds = []
    for ext in ["*.smt_in", "*.smt2", "*.smt"]:
        seeds.extend(seed_dir.glob(ext))
    if not seeds:
        print(f"[!] No .smt_in/.smt2 files found in {seed_dir}")
        sys.exit(1)

    print(f"[*] Loaded {len(seeds)} seed files from {seed_dir}")
    print(f"[*] Z3:   {z3_path}")
    print(f"[*] CVC5: {cvc5_path}")
    print(f"[*] Rounds: {rounds}")
    print(f"[*] Timeout: {timeout}s")
    print(f"[*] Output: {output_dir}")
    print()

    # Prepare seeds
    prepared_seeds = {}
    for sf in seeds:
        raw = sf.read_text(encoding="utf-8", errors="replace")
        prepared_seeds[sf.name] = prepare_seed(raw)

    # Stats
    stats = {
        "total": 0,
        "agree_sat": 0, "agree_unsat": 0, "agree_unknown": 0,
        "soundness_bug": 0,
        "z3_crash": 0, "cvc5_crash": 0, "both_crash": 0,
        "z3_error": 0, "cvc5_error": 0, "both_error": 0,
        "disagree_other": 0, "both_timeout": 0,
    }

    results: list[DiffResult] = []
    start_time = time.monotonic()

    for i in range(rounds):
        seed_name = random.choice(list(prepared_seeds.keys()))
        seed_content = prepared_seeds[seed_name]

        # Round 0: run unmutated seed first
        if i == 0:
            mutated = seed_content
            mutant_id = "seed_original"
        else:
            mutated = mutate_smt(seed_content)
            mut_hash = hashlib.md5(mutated.encode()).hexdigest()[:8]
            mutant_id = f"mut_{i:05d}_{mut_hash}"

        # Write mutant to file
        mutant_path = mutants_dir / f"{mutant_id}.smt2"
        mutant_path.write_text(mutated, encoding="utf-8")

        # Run both solvers
        z3r = run_solver(z3_path, "z3", mutant_path, timeout, z3_args)
        cvc5r = run_solver(cvc5_path, "cvc5", mutant_path, timeout, cvc5_args)

        # Classify
        category, severity, notes = classify_diff(z3r, cvc5r)

        dr = DiffResult(
            mutant_id=mutant_id,
            seed_file=seed_name,
            mutation_hash=hashlib.md5(mutated.encode()).hexdigest()[:12],
            z3=z3r,
            cvc5=cvc5r,
            category=category,
            severity=severity,
            notes=notes,
        )
        results.append(dr)
        stats["total"] += 1
        stats[category] = stats.get(category, 0) + 1

        # Print progress
        marker = ""
        if severity == "critical":
            marker = " *** CRITICAL ***"
        elif severity == "high":
            marker = " ** HIGH **"
        elif severity == "medium":
            marker = " * MEDIUM *"

        elapsed = time.monotonic() - start_time
        rate = stats["total"] / elapsed if elapsed > 0 else 0

        print(f"  [{i+1:5d}/{rounds}] {category:20s} "
              f"Z3={z3r.answer:8s} CVC5={cvc5r.answer:8s} "
              f"({rate:.1f}/s){marker}")

        # Save interesting cases
        if severity in ("critical", "high", "medium"):
            save_path = interesting_dir / f"{severity}_{mutant_id}.smt2"
            mutant_path.rename(save_path) if mutant_path.exists() else None
            # Also save a .json with details
            detail_path = interesting_dir / f"{severity}_{mutant_id}.json"
            detail = {
                "mutant_id": mutant_id,
                "seed": seed_name,
                "category": category,
                "severity": severity,
                "notes": notes,
                "z3": asdict(z3r),
                "cvc5": asdict(cvc5r),
            }
            detail_path.write_text(json.dumps(detail, indent=2))

    # ── Final report ──
    total_time = time.monotonic() - start_time

    report = {
        "timestamp": datetime.now().isoformat(),
        "config": {
            "seed_dir": str(seed_dir),
            "z3": z3_path,
            "cvc5": cvc5_path,
            "rounds": rounds,
            "timeout": timeout,
        },
        "stats": stats,
        "total_time_s": round(total_time, 2),
        "throughput": round(stats["total"] / total_time, 2) if total_time > 0 else 0,
        "interesting": [
            asdict(r) for r in results
            if r.severity in ("critical", "high", "medium")
        ],
    }

    report_path = output_dir / "fuzz_report.json"
    report_path.write_text(json.dumps(report, indent=2, default=str))

    # Print summary
    print(f"\n{'='*60}")
    print(f"  SMT DIFFERENTIAL FUZZING REPORT")
    print(f"{'='*60}")
    print(f"  Total mutants:    {stats['total']}")
    print(f"  Time:             {total_time:.1f}s")
    print(f"  Throughput:       {stats['total']/total_time:.1f} tests/s")
    print()
    print(f"  SOUNDNESS BUGS:   {stats.get('soundness_bug', 0)}  {'*** CHECK THESE ***' if stats.get('soundness_bug', 0) > 0 else ''}")
    print(f"  Z3 crashes:       {stats.get('z3_crash', 0)}")
    print(f"  CVC5 crashes:     {stats.get('cvc5_crash', 0)}")
    print(f"  Both crash:       {stats.get('both_crash', 0)}")
    print(f"  Z3 errors:        {stats.get('z3_error', 0)}")
    print(f"  CVC5 errors:      {stats.get('cvc5_error', 0)}")
    print(f"  Both errors:      {stats.get('both_error', 0)}")
    print(f"  Agree sat:        {stats.get('agree_sat', 0)}")
    print(f"  Agree unsat:      {stats.get('agree_unsat', 0)}")
    print(f"  Agree unknown:    {stats.get('agree_unknown', 0)}")
    print(f"  Both timeout:     {stats.get('both_timeout', 0)}")
    print(f"  Other disagree:   {stats.get('disagree_other', 0)}")
    print(f"{'='*60}")
    print(f"  Report: {report_path}")
    print(f"  Interesting cases: {interesting_dir}")


def main():
    parser = argparse.ArgumentParser(
        description="SMT-LIB Differential Fuzzer for Isabelle-Sledgehammer interface"
    )
    parser.add_argument("--seeds", required=True,
                        help="Directory containing .smt_in / .smt2 seed files")
    parser.add_argument("--z3", required=True, help="Path to Z3 binary")
    parser.add_argument("--cvc5", required=True, help="Path to CVC5 binary")
    parser.add_argument("--rounds", type=int, default=500,
                        help="Number of mutants to test (default: 500)")
    parser.add_argument("--timeout", type=int, default=30,
                        help="Per-solver timeout in seconds (default: 30)")
    parser.add_argument("--output-dir", default="./smt_fuzz_results",
                        help="Output directory for results")
    parser.add_argument("--z3-args", default="", help="Extra args for Z3 (space-separated)")
    parser.add_argument("--cvc5-args", default="", help="Extra args for CVC5 (space-separated)")

    args = parser.parse_args()

    z3_args = args.z3_args.split() if args.z3_args else []
    cvc5_args = args.cvc5_args.split() if args.cvc5_args else []

    run_fuzz_campaign(
        seed_dir=Path(args.seeds),
        z3_path=args.z3,
        cvc5_path=args.cvc5,
        output_dir=Path(args.output_dir),
        rounds=args.rounds,
        timeout=args.timeout,
        z3_args=z3_args,
        cvc5_args=cvc5_args,
    )


if __name__ == "__main__":
    main()
