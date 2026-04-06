#!/usr/bin/env python3
"""
smt_diff_fuzz_v2.py — SMT-LIB Differential Fuzzer v2.

Changes from v1:
  - Parallel solver execution (2x throughput)
  - Removed noisy mutations (push/pop, swap_logic) that produce known false positives
  - Added aggressive new mutations targeting solver internals
  - Saves disagree cases (not just medium+)
  - Dedup: skips mutants identical to previously tested ones
  - Shorter default timeout (5s)
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
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, asdict, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# ═══════════════════════════════════════════════════════════════════════
#  SMT-LIB MUTATION STRATEGIES (v2 — cleaned up)
# ═══════════════════════════════════════════════════════════════════════

SMTLIB_RESERVED = [
    "par", "NUMERAL", "DECIMAL", "STRING", "_", "!", "as", "let",
    "forall", "exists", "match", "assert", "check-sat", "declare-fun",
    "declare-sort", "define-fun", "set-logic", "set-option",
]


def mutate_smt(content: str, mutation_count: int = None) -> str:
    """Apply random mutations to SMT-LIB content."""
    mutations = [
        # ── Structural (semantics-preserving-ish) ──
        _mut_remove_assert,
        _mut_duplicate_assert,
        _mut_negate_assert,
        _mut_permute_asserts,
        _mut_add_redundant_assert,
        # ── Symbol / type manipulation ──
        _mut_swap_symbol_name,
        _mut_inject_reserved_symbol,
        _mut_swap_sort_in_decl,
        _mut_add_extra_sort,
        _mut_duplicate_declare,
        # ── Formula manipulation ──
        _mut_flip_quantifier,
        _mut_swap_connective,
        _mut_corrupt_numeral,
        _mut_inject_deep_nesting,
        _mut_inject_let_binding,
        _mut_add_named_assert,
        # ── Aggressive / edge-case ──
        _mut_inject_huge_numeral,
        _mut_inject_chained_equals,
        _mut_inject_ite_chain,
        _mut_inject_distinct,
        _mut_empty_assert,
    ]

    if mutation_count is None:
        mutation_count = random.randint(1, 4)

    for _ in range(mutation_count):
        mut = random.choice(mutations)
        try:
            content = mut(content)
        except Exception:
            pass

    return content


# ── Helpers ──────────────────────────────────────────────────────────

def _find_assert_blocks(content: str) -> list[str]:
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


def _get_declared_symbols(content: str) -> list[str]:
    return re.findall(r'\(declare-fun\s+(\w+\$?\w*)\s', content)


def _get_declared_sorts(content: str) -> list[str]:
    return re.findall(r'\(declare-sort\s+(\w+\$?)\s+\d+\)', content)


# ── Structural mutations ────────────────────────────────────────────

def _mut_remove_assert(content: str) -> str:
    blocks = _find_assert_blocks(content)
    if len(blocks) <= 2:
        return content
    target = random.choice(blocks)
    return content.replace(target, "", 1)


def _mut_duplicate_assert(content: str) -> str:
    blocks = _find_assert_blocks(content)
    if not blocks:
        return content
    target = random.choice(blocks)
    return content.replace(target, target + "\n" + target, 1)


def _mut_negate_assert(content: str) -> str:
    blocks = _find_assert_blocks(content)
    if not blocks:
        return content
    target = random.choice(blocks)
    inner = target[7:-1].strip()
    if inner.startswith("(!"):
        named_match = re.search(r':named\s+\w+', inner)
        if named_match:
            formula_end = named_match.start()
            formula = inner[2:formula_end].strip()
            named_part = inner[formula_end:].rstrip(")")
            negated = f"(assert (! (not {formula}) {named_part}))"
            return content.replace(target, negated, 1)
    negated = f"(assert (not {inner}))"
    return content.replace(target, negated, 1)


def _mut_permute_asserts(content: str) -> str:
    blocks = _find_assert_blocks(content)
    if len(blocks) < 3:
        return content
    n = random.randint(2, min(10, len(blocks)))
    chosen = random.sample(blocks, n)
    shuffled = chosen[:]
    random.shuffle(shuffled)
    result = content
    for orig, new_block in zip(chosen, shuffled):
        placeholder = f"__PH_{id(orig)}__"
        result = result.replace(orig, placeholder, 1)
    for orig, new_block in zip(chosen, shuffled):
        placeholder = f"__PH_{id(orig)}__"
        result = result.replace(placeholder, new_block, 1)
    return result


def _mut_add_redundant_assert(content: str) -> str:
    tautologies = [
        "(assert (= 0 0))",
        "(assert (or true true))",
        "(assert (=> false true))",
        "(assert (not false))",
        "(assert (<= 0 0))",
        "(assert (forall ((?x Int)) (= ?x ?x)))",
        "(assert (forall ((?x Int)) (<= ?x ?x)))",
        "(assert (=> true true))",
    ]
    taut = random.choice(tautologies)
    return content.replace("(check-sat)", f"{taut}\n(check-sat)", 1)


# ── Symbol / type mutations ─────────────────────────────────────────

def _mut_swap_symbol_name(content: str) -> str:
    decls = _get_declared_symbols(content)
    if not decls:
        return content
    old = random.choice(decls)
    new = f"mut_{random.randint(0,9999)}"
    return content.replace(old, new)


def _mut_inject_reserved_symbol(content: str) -> str:
    """Inject a declaration using an SMT-LIB reserved word as the name."""
    kw = random.choice(SMTLIB_RESERVED)
    sort = random.choice(["Int", "Bool"])
    injection = f"(declare-fun {kw} () {sort})\n"
    match = re.search(r'\(set-logic\s+\w+\)\s*\n', content)
    if match:
        pos = match.end()
        return content[:pos] + injection + content[pos:]
    return injection + content


def _mut_swap_sort_in_decl(content: str) -> str:
    user_sorts = _get_declared_sorts(content)
    if len(user_sorts) < 2:
        return content
    old = random.choice(user_sorts)
    new = random.choice([s for s in user_sorts if s != old])
    decl_funs = list(re.finditer(r'\(declare-fun\s+[^)]+\)', content))
    if not decl_funs:
        return content
    target_match = random.choice(decl_funs)
    target = target_match.group()
    if old in target:
        swapped = target.replace(old, new, 1)
        return content[:target_match.start()] + swapped + content[target_match.end():]
    return content


def _mut_add_extra_sort(content: str) -> str:
    name = f"FuzzSort{random.randint(0, 999)}$"
    decl = f"(declare-sort {name} 0)\n"
    last_sort = content.rfind("(declare-sort")
    if last_sort >= 0:
        eol = content.index("\n", last_sort)
        return content[:eol+1] + decl + content[eol+1:]
    return decl + content


def _mut_duplicate_declare(content: str) -> str:
    decls = list(re.finditer(r'\(declare-fun\s+[^)]+\)\s*\n', content))
    if not decls:
        return content
    target = random.choice(decls)
    return content[:target.end()] + target.group() + content[target.end():]


# ── Formula manipulation ────────────────────────────────────────────

def _mut_flip_quantifier(content: str) -> str:
    if random.random() < 0.5:
        idx = content.find("forall")
        if idx >= 0:
            return content[:idx] + "exists" + content[idx+6:]
    else:
        idx = content.find("exists")
        if idx >= 0:
            return content[:idx] + "forall" + content[idx+6:]
    return content


def _mut_swap_connective(content: str) -> str:
    swaps = [("and ", "or "), ("or ", "and "), ("=> ", "= ")]
    old, new = random.choice(swaps)
    indices = [m.start() for m in re.finditer(re.escape(f"({old}"), content)]
    if not indices:
        return content
    idx = random.choice(indices)
    return content[:idx] + f"({new}" + content[idx + len(f"({old}"):]


def _mut_corrupt_numeral(content: str) -> str:
    replacements = ["999999999999999999999", "-1", "0", "1",
                    "2147483647", "2147483648", "-2147483648",
                    "9223372036854775807"]
    nums = list(re.finditer(r'(?<=\s)(\d+)(?=[\s)])', content))
    if not nums:
        return content
    target = random.choice(nums)
    new_num = random.choice(replacements)
    return content[:target.start()] + new_num + content[target.end():]


def _mut_inject_deep_nesting(content: str) -> str:
    """Inject a deeply nested term to stress parser stack."""
    depth = random.randint(50, 200)
    inner = "x_deep"
    for _ in range(depth):
        op = random.choice(["not ", "not "])
        inner = f"({op}{inner})"
    decl = f"(declare-fun x_deep () Bool)\n"
    assertion = f"(assert {inner})\n"
    if "x_deep" not in content:
        content = content.replace("(check-sat)", f"{decl}{assertion}(check-sat)", 1)
    return content


def _mut_inject_let_binding(content: str) -> str:
    """Inject a let binding that could confuse scope handling."""
    symbols = _get_declared_symbols(content)
    if not symbols:
        return content
    sym = random.choice(symbols)
    let_expr = f"(assert (let ((?let_v 0)) (= ?let_v 0)))\n"
    return content.replace("(check-sat)", f"{let_expr}(check-sat)", 1)


def _mut_add_named_assert(content: str) -> str:
    """Add an assertion with a :named annotation using an unusual name."""
    names = [f"n{random.randint(0,9999)}", "assert", "check-sat",
             "declare-fun", "true", "false", "x$", ""]
    name = random.choice(names)
    if name:
        assertion = f'(assert (! true :named {name}))\n'
    else:
        assertion = "(assert true)\n"
    return content.replace("(check-sat)", f"{assertion}(check-sat)", 1)


# ── Aggressive / edge-case mutations ────────────────────────────────

def _mut_inject_huge_numeral(content: str) -> str:
    """Inject a very large numeral to test bignum handling."""
    huge = str(10**random.randint(100, 500))
    assertion = f"(assert (>= {huge} 0))\n"
    return content.replace("(check-sat)", f"{assertion}(check-sat)", 1)


def _mut_inject_chained_equals(content: str) -> str:
    """Inject a chain of equalities: (= a b c d ...)."""
    symbols = _get_declared_symbols(content)
    if len(symbols) < 3:
        return content
    n = random.randint(3, min(8, len(symbols)))
    chain = random.sample(symbols, n)
    assertion = f"(assert (= {' '.join(chain)}))\n"
    return content.replace("(check-sat)", f"{assertion}(check-sat)", 1)


def _mut_inject_ite_chain(content: str) -> str:
    """Inject a chain of ite (if-then-else) expressions."""
    depth = random.randint(5, 30)
    expr = "0"
    for i in range(depth):
        cond = f"(> {i} {i-1})" if i > 0 else "true"
        expr = f"(ite {cond} {expr} {i})"
    assertion = f"(assert (>= {expr} 0))\n"
    return content.replace("(check-sat)", f"{assertion}(check-sat)", 1)


def _mut_inject_distinct(content: str) -> str:
    """Inject (distinct ...) with many arguments."""
    symbols = _get_declared_symbols(content)
    if len(symbols) < 2:
        return content
    n = random.randint(2, min(6, len(symbols)))
    chosen = random.sample(symbols, n)
    assertion = f"(assert (distinct {' '.join(chosen)}))\n"
    return content.replace("(check-sat)", f"{assertion}(check-sat)", 1)


def _mut_empty_assert(content: str) -> str:
    """Inject edge-case assertions."""
    edge_cases = [
        "(assert true)",
        "(assert (not false))",
        "(assert (= 0 0))",
        "(assert (and))",          # zero-arg and — should be true per spec
        "(assert (or))",           # zero-arg or — should be false per spec
        "(assert (distinct))",     # zero-arg distinct
    ]
    assertion = random.choice(edge_cases) + "\n"
    return content.replace("(check-sat)", f"{assertion}(check-sat)", 1)


# ═══════════════════════════════════════════════════════════════════════
#  SOLVER HARNESS (unchanged from v1)
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class SolverResult:
    solver: str
    exit_code: int
    answer: str
    raw_output: str
    elapsed_ms: int
    error_msg: Optional[str] = None


def run_solver(solver_path: str, solver_name: str, input_file: Path,
               timeout: int = 5, extra_args: list[str] = None) -> SolverResult:
    cmd = [solver_path] + (extra_args or []) + [str(input_file)]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        elapsed = int((time.monotonic() - start) * 1000)
        stdout = proc.stdout.strip()
        stderr = proc.stderr.strip()
        combined = stdout + "\n" + stderr

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

        error_msg = None
        if proc.returncode < 0:
            answer = "crash"
            error_msg = f"signal {-proc.returncode}"
        elif proc.returncode != 0 and answer not in ("sat", "unsat"):
            if "error" in combined.lower() or "fatal" in combined.lower():
                answer = "error"
                for line in combined.splitlines():
                    if "error" in line.lower():
                        error_msg = line.strip()[:200]
                        break

        return SolverResult(solver=solver_name, exit_code=proc.returncode,
                           answer=answer, raw_output=combined[:2000],
                           elapsed_ms=elapsed, error_msg=error_msg)

    except subprocess.TimeoutExpired:
        elapsed = int((time.monotonic() - start) * 1000)
        return SolverResult(solver=solver_name, exit_code=-1, answer="timeout",
                           raw_output="TIMEOUT", elapsed_ms=elapsed,
                           error_msg=f"timeout after {timeout}s")


def run_solvers_parallel(z3_path, cvc5_path, input_file, timeout, z3_args, cvc5_args):
    """Run Z3 and CVC5 in parallel."""
    with ThreadPoolExecutor(max_workers=2) as pool:
        f_z3 = pool.submit(run_solver, z3_path, "z3", input_file, timeout, z3_args)
        f_cvc5 = pool.submit(run_solver, cvc5_path, "cvc5", input_file, timeout, cvc5_args)
        return f_z3.result(), f_cvc5.result()


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
    category: str
    severity: str
    notes: str = ""


def classify_diff(z3r: SolverResult, cvc5r: SolverResult) -> tuple[str, str, str]:
    a1, a2 = z3r.answer, cvc5r.answer

    if a1 == a2:
        if a1 == "sat":     return "agree_sat", "info", ""
        if a1 == "unsat":   return "agree_unsat", "info", ""
        if a1 == "timeout": return "both_timeout", "info", ""
        if a1 == "crash":   return "both_crash", "high", "Both solvers crashed"
        if a1 == "error":   return "both_error", "low", "Both solvers rejected"
        return "agree_unknown", "info", ""

    if {a1, a2} == {"sat", "unsat"}:
        return ("soundness_bug", "critical",
                f"Z3={a1}, CVC5={a2} — SOUNDNESS BUG!")

    if a1 == "crash" and a2 != "crash":
        return "z3_crash", "critical", f"Z3 crashed: {z3r.error_msg}"
    if a2 == "crash" and a1 != "crash":
        return "cvc5_crash", "critical", f"CVC5 crashed: {cvc5r.error_msg}"

    if a1 == "error" and a2 not in ("error", "crash"):
        return "z3_error", "medium", f"Z3 error but CVC5 gave {a2}: {z3r.error_msg}"
    if a2 == "error" and a1 not in ("error", "crash"):
        return "cvc5_error", "medium", f"CVC5 error but Z3 gave {a1}: {cvc5r.error_msg}"

    if a1 in ("sat", "unsat") and a2 in ("timeout", "unknown"):
        return "disagree_answer", "low", f"Z3={a1} but CVC5={a2}"
    if a2 in ("sat", "unsat") and a1 in ("timeout", "unknown"):
        return "disagree_answer", "low", f"CVC5={a2} but Z3={a1}"

    return "disagree_other", "low", f"Z3={a1}, CVC5={a2}"


# ═══════════════════════════════════════════════════════════════════════
#  SEED PREPARATION
# ═══════════════════════════════════════════════════════════════════════

def prepare_seed(content: str) -> str:
    lines = content.splitlines(keepends=True)
    if lines and lines[0].strip().startswith(";"):
        lines = lines[1:]
    content = "".join(lines)
    if "(check-sat)" not in content:
        content = content.rstrip() + "\n(check-sat)\n"
    content = content.replace("(get-unsat-core)", "")
    return content


# ═══════════════════════════════════════════════════════════════════════
#  MAIN FUZZER LOOP (v2 — parallel, dedup, saves all interesting)
# ═══════════════════════════════════════════════════════════════════════

def run_fuzz_campaign(
    seed_dir: Path,
    z3_path: str,
    cvc5_path: str,
    output_dir: Path,
    rounds: int = 5000,
    timeout: int = 5,
    z3_args: list[str] = None,
    cvc5_args: list[str] = None,
):
    output_dir.mkdir(parents=True, exist_ok=True)
    mutants_dir = output_dir / "mutants"
    mutants_dir.mkdir(exist_ok=True)
    interesting_dir = output_dir / "interesting"
    interesting_dir.mkdir(exist_ok=True)

    seeds = []
    for ext in ["*.smt_in", "*.smt2", "*.smt"]:
        seeds.extend(seed_dir.glob(ext))
    if not seeds:
        print(f"[!] No seed files found in {seed_dir}")
        sys.exit(1)

    prepared_seeds = {}
    for sf in seeds:
        raw = sf.read_text(encoding="utf-8", errors="replace")
        prepared_seeds[sf.name] = prepare_seed(raw)

    print(f"[*] Seeds: {len(seeds)}  Rounds: {rounds}  Timeout: {timeout}s")
    print(f"[*] Z3:   {z3_path}")
    print(f"[*] CVC5: {cvc5_path}")
    print(f"[*] Output: {output_dir}")
    print()

    stats = {
        "total": 0, "deduped": 0,
        "agree_sat": 0, "agree_unsat": 0, "agree_unknown": 0,
        "soundness_bug": 0,
        "z3_crash": 0, "cvc5_crash": 0, "both_crash": 0,
        "z3_error": 0, "cvc5_error": 0, "both_error": 0,
        "disagree_answer": 0, "disagree_other": 0, "both_timeout": 0,
    }

    seen_hashes = set()
    start_time = time.monotonic()

    for i in range(rounds):
        seed_name = random.choice(list(prepared_seeds.keys()))
        seed_content = prepared_seeds[seed_name]

        if i == 0:
            mutated = seed_content
            mutant_id = "seed_original"
        else:
            mutated = mutate_smt(seed_content)
            mut_hash = hashlib.md5(mutated.encode()).hexdigest()[:10]
            # Dedup
            if mut_hash in seen_hashes:
                stats["deduped"] += 1
                continue
            seen_hashes.add(mut_hash)
            mutant_id = f"mut_{i:05d}_{mut_hash}"

        mutant_path = mutants_dir / f"{mutant_id}.smt2"
        mutant_path.write_text(mutated, encoding="utf-8")

        # Run both solvers in parallel
        z3r, cvc5r = run_solvers_parallel(
            z3_path, cvc5_path, mutant_path, timeout, z3_args, cvc5_args)

        category, severity, notes = classify_diff(z3r, cvc5r)

        stats["total"] += 1
        stats[category] = stats.get(category, 0) + 1

        elapsed = time.monotonic() - start_time
        rate = stats["total"] / elapsed if elapsed > 0 else 0

        marker = ""
        if severity == "critical":
            marker = " *** CRITICAL ***"
        elif severity == "high":
            marker = " ** HIGH **"

        if severity != "info":
            print(f"  [{i+1:5d}/{rounds}] {category:20s} "
                  f"Z3={z3r.answer:8s} CVC5={cvc5r.answer:8s} "
                  f"({rate:.1f}/s){marker}")
        elif (i+1) % 100 == 0:
            print(f"  [{i+1:5d}/{rounds}] ... ({rate:.1f}/s) "
                  f"sat={stats['agree_sat']} unsat={stats['agree_unsat']} "
                  f"err={stats.get('cvc5_error',0)} disagree={stats.get('disagree_answer',0)}")

        # Save interesting cases (critical, high, medium, AND disagree)
        if severity in ("critical", "high", "medium") or category.startswith("disagree"):
            save_path = interesting_dir / f"{severity}_{category}_{mutant_id}.smt2"
            try:
                if mutant_path.exists():
                    import shutil
                    shutil.copy2(mutant_path, save_path)
            except Exception:
                pass

            detail_path = interesting_dir / f"{severity}_{category}_{mutant_id}.json"
            detail = {
                "mutant_id": mutant_id, "seed": seed_name,
                "category": category, "severity": severity, "notes": notes,
                "z3": asdict(z3r), "cvc5": asdict(cvc5r),
            }
            try:
                detail_path.write_text(json.dumps(detail, indent=2))
            except Exception:
                pass

        # Clean up non-interesting mutant files to save disk
        if severity == "info" and mutant_path.exists():
            mutant_path.unlink()

    total_time = time.monotonic() - start_time

    report = {
        "timestamp": datetime.now().isoformat(),
        "config": {"seeds": len(seeds), "rounds": rounds, "timeout": timeout},
        "stats": stats,
        "total_time_s": round(total_time, 2),
        "throughput": round(stats["total"] / total_time, 2) if total_time > 0 else 0,
    }

    report_path = output_dir / "fuzz_report.json"
    report_path.write_text(json.dumps(report, indent=2, default=str))

    print(f"\n{'='*60}")
    print(f"  SMT DIFFERENTIAL FUZZING v2 REPORT")
    print(f"{'='*60}")
    print(f"  Total tested:     {stats['total']}")
    print(f"  Deduped/skipped:  {stats['deduped']}")
    print(f"  Time:             {total_time:.1f}s")
    print(f"  Throughput:       {stats['total']/total_time:.1f} tests/s")
    print()
    print(f"  SOUNDNESS BUGS:   {stats.get('soundness_bug', 0)}")
    print(f"  Z3 crashes:       {stats.get('z3_crash', 0)}")
    print(f"  CVC5 crashes:     {stats.get('cvc5_crash', 0)}")
    print(f"  Both crash:       {stats.get('both_crash', 0)}")
    print(f"  Z3 errors:        {stats.get('z3_error', 0)}")
    print(f"  CVC5 errors:      {stats.get('cvc5_error', 0)}")
    print(f"  Both errors:      {stats.get('both_error', 0)}")
    print(f"  Disagree (answer):{stats.get('disagree_answer', 0)}")
    print(f"  Disagree (other): {stats.get('disagree_other', 0)}")
    print(f"  Agree sat:        {stats.get('agree_sat', 0)}")
    print(f"  Agree unsat:      {stats.get('agree_unsat', 0)}")
    print(f"  Agree unknown:    {stats.get('agree_unknown', 0)}")
    print(f"  Both timeout:     {stats.get('both_timeout', 0)}")
    print(f"{'='*60}")
    print(f"  Report: {report_path}")
    print(f"  Interesting: {interesting_dir}")


def main():
    parser = argparse.ArgumentParser(description="SMT Differential Fuzzer v2")
    parser.add_argument("--seeds", required=True)
    parser.add_argument("--z3", required=True)
    parser.add_argument("--cvc5", required=True)
    parser.add_argument("--rounds", type=int, default=5000)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--output-dir", default="./smt_fuzz_v2")
    parser.add_argument("--z3-args", default="")
    parser.add_argument("--cvc5-args", default="")
    args = parser.parse_args()

    run_fuzz_campaign(
        seed_dir=Path(args.seeds),
        z3_path=args.z3,
        cvc5_path=args.cvc5,
        output_dir=Path(args.output_dir),
        rounds=args.rounds,
        timeout=args.timeout,
        z3_args=args.z3_args.split() if args.z3_args else [],
        cvc5_args=args.cvc5_args.split() if args.cvc5_args else [],
    )


if __name__ == "__main__":
    main()
