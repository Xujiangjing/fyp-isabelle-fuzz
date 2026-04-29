#!/usr/bin/env python3
"""
differential_fuzz.py — Multi-prover differential fuzzing for Isabelle's ATP interface.

Takes Isabelle-generated TPTP seeds, mutates them, and replays across multiple
ATP backends to find:
  1. CRASH:        A prover segfaults or throws an internal error on valid TPTP
  2. DISAGREEMENT: Prover A says Theorem but Prover B says CounterSatisfiable
  3. HANG:         A prover does not terminate within timeout

This is a grey-box fuzzing approach: we use knowledge of TPTP syntax to guide
mutations while treating the provers as black boxes.

Usage:
    python3 differential_fuzz.py \
        --seed-dir ~/fyp-isabelle-fuzz/unique_inputs \
        --output-dir ~/fyp-isabelle-fuzz/differential_results \
        --mutants 200 \
        --timeout 30

Author: Jiangjing Xu, King's College London
"""

import argparse
import csv
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, asdict, field
from pathlib import Path
from typing import Optional


# ══════════════════════════════════════════════════════════════════════
#  PROVER CONFIGURATION
# ══════════════════════════════════════════════════════════════════════

ISA = Path("/Applications/Isabelle2025-2.app/contrib")

PROVERS = {
    "e": {
        "bin": str(ISA / "e-3.2/arm64-darwin/eprover"),
        "args": ["--tstp-in", "--tstp-out", "--silent", "--auto-schedule",
                 "--cpu-limit={timeout}", "--proof-object=0"],
        "format": "tptp",
    },
    "vampire": {
        "bin": str(ISA / "vampire-4.9-0/x86_64-darwin/vampire"),
        "args": ["--input_syntax", "tptp", "--mode", "casc",
                 "--time_limit", "{timeout}"],
        "format": "tptp",
    },
    "zipperposition": {
        "bin": str(Path.home() / ".opam/default/bin/zipperposition"),
        "args": ["--input", "tptp", "--output", "tptp", "--timeout", "{timeout}"],
        "format": "tptp",
    },
    "spass": {
        # SPASS uses DFG format by default; skip for now since seeds are TPTP
        # Include only if we convert, or use SPASS -TPTP flag
        "bin": str(ISA / "spass-3.8ds/x86_64-darwin/SPASS"),
        "args": ["-TPTP", "-TimeLimit={timeout}"],
        "format": "tptp",
    },
}

# SZS status extraction patterns
SZS_PATTERN = re.compile(r"SZS status\s+(\w+)", re.IGNORECASE)

# Map raw SZS statuses to normalised categories
SZS_POSITIVE = {"Theorem", "Unsatisfiable", "ContradictoryAxioms"}
SZS_NEGATIVE = {"CounterSatisfiable", "Satisfiable"}
SZS_UNKNOWN  = {"Unknown", "GaveUp", "Timeout", "ResourceOut", "Incomplete",
                "Inappropriate", "Error", "InputError"}


def normalise_szs(raw: str) -> str:
    if raw in SZS_POSITIVE:
        return "theorem"
    if raw in SZS_NEGATIVE:
        return "counter"
    if raw in SZS_UNKNOWN:
        return "unknown"
    return "other"


# ══════════════════════════════════════════════════════════════════════
#  MUTATION ENGINE  (TPTP-level, AFL-style havoc)
# ══════════════════════════════════════════════════════════════════════

def mutate_tptp(content: str, intensity: int = 3) -> str:
    """Apply random mutations to a TPTP file. intensity = number of mutations."""
    lines = content.split("\n")
    for _ in range(intensity):
        strategy = random.choice([
            "swap_role", "flip_sign", "drop_line", "dup_line",
            "rename_sym", "inject_keyword", "flip_quantifier",
            "corrupt_parens", "swap_connective", "negate_conjecture",
        ])
        try:
            lines = MUTATORS[strategy](lines)
        except Exception:
            pass  # skip failed mutation, keep going
    return "\n".join(lines)


def _swap_role(lines):
    """Change a random axiom to conjecture or vice versa."""
    candidates = [i for i, l in enumerate(lines)
                  if re.match(r"\s*(tff|fof|thf|cnf)\(", l)]
    if not candidates:
        return lines
    i = random.choice(candidates)
    lines[i] = re.sub(r"\b(axiom|conjecture|hypothesis|lemma)\b",
                       lambda m: random.choice(["axiom", "conjecture", "hypothesis"]),
                       lines[i], count=1)
    return lines


def _flip_sign(lines):
    """Insert or remove a negation."""
    candidates = [i for i, l in enumerate(lines) if "=" in l and "tff(" in l]
    if not candidates:
        return lines
    i = random.choice(candidates)
    if "!=" in lines[i]:
        lines[i] = lines[i].replace("!=", "=", 1)
    elif "= " in lines[i]:
        lines[i] = lines[i].replace("= ", "!= ", 1)
    return lines


def _drop_line(lines):
    """Remove a random formula line."""
    candidates = [i for i, l in enumerate(lines)
                  if re.match(r"\s*(tff|fof|thf|cnf)\(", l) and "conjecture" not in l]
    if not candidates:
        return lines
    i = random.choice(candidates)
    # Find the end of this statement (next line ending with ").")
    j = i
    while j < len(lines) and not lines[j].rstrip().endswith(")."):
        j += 1
    del lines[i:j+1]
    return lines


def _dup_line(lines):
    """Duplicate a random formula."""
    candidates = [i for i, l in enumerate(lines)
                  if re.match(r"\s*(tff|fof|thf|cnf)\(", l)]
    if not candidates:
        return lines
    i = random.choice(candidates)
    j = i
    while j < len(lines) and not lines[j].rstrip().endswith(")."):
        j += 1
    block = lines[i:j+1]
    # Change the name to avoid duplicate
    block[0] = re.sub(r"\(([^,]+),", lambda m: f"(dup_{random.randint(0,9999)}_{m.group(1)},",
                       block[0], count=1)
    lines[j+1:j+1] = block
    return lines


def _rename_sym(lines):
    """Rename a random user symbol to a TPTP keyword (stress-test parsers)."""
    keywords = ["fof", "tff", "cnf", "thf", "include", "type", "axiom"]
    # Find a user symbol
    syms = set()
    for l in lines:
        syms.update(re.findall(r"\b([a-z][a-z0-9_]{2,20})\b", l))
    syms -= set(keywords) | {"tptp", "true", "false"}
    if not syms:
        return lines
    old = random.choice(list(syms))
    new = random.choice(keywords)
    return [l.replace(old, new) for l in lines]


def _inject_keyword(lines):
    """Add a declaration using a TPTP keyword as a symbol name."""
    kw = random.choice(["fof", "tff", "cnf", "thf", "include"])
    decl = f"tff(inject_{random.randint(0,9999)}, type, {kw}: $tType)."
    lines.insert(random.randint(0, len(lines)), decl)
    return lines


def _flip_quantifier(lines):
    """Swap ! (forall) with ? (exists) or vice versa."""
    candidates = [i for i, l in enumerate(lines) if "![" in l or "?[" in l]
    if not candidates:
        return lines
    i = random.choice(candidates)
    if "![" in lines[i]:
        lines[i] = lines[i].replace("![", "?[", 1)
    else:
        lines[i] = lines[i].replace("?[", "![", 1)
    return lines


def _corrupt_parens(lines):
    """Remove or add a parenthesis (test parser robustness)."""
    candidates = [i for i, l in enumerate(lines) if "(" in l and "tff(" not in l[:5]]
    if not candidates:
        return lines
    i = random.choice(candidates)
    if random.random() < 0.5:
        # Remove one paren
        idx = lines[i].rfind(")")
        if idx > 0:
            lines[i] = lines[i][:idx] + lines[i][idx+1:]
    else:
        # Add extra paren
        idx = random.randint(0, len(lines[i]))
        lines[i] = lines[i][:idx] + "(" + lines[i][idx:]
    return lines


def _swap_connective(lines):
    """Swap & with | or => with <=>."""
    swaps = [("&", "|"), ("|", "&"), ("=>", "<=>"), ("<=>", "=>")]
    candidates = [i for i, l in enumerate(lines)
                  if any(old in l for old, _ in swaps)]
    if not candidates:
        return lines
    i = random.choice(candidates)
    old, new = random.choice(swaps)
    lines[i] = lines[i].replace(old, new, 1)
    return lines


def _negate_conjecture(lines):
    """Wrap the conjecture's formula body with ~(...)."""
    for i, l in enumerate(lines):
        if "conjecture" in l and "(" in l:
            # Very rough: find the formula part and negate it
            lines[i] = l.replace("conjecture,", "conjecture, ~(", 1)
            # Find closing ")." and add extra ")"
            for j in range(i, min(i+5, len(lines))):
                if lines[j].rstrip().endswith(")."):
                    lines[j] = lines[j].rstrip()[:-2] + "))."
                    break
            break
    return lines


MUTATORS = {
    "swap_role": _swap_role,
    "flip_sign": _flip_sign,
    "drop_line": _drop_line,
    "dup_line": _dup_line,
    "rename_sym": _rename_sym,
    "inject_keyword": _inject_keyword,
    "flip_quantifier": _flip_quantifier,
    "corrupt_parens": _corrupt_parens,
    "swap_connective": _swap_connective,
    "negate_conjecture": _negate_conjecture,
}


# ══════════════════════════════════════════════════════════════════════
#  PROVER RUNNER
# ══════════════════════════════════════════════════════════════════════

def run_prover(name: str, filepath: Path, timeout: int) -> dict:
    """Run a single prover and return structured result."""
    cfg = PROVERS[name]
    args = [a.replace("{timeout}", str(timeout)) for a in cfg["args"]]
    cmd = [cfg["bin"]] + args + [str(filepath)]

    t0 = time.time()
    timed_out = False
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout + 5)
        exit_code = proc.returncode
        output = proc.stdout + proc.stderr
    except subprocess.TimeoutExpired:
        exit_code = -1
        output = ""
        timed_out = True
    except FileNotFoundError:
        return {"prover": name, "szs": "missing", "norm": "missing",
                "exit": -99, "time": 0, "crash": False, "error": "binary not found"}
    elapsed = time.time() - t0

    # Extract SZS status
    m = SZS_PATTERN.search(output)
    szs_raw = m.group(1) if m else ("Timeout" if timed_out else "Unknown")
    norm = normalise_szs(szs_raw)

    # Detect crashes (segfault, abort, internal error)
    crash = False
    error_snippet = ""
    if exit_code < 0 and not timed_out:
        crash = True
        error_snippet = f"signal {-exit_code}"
    elif exit_code not in (0, 1) and not timed_out:
        crash = True
        error_snippet = output[-300:] if output else f"exit={exit_code}"
    elif any(kw in output.lower() for kw in ["segfault", "fatal", "assertion",
             "stack overflow", "out of memory", "failure(", "exception"]):
        if "Failure(" in output:
            crash = True
            for line in output.splitlines():
                if "Failure(" in line:
                    error_snippet = line.strip()[:200]
                    break

    return {
        "prover": name,
        "szs": szs_raw,
        "norm": norm,
        "exit": exit_code,
        "time": round(elapsed, 2),
        "crash": crash,
        "error": error_snippet,
    }


# ══════════════════════════════════════════════════════════════════════
#  DIFFERENTIAL ANALYSIS
# ══════════════════════════════════════════════════════════════════════

@dataclass
class Finding:
    file: str
    finding_type: str   # "crash" | "disagreement" | "hang"
    severity: str       # "critical" | "high" | "medium" | "low"
    details: dict
    description: str


def analyse_results(filename: str, results: dict[str, dict]) -> list[Finding]:
    """Compare results across provers and flag anomalies."""
    findings = []

    # Check for crashes
    for name, r in results.items():
        if r["crash"]:
            findings.append(Finding(
                file=filename,
                finding_type="crash",
                severity="critical" if "segfault" in r.get("error", "").lower() else "high",
                details={"prover": name, "exit": r["exit"], "error": r["error"]},
                description=f"{name} crashed: {r['error'][:100]}",
            ))

    # Check for disagreements (only among non-crashed, non-timeout results)
    valid = {k: v for k, v in results.items()
             if not v["crash"] and v["norm"] in ("theorem", "counter")}
    norms = set(v["norm"] for v in valid.values())
    if len(norms) > 1:
        detail = {k: v["szs"] for k, v in valid.items()}
        findings.append(Finding(
            file=filename,
            finding_type="disagreement",
            severity="critical",
            details=detail,
            description=f"Provers disagree: {detail}",
        ))

    return findings


# ══════════════════════════════════════════════════════════════════════
#  MAIN PIPELINE
# ══════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Multi-prover differential fuzzing for Isabelle ATP interface")
    parser.add_argument("--seed-dir", required=True, help="Directory with .p seed files")
    parser.add_argument("--output-dir", default=str(Path.home() / "fyp-isabelle-fuzz/differential_results"))
    parser.add_argument("--mutants", type=int, default=200, help="Number of mutants to generate")
    parser.add_argument("--timeout", type=int, default=30, help="Per-prover timeout in seconds")
    parser.add_argument("--intensity", type=int, default=3, help="Mutations per file (1-5)")
    parser.add_argument("--provers", nargs="+", default=["e", "vampire", "zipperposition"],
                        help="Provers to use (default: e vampire zipperposition)")
    parser.add_argument("--seeds-only", action="store_true",
                        help="Run seeds without mutation (baseline)")
    args = parser.parse_args()

    seed_dir = Path(args.seed_dir)
    output_dir = Path(args.output_dir)
    mutant_dir = output_dir / "mutants"
    output_dir.mkdir(parents=True, exist_ok=True)
    mutant_dir.mkdir(parents=True, exist_ok=True)

    seeds = sorted(seed_dir.glob("*.p"))
    if not seeds:
        print(f"[!] No .p files in {seed_dir}")
        sys.exit(1)

    # Validate provers exist
    active_provers = []
    for p in args.provers:
        if p not in PROVERS:
            print(f"[!] Unknown prover: {p}")
            continue
        if not Path(PROVERS[p]["bin"]).exists():
            print(f"[!] Binary not found for {p}: {PROVERS[p]['bin']}")
            continue
        active_provers.append(p)

    if len(active_provers) < 2:
        print(f"[!] Need at least 2 working provers for differential testing, found: {active_provers}")
        sys.exit(1)

    print(f"[*] Seeds: {len(seeds)} files from {seed_dir}")
    print(f"[*] Provers: {', '.join(active_provers)}")
    print(f"[*] Timeout: {args.timeout}s per prover")

    # ── Stage 1: Generate mutants ────────────────────────────────
    if args.seeds_only:
        test_files = seeds
        print(f"[*] Seeds-only mode: testing {len(test_files)} original files")
    else:
        print(f"\n[*] Generating {args.mutants} mutants (intensity={args.intensity})...")
        test_files = list(seeds)  # include originals
        seen_hashes = set()
        for s in seeds:
            seen_hashes.add(hashlib.sha256(s.read_bytes()).hexdigest())

        generated = 0
        attempts = 0
        while generated < args.mutants and attempts < args.mutants * 5:
            attempts += 1
            base = random.choice(seeds)
            content = base.read_text(encoding="utf-8", errors="replace")
            mutated = mutate_tptp(content, intensity=args.intensity)
            h = hashlib.sha256(mutated.encode()).hexdigest()
            if h in seen_hashes:
                continue
            seen_hashes.add(h)
            out_path = mutant_dir / f"mut_{generated:04d}_{base.stem}.p"
            out_path.write_text(mutated, encoding="utf-8")
            test_files.append(out_path)
            generated += 1

        print(f"[*] Generated {generated} unique mutants + {len(seeds)} seeds = {len(test_files)} total")

    # ── Stage 2: Run all provers on all files ────────────────────
    all_results = []  # list of (filename, {prover: result})
    all_findings = []
    stats = Counter()

    total = len(test_files)
    print(f"\n[*] Running {len(active_provers)} provers × {total} files = {len(active_provers)*total} jobs...")
    print(f"[*] Estimated time: ~{len(active_provers)*total*args.timeout//60} min (worst case)\n")

    t_start = time.time()
    for idx, fp in enumerate(test_files, 1):
        results = {}
        for prover in active_provers:
            results[prover] = run_prover(prover, fp, args.timeout)

        filename = fp.name
        all_results.append({"file": filename, "results": results})

        # Analyse
        findings = analyse_results(filename, results)
        all_findings.extend(findings)
        for f in findings:
            stats[f.finding_type] += 1

        # Progress
        statuses = " | ".join(f"{p}:{r['szs'][:8]}" for p, r in results.items())
        marker = " *** FINDING ***" if findings else ""
        elapsed = time.time() - t_start
        eta = elapsed / idx * (total - idx)
        print(f"  [{idx:4d}/{total}] {filename[:40]:40s} {statuses}{marker}  (ETA {eta:.0f}s)")

    # ── Stage 3: Write reports ───────────────────────────────────
    total_time = time.time() - t_start

    # CSV of all results
    csv_path = output_dir / "all_results.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        header = ["file"] + [f"{p}_{field}" for p in active_provers
                             for field in ["szs", "exit", "time", "crash"]]
        w.writerow(header)
        for entry in all_results:
            row = [entry["file"]]
            for p in active_provers:
                r = entry["results"].get(p, {})
                row.extend([r.get("szs", ""), r.get("exit", ""),
                           r.get("time", ""), r.get("crash", "")])
            w.writerow(row)

    # JSON of findings
    findings_path = output_dir / "findings.json"
    with open(findings_path, "w") as f:
        json.dump([asdict(f) for f in all_findings], f, indent=2)

    # Human-readable summary
    summary_path = output_dir / "summary.txt"
    lines = [
        "=" * 70,
        "DIFFERENTIAL FUZZING SUMMARY",
        "=" * 70,
        f"Date:      {time.strftime('%Y-%m-%d %H:%M:%S')}",
        f"Seeds:     {len(seeds)} files",
        f"Mutants:   {len(test_files) - len(seeds)}",
        f"Provers:   {', '.join(active_provers)}",
        f"Timeout:   {args.timeout}s",
        f"Total time: {total_time:.1f}s",
        "",
        "FINDINGS:",
        f"  Crashes:       {stats.get('crash', 0)}",
        f"  Disagreements: {stats.get('disagreement', 0)}",
        f"  Hangs:         {stats.get('hang', 0)}",
        "",
    ]

    if all_findings:
        lines.append("=" * 70)
        lines.append("DETAILED FINDINGS")
        lines.append("=" * 70)
        for f in all_findings:
            lines.append(f"\n  [{f.severity.upper()}] {f.finding_type}: {f.file}")
            lines.append(f"    {f.description}")
            for k, v in f.details.items():
                lines.append(f"    {k}: {v}")
    else:
        lines.append("No findings. All provers agreed and none crashed.")

    # Per-prover stats
    lines.append("\n" + "=" * 70)
    lines.append("PER-PROVER STATUS DISTRIBUTION")
    lines.append("=" * 70)
    for p in active_provers:
        szs_counts = Counter()
        crash_count = 0
        for entry in all_results:
            r = entry["results"].get(p, {})
            szs_counts[r.get("szs", "N/A")] += 1
            if r.get("crash"):
                crash_count += 1
        lines.append(f"\n  {p}:")
        for status, count in szs_counts.most_common():
            lines.append(f"    {status:25s} {count:4d}")
        if crash_count:
            lines.append(f"    {'CRASHES':25s} {crash_count:4d}")

    summary_path.write_text("\n".join(lines) + "\n")

    # Print summary
    print("\n" + "\n".join(lines))
    print(f"\n[*] CSV results:  {csv_path}")
    print(f"[*] Findings:     {findings_path}")
    print(f"[*] Summary:      {summary_path}")
    if all_findings:
        print(f"\n[!] Found {len(all_findings)} issues — check findings.json for details!")


if __name__ == "__main__":
    main()
