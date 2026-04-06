#!/usr/bin/env python3
"""
fuzz_reconstruction.py — Find Sledgehammer proof reconstruction failures.

Strategy:
  Sledgehammer often says "proof found" but the reconstructed proof method
  (metis, smt, meson, etc.) fails when Isabelle tries to check it.
  This is an interface bug between Sledgehammer and the external prover.

  We generate diverse TRUE lemmas, run Sledgehammer with ALL bundled provers,
  and parse the build log to find:
    1. RECONSTRUCT_FAIL: prover found proof, but reconstruction failed
    2. PROVER_CRASH:     prover crashed/errored on valid input
    3. DIFFERENTIAL:     some provers succeed, others crash on same lemma

  The .thy files use `sorry` as fallback so the build never blocks.

Approach:
  - Generate lemmas across many Isabelle domains (arithmetic, lists, sets,
    HOF, type classes, records, options, maps, etc.)
  - Each lemma tries ALL provers: zipperposition, e, vampire, spass, cvc5
  - Parse Isabelle build output for reconstruction results
  - Produce a structured report

Usage:
    # Step 1: Generate theories
    python3 fuzz_reconstruction.py generate --output-dir ~/fyp-isabelle-fuzz/recon_session --count 20

    # Step 2: Run Isabelle build (manually or via this script)
    python3 fuzz_reconstruction.py build --session-dir ~/fyp-isabelle-fuzz/recon_session

    # Step 3: Parse build log for reconstruction failures
    python3 fuzz_reconstruction.py analyse --log ~/fyp-isabelle-fuzz/logs/recon_build.log \
                                           --output-dir ~/fyp-isabelle-fuzz/recon_results
"""

import argparse
import json
import random
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, asdict, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# ══════════════════════════════════════════════════════════════════════
#  LEMMA TEMPLATES — organised by domain and complexity
# ══════════════════════════════════════════════════════════════════════

# Each entry: (formula_template, domain, complexity)
# Templates use {v}, {w} for variable names, filled at generation time.
# All lemmas are TRUE — we only care whether reconstruction works.

LEMMA_POOL = [
    # ── Nat arithmetic ──────────────────────────────────────────────
    ('"{v} + 0 = ({v}::nat)"',                          "nat_arith", "simple"),
    ('"({v}::nat) * 1 = {v}"',                          "nat_arith", "simple"),
    ('"0 + ({v}::nat) = {v}"',                          "nat_arith", "simple"),
    ('"({v}::nat) + {w} = {w} + {v}"',                  "nat_arith", "medium"),
    ('"({v}::nat) * ({w} + 1) = {v} * {w} + {v}"',     "nat_arith", "medium"),
    ('"({v}::nat) + {v} = 2 * {v}"',                    "nat_arith", "medium"),
    ('"Suc ({v}::nat) = {v} + 1"',                      "nat_arith", "simple"),
    ('"({v}::nat) + Suc {w} = Suc ({v} + {w})"',       "nat_arith", "medium"),
    ('"({v}::nat) \\<le> {v}"',                         "nat_arith", "simple"),
    ('"({v}::nat) < {v} + 1"',                          "nat_arith", "simple"),
    ('"min ({v}::nat) {w} \\<le> max {v} {w}"',         "nat_arith", "medium"),
    ('"min ({v}::nat) {v} = {v}"',                      "nat_arith", "simple"),
    ('"max ({v}::nat) {v} = {v}"',                      "nat_arith", "simple"),

    # ── Int arithmetic ──────────────────────────────────────────────
    ('"({v}::int) + 0 = {v}"',                          "int_arith", "simple"),
    ('"({v}::int) + {w} = {w} + {v}"',                  "int_arith", "medium"),
    ('"({v}::int) * (-1) = -{v}"',                      "int_arith", "medium"),
    ('"({v}::int) - {v} = 0"',                          "int_arith", "simple"),
    ('"\\<bar>({v}::int)\\<bar> \\<ge> 0"',             "int_arith", "medium"),

    # ── List operations ─────────────────────────────────────────────
    ('"length [{v}] = (1::nat)"',                       "list", "simple"),
    ('"hd [{v}] = ({v}::nat)"',                         "list", "simple"),
    ('"tl [{v}] = ([]::nat list)"',                     "list", "simple"),
    ('"rev [{v}] = [({v}::nat)]"',                      "list", "simple"),
    ('"rev (rev xs) = (xs::nat list)"',                 "list", "medium"),
    ('"length (xs @ ys) = length xs + length (ys::nat list)"', "list", "medium"),
    ('"map id xs = (xs::nat list)"',                    "list", "medium"),
    ('"filter (\\<lambda>x. True) xs = (xs::nat list)"', "list", "medium"),
    ('"concat [xs, ys] = xs @ (ys::nat list)"',         "list", "medium"),
    ('"length (map f xs) = length (xs::nat list)"',     "list", "medium"),
    ('"rev (xs @ ys) = rev ys @ rev (xs::nat list)"',   "list", "hard"),
    ('"length (replicate n x) = (n::nat)"',             "list", "medium"),
    ('"set (xs @ ys) = set xs \\<union> set (ys::nat list)"', "list", "hard"),
    ('"distinct [({v}::nat)]"',                         "list", "simple"),
    ('"sorted [(1::nat), 2, 3]"',                       "list", "simple"),
    ('"butlast [{v}, {w}] = [({v}::nat)]"',             "list", "medium"),
    ('"last [{v}, {w}] = ({w}::nat)"',                  "list", "medium"),
    ('"nth [{v}, {w}] 0 = ({v}::nat)"',                 "list", "medium"),
    ('"nth [{v}, {w}] 1 = ({w}::nat)"',                 "list", "medium"),
    ('"take 1 [{v}, {w}] = [({v}::nat)]"',              "list", "medium"),
    ('"drop 1 [{v}, {w}] = [({w}::nat)]"',              "list", "medium"),
    ('"zip [({v}::nat)] [{w}] = [({v}, {w})]"',         "list", "medium"),

    # ── Set operations ──────────────────────────────────────────────
    ('"({v}::nat) \\<in> set [{v}, {w}]"',              "set", "simple"),
    ('"set [{v}, {w}] = set [{w}, ({v}::nat)]"',        "set", "medium"),
    ('"set [{v}] \\<union> set [{w}] = set [{v}, ({w}::nat)]"', "set", "medium"),
    ('"set [{v}] \\<inter> set [{v}, {w}] = set [({v}::nat)]"', "set", "hard"),
    ('"card (set [({v}::nat)]) \\<le> 1"',              "set", "medium"),
    ('"finite (set [{v}, ({w}::nat)])"',                "set", "simple"),
    ('"set ([] :: nat list) = {}"',                     "set", "simple"),

    # ── Option type ─────────────────────────────────────────────────
    ('"the (Some ({v}::nat)) = {v}"',                   "option", "simple"),
    ('"Option.is_none (None :: nat option)"',           "option", "simple"),
    ('"\\<not> Option.is_none (Some ({v}::nat))"',      "option", "simple"),

    # ── Product/pair operations ─────────────────────────────────────
    ('"fst ({v}, {w}) = ({v}::nat)"',                   "pair", "simple"),
    ('"snd ({v}, {w}) = ({w}::nat)"',                   "pair", "simple"),

    # ── Boolean/logic ───────────────────────────────────────────────
    ('"({v}::nat) = {v} \\<or> False"',                 "logic", "simple"),
    ('"True \\<longrightarrow> ({v}::nat) = {v}"',      "logic", "simple"),
    ('"(\\<forall>x::nat. x = x)"',                     "logic", "simple"),
    ('"(\\<exists>x::nat. x = 0)"',                     "logic", "simple"),
    ('"\\<not> False"',                                  "logic", "simple"),
    ('"True \\<and> True"',                              "logic", "simple"),
    ('"(P \\<longrightarrow> Q) \\<longrightarrow> (\\<not> Q \\<longrightarrow> \\<not> P)"', "logic", "medium"),
    ('"(P \\<and> Q) = (Q \\<and> P)"',                  "logic", "medium"),
    ('"(P \\<or> Q) = (Q \\<or> P)"',                    "logic", "medium"),

    # ── Higher-order / lambda ───────────────────────────────────────
    ('"(\\<lambda>x::nat. x) {v} = {v}"',               "hof", "simple"),
    ('"(\\<lambda>x::nat. x + 1) {v} = {v} + 1"',      "hof", "simple"),
    ('"map (\\<lambda>x. x + 1) [({v}::nat)] = [{v} + 1]"', "hof", "medium"),
    ('"filter (\\<lambda>x. True) [(1::nat)] = [1]"',   "hof", "medium"),

    # ── Fun update / function manipulation ──────────────────────────
    ('"(\\<lambda>x::nat. 0)(({v}::nat) := 1) {v} = 1"', "fun", "medium"),

    # ── Division and modulo (often tricky for ATPs) ─────────────────
    ('"(4::nat) div 2 = 2"',                            "divmod", "medium"),
    ('"(5::nat) mod 2 = 1"',                            "divmod", "medium"),
    ('"(0::nat) div 1 = 0"',                            "divmod", "simple"),
    ('"({v}::nat) div 1 = {v}"',                        "divmod", "medium"),
    ('"({v}::nat) mod 1 = 0"',                          "divmod", "medium"),

    # ── Power / exponential ─────────────────────────────────────────
    ('"(2::nat) ^ 0 = 1"',                              "power", "simple"),
    ('"(2::nat) ^ 1 = 2"',                              "power", "simple"),
    ('"({v}::nat) ^ 1 = {v}"',                          "power", "medium"),
    ('"(1::nat) ^ {v} = 1"',                            "power", "medium"),

    # ── Sum type ────────────────────────────────────────────────────
    ('"isl (Inl ({v}::nat) :: nat + nat)"',             "sum", "simple"),
    ('"\\<not> isl (Inr ({v}::nat) :: nat + nat)"',     "sum", "simple"),

    # ── If-then-else ────────────────────────────────────────────────
    ('"(if True then ({v}::nat) else {w}) = {v}"',      "ite", "simple"),
    ('"(if False then ({v}::nat) else {w}) = {w}"',     "ite", "simple"),
    ('"(if ({v}::nat) = {v} then 1 else 0) = 1"',      "ite", "medium"),

    # ── Let bindings ────────────────────────────────────────────────
    ('"(let x = ({v}::nat) in x + 1) = {v} + 1"',      "let", "medium"),
    ('"(let x = ({v}::nat); y = {w} in x + y) = {v} + {w}"', "let", "medium"),

    # ── Recursive / inductive definitions ───────────────────────────
    ('"sum_list [(1::nat), 2, 3] = 6"',                 "recursive", "medium"),
    ('"length (replicate 5 (0::nat)) = 5"',             "recursive", "medium"),
]

# All bundled provers to test
PROVERS = ["zipperposition", "e", "vampire", "spass", "cvc5"]

SAFE_VARS = ["x", "y", "z", "a", "b", "m", "n", "u", "v", "w"]


# ══════════════════════════════════════════════════════════════════════
#  GENERATE: Create .thy files that test reconstruction
# ══════════════════════════════════════════════════════════════════════

def pick_lemmas(count: int) -> list[tuple[str, str, str]]:
    """Pick `count` lemmas from the pool, ensuring domain diversity."""
    by_domain = defaultdict(list)
    for entry in LEMMA_POOL:
        by_domain[entry[1]].append(entry)

    selected = []
    domains = list(by_domain.keys())

    # First: at least one from each domain
    for d in domains:
        if len(selected) >= count:
            break
        entry = random.choice(by_domain[d])
        selected.append(entry)

    # Then fill remaining randomly
    while len(selected) < count:
        entry = random.choice(LEMMA_POOL)
        selected.append(entry)

    random.shuffle(selected)
    return selected[:count]


def generate_theory(theory_name: str, lemmas_per_theory: int = 15,
                    provers: list[str] = None) -> str:
    """Generate a single .thy file.

    Each lemma gets a separate sledgehammer call for EACH prover.
    We use `oops` as fallback so the build never blocks on a failed lemma.
    The key output we parse is Sledgehammer's log lines.
    """
    if provers is None:
        provers = PROVERS

    selected = pick_lemmas(lemmas_per_theory)

    lines = [
        f"theory {theory_name}",
        "imports Main",
        "begin",
        "",
    ]

    lemma_id = 0
    for formula_template, domain, complexity in selected:
        v = random.choice(SAFE_VARS)
        w = random.choice([x for x in SAFE_VARS if x != v])

        try:
            formula = formula_template.format(v=v, w=w)
        except (KeyError, IndexError):
            formula = f'"{v} = ({v}::nat)"'

        lemma_id += 1
        tag = f"{domain}__{complexity}__{lemma_id}"

        # Each prover gets its own sledgehammer call on the same lemma
        for prover in provers:
            lines.append(f'lemma {tag}_{prover}: {formula}')
            lines.append(
                f'  sledgehammer [prover = {prover}, slices = 1, '
                f'timeout = 30, overlord]'
            )
            lines.append("  oops")
            lines.append("")

    lines.append("end")
    return "\n".join(lines)


def cmd_generate(args):
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    # Clean old subdirs
    import shutil
    for p in out.iterdir():
        if p.is_dir():
            shutil.rmtree(p)
    for p in out.glob("*.thy"):
        p.unlink()
    for p in out.glob("ROOT"):
        p.unlink()

    provers = args.provers.split(",") if args.provers else PROVERS

    theories = []
    for i in range(args.count):
        name = f"Recon{i:03d}"
        content = generate_theory(
            name,
            lemmas_per_theory=args.lemmas,
            provers=provers,
        )
        # Each theory in its own subdirectory
        sub = out / name
        sub.mkdir(parents=True, exist_ok=True)
        (sub / f"{name}.thy").write_text(content, encoding="utf-8")
        root_lines = [
            f"session {name} = HOL +",
            f"  theories",
            f"    {name}",
        ]
        (sub / "ROOT").write_text("\n".join(root_lines) + "\n")
        theories.append(name)

    total_lemmas = args.count * args.lemmas * len(provers)
    print(f"[*] Generated {args.count} theories × {args.lemmas} lemmas × "
          f"{len(provers)} provers = {total_lemmas} sledgehammer calls")
    print(f"[*] Provers: {', '.join(provers)}")
    print(f"[*] Output: {out}")
    print(f"[*] Each theory is its own session in a subdirectory")
    print(f"[*] Next: run  python3 fuzz_reconstruction.py build --session-dir {out}")


# ══════════════════════════════════════════════════════════════════════
#  BUILD: Run isabelle build and capture log
# ══════════════════════════════════════════════════════════════════════

def cmd_build(args):
    session_dir = Path(args.session_dir)
    log_dir = Path(args.log_dir)
    log_dir.mkdir(parents=True, exist_ok=True)

    run_id = datetime.now().strftime("%Y%m%d_%H%M%S")
    build_log = log_dir / f"recon_build_{run_id}.log"

    # Find all subdirectories with ROOT files
    subdirs = sorted([d for d in session_dir.iterdir()
                      if d.is_dir() and (d / "ROOT").exists()])

    if not subdirs:
        print(f"[!] No session subdirectories found in {session_dir}")
        sys.exit(1)

    print(f"[*] Building {len(subdirs)} sessions in {session_dir}")
    print(f"[*] Log: {build_log}")
    print(f"[*] This will take a while...")

    all_logs = []
    session_names = []
    succeeded = 0
    failed = 0

    for i, sub in enumerate(subdirs, 1):
        name = sub.name
        session_names.append(name)
        print(f"  [{i}/{len(subdirs)}] Building {name}...", end="", flush=True)
        result = subprocess.run(
            ["isabelle", "build", "-c", "-v", "-j1", "-o", "threads=1",
             "-D", str(sub)],
            capture_output=True, text=True,
        )

        if result.returncode == 0:
            succeeded += 1
            print(" OK", end="")
        else:
            failed += 1
            print(" FAILED", end="")

        # Extract detailed log via isabelle build_log
        blog = subprocess.run(
            ["isabelle", "build_log", name],
            capture_output=True, text=True,
        )
        detail = blog.stdout + blog.stderr
        all_logs.append(
            f"{'='*60}\n"
            f"SESSION: {name}\n"
            f"{'='*60}\n"
            f"{detail}\n"
        )
        # Count results inline
        tries = detail.count("Try this:")
        print(f" ({tries} proofs found)")

    full_log = "\n".join(all_logs)
    build_log.write_text(full_log)

    print(f"\n[*] Build finished: {succeeded} OK, {failed} FAILED")
    print(f"[*] Log written to {build_log}")
    print(f"[*] Next: run  python3 fuzz_reconstruction.py analyse --log {build_log}")

    # Quick grep for interesting lines
    found = full_log.count("Try this:")
    no_proof = full_log.count("found no proof")
    timed_out = full_log.count("Timed out")
    print(f"[*] Quick stats: {found} 'Try this:', {no_proof} 'no proof', "
          f"{timed_out} 'Timed out'")


# ══════════════════════════════════════════════════════════════════════
#  ANALYSE: Parse build log for reconstruction failures
# ══════════════════════════════════════════════════════════════════════

@dataclass
class ReconResult:
    theory: str
    lemma_tag: str           # e.g. "nat_arith__simple__1_zipperposition"
    prover: str
    domain: str
    complexity: str
    outcome: str             # found_and_ok | found_but_fail | no_proof | timeout | error
    method: Optional[str]    # the "by ..." method suggested, if any
    error_snippet: Optional[str] = None


def parse_build_log(log_path: Path) -> list[ReconResult]:
    """Parse combined isabelle build_log output.

    Format from `isabelle build_log`:
      Output (line NN of "~/path/TheoryName.thy"):
      Sledgehammering...
      Output (line NN of "~/path/TheoryName.thy"):
      zipperposition found a proof...
      Output (line NN of "~/path/TheoryName.thy"):
      zipperposition: Try this: by simp (1 ms)
      Output (line NN of "~/path/TheoryName.thy"):
      Done

    Or for failures:
      Output (line NN of "~/path/TheoryName.thy"):
      Sledgehammer found no proof
    """
    log_text = log_path.read_text(encoding="utf-8", errors="replace")
    results = []

    current_session = "unknown"
    current_theory = "unknown"
    current_line_no = 0

    lines = log_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]

        # Detect session boundary
        m = re.match(r'^={5,}\s*$', line)
        if m and i + 1 < len(lines) and lines[i + 1].startswith("SESSION:"):
            current_session = lines[i + 1].replace("SESSION:", "").strip()
            i += 2
            continue

        # Detect theory
        m = re.match(r'Theory "([^"]+)"', line)
        if m:
            current_theory = m.group(1)

        # Detect "Output (line NN of ...)" — this gives us the line number
        m = re.match(r'Output \(line (\d+) of "([^"]+)"\):', line)
        if m:
            current_line_no = int(m.group(1))
            thy_file = m.group(2)
            # Extract theory name from path
            tm = re.search(r'(\w+)\.thy', thy_file)
            if tm:
                current_theory = tm.group(1)

        # Detect "PROVER found a proof..."
        m = re.match(r'^(\w+) found a proof', line)
        if m:
            prover = m.group(1)
            # Look ahead for the "Try this:" line
            method = None
            for j in range(i + 1, min(i + 5, len(lines))):
                tm = re.search(r'Try this:\s*(.*?)(?:\s*\([\d.]+ (?:ms|s)\))?$',
                               lines[j])
                if tm:
                    method = tm.group(1).strip()
                    break
                # Also match "PROVER: Try this: ..."
                tm = re.search(r'^\w+:\s*Try this:\s*(.*?)(?:\s*\([\d.]+ (?:ms|s)\))?$',
                               lines[j])
                if tm:
                    method = tm.group(1).strip()
                    break

            # Look up the lemma tag from the .thy file using line number
            lemma_tag = _lookup_lemma_tag(current_session, current_line_no,
                                          Path(args_session_dir) if 'args_session_dir' in dir() else None)

            domain, complexity = "unknown", "unknown"
            # Try to parse from lemma tag
            if lemma_tag and "__" in lemma_tag:
                parts = lemma_tag.rsplit("_", 1)  # strip prover suffix
                if parts:
                    tag_parts = parts[0].split("__")
                    if len(tag_parts) >= 2:
                        domain = tag_parts[0]
                        complexity = tag_parts[1]

            results.append(ReconResult(
                theory=current_theory,
                lemma_tag=f"line_{current_line_no}_{prover}",
                prover=prover,
                domain=domain,
                complexity=complexity,
                outcome="found_and_ok" if method else "found_but_fail",
                method=method,
            ))

        # Detect "Sledgehammer found no proof" or "PROVER found no proof"
        if "found no proof" in line.lower():
            m = re.match(r'^(\w+) found no proof', line)
            prover = m.group(1) if m else "unknown"
            results.append(ReconResult(
                theory=current_theory,
                lemma_tag=f"line_{current_line_no}_{prover}",
                prover=prover,
                domain="unknown",
                complexity="unknown",
                outcome="no_proof",
                method=None,
            ))

        # Detect "Timed out"
        if "timed out" in line.lower():
            m = re.match(r'^(\w+)\s+timed out', line, re.IGNORECASE)
            prover = m.group(1) if m else "unknown"
            results.append(ReconResult(
                theory=current_theory,
                lemma_tag=f"line_{current_line_no}_{prover}",
                prover=prover,
                domain="unknown",
                complexity="unknown",
                outcome="timeout",
                method=None,
            ))

        # Detect errors/crashes
        if any(kw in line.lower() for kw in [
            "prover error", "failure(", "exception", "parse error",
        ]):
            m = re.match(r'^(\w+)', line)
            prover = m.group(1) if m and m.group(1).lower() not in [
                "output", "at", "the", "error", "fatal"
            ] else "unknown"
            results.append(ReconResult(
                theory=current_theory,
                lemma_tag=f"line_{current_line_no}_{prover}",
                prover=prover,
                domain="unknown",
                complexity="unknown",
                outcome="error",
                method=None,
                error_snippet=line.strip()[:200],
            ))

        # Detect reconstruction failure patterns
        if any(kw in line.lower() for kw in [
            "one-line proof could not be found",
            "reconstruction failed",
            "proof failed",
        ]):
            m = re.match(r'^(\w+)', line)
            prover = m.group(1) if m and m.group(1).lower() not in [
                "output", "at", "the", "a"
            ] else "unknown"
            results.append(ReconResult(
                theory=current_theory,
                lemma_tag=f"line_{current_line_no}_{prover}",
                prover=prover,
                domain="unknown",
                complexity="unknown",
                outcome="found_but_fail",
                method=None,
                error_snippet=line.strip()[:200],
            ))

        i += 1

    return results


def _lookup_lemma_tag(session_name: str, line_no: int, session_dir: Optional[Path]) -> Optional[str]:
    """Try to find the lemma name at a given line in the .thy file."""
    # This is best-effort; if we can't find it, return None
    return None


def cmd_analyse(args):
    log_path = Path(args.log)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    if not log_path.exists():
        print(f"[!] Log file not found: {log_path}")
        sys.exit(1)

    print(f"[*] Parsing build log: {log_path}")
    results = parse_build_log(log_path)
    print(f"[*] Found {len(results)} sledgehammer result entries")

    if not results:
        print("[!] No results parsed. The log format might not match.")
        print("[!] You may need to adjust the regexes in parse_build_log().")
        print("[!] Saving raw log analysis anyway...")
        # Save a diagnostic: show first 100 lines that contain sledgehammer-related keywords
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        interesting = [l for l in log_text.splitlines()
                       if any(kw in l.lower() for kw in
                              ["sledgehammer", "try this", "proof", "error",
                               "timeout", "failure", "no proof"])]
        diag_path = output_dir / "diagnostic_lines.txt"
        diag_path.write_text("\n".join(interesting[:200]) + "\n")
        print(f"[*] Wrote diagnostic lines to {diag_path}")
        print("[*] Check this file and adjust the parser accordingly.")
        return

    # ── Build summary ──
    by_outcome = Counter(r.outcome for r in results)
    by_prover_outcome = defaultdict(Counter)
    for r in results:
        by_prover_outcome[r.prover][r.outcome] += 1

    by_domain_outcome = defaultdict(Counter)
    for r in results:
        by_domain_outcome[r.domain][r.outcome] += 1

    # ── Find differential results ──
    # Group by base lemma (strip prover suffix)
    by_base_lemma = defaultdict(dict)
    for r in results:
        base = r.lemma_tag
        for p in PROVERS:
            if base.endswith(f"_{p}"):
                base = base[:-(len(p) + 1)]
                break
        by_base_lemma[base][r.prover] = r.outcome

    differentials = []
    for base, prover_outcomes in by_base_lemma.items():
        outcomes = set(prover_outcomes.values())
        if len(outcomes) > 1:
            differentials.append((base, dict(prover_outcomes)))

    # ── Reconstruction failures ──
    recon_failures = [r for r in results if r.outcome == "found_but_fail"]
    errors = [r for r in results if r.outcome == "error"]

    # ── Write JSON report ──
    report = {
        "summary": {
            "total_entries": len(results),
            "by_outcome": dict(by_outcome),
            "by_prover": {p: dict(c) for p, c in by_prover_outcome.items()},
            "by_domain": {d: dict(c) for d, c in by_domain_outcome.items()},
        },
        "reconstruction_failures": [asdict(r) for r in recon_failures],
        "prover_errors": [asdict(r) for r in errors],
        "differential_results": differentials[:50],  # top 50
        "all_results": [asdict(r) for r in results],
    }

    json_path = output_dir / "recon_report.json"
    with open(json_path, "w") as f:
        json.dump(report, f, indent=2)

    # ── Write human-readable summary ──
    txt_path = output_dir / "recon_summary.txt"
    lines = [
        "=" * 60,
        "PROOF RECONSTRUCTION ANALYSIS",
        "=" * 60, "",
        f"Total sledgehammer calls parsed: {len(results)}", "",
        "── Overall outcomes ──",
    ]
    for outcome, count in sorted(by_outcome.items(), key=lambda x: -x[1]):
        lines.append(f"  {outcome:25s} {count:4d}")

    lines += ["", "── By prover ──"]
    for prover in PROVERS:
        if prover in by_prover_outcome:
            lines.append(f"  {prover}:")
            for outcome, count in sorted(by_prover_outcome[prover].items(),
                                         key=lambda x: -x[1]):
                lines.append(f"    {outcome:25s} {count:4d}")

    lines += ["", "── By domain ──"]
    for domain, counts in sorted(by_domain_outcome.items()):
        lines.append(f"  {domain}:")
        for outcome, count in sorted(counts.items(), key=lambda x: -x[1]):
            lines.append(f"    {outcome:25s} {count:4d}")

    lines += [
        "", "=" * 60,
        "RECONSTRUCTION FAILURES (proof found but reconstruction failed)",
        "=" * 60, "",
    ]
    if recon_failures:
        for r in recon_failures:
            lines.append(f"  [{r.prover:15s}] {r.lemma_tag}")
            if r.error_snippet:
                lines.append(f"    {r.error_snippet[:150]}")
    else:
        lines.append("  None found in this run.")

    lines += [
        "", "=" * 60,
        "PROVER ERRORS / CRASHES",
        "=" * 60, "",
    ]
    if errors:
        for r in errors:
            lines.append(f"  [{r.prover:15s}] {r.lemma_tag}")
            if r.error_snippet:
                lines.append(f"    {r.error_snippet[:150]}")
    else:
        lines.append("  None found in this run.")

    lines += [
        "", "=" * 60,
        f"DIFFERENTIAL RESULTS ({len(differentials)} lemmas with mixed outcomes)",
        "=" * 60, "",
    ]
    for base, po in differentials[:20]:
        lines.append(f"  {base}:")
        for prover, outcome in sorted(po.items()):
            lines.append(f"    {prover:18s} → {outcome}")

    txt_path.write_text("\n".join(lines) + "\n")

    print(f"\n{'='*60}")
    print(f"  Total parsed:              {len(results)}")
    print(f"  Reconstruction failures:   {len(recon_failures)}")
    print(f"  Prover errors/crashes:     {len(errors)}")
    print(f"  Differential results:      {len(differentials)}")
    print(f"{'='*60}")
    print(f"[*] JSON report:  {json_path}")
    print(f"[*] Summary:      {txt_path}")


# ══════════════════════════════════════════════════════════════════════
#  CLI
# ══════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Fuzz Sledgehammer proof reconstruction across all provers"
    )
    sub = parser.add_subparsers(dest="cmd")

    # Generate
    p_gen = sub.add_parser("generate", help="Generate .thy files for reconstruction testing")
    p_gen.add_argument("--output-dir", required=True, help="Where to write .thy files")
    p_gen.add_argument("--count", type=int, default=20, help="Number of .thy files")
    p_gen.add_argument("--lemmas", type=int, default=15, help="Lemmas per .thy file")
    p_gen.add_argument("--provers", default=None,
                       help="Comma-separated prover list (default: all 5)")

    # Build
    p_build = sub.add_parser("build", help="Run isabelle build and capture log")
    p_build.add_argument("--session-dir", required=True)
    p_build.add_argument("--log-dir",
                         default=str(Path.home() / "fyp-isabelle-fuzz" / "logs"))

    # Analyse
    p_analyse = sub.add_parser("analyse", help="Parse build log for reconstruction failures")
    p_analyse.add_argument("--log", required=True, help="Path to build log file")
    p_analyse.add_argument("--output-dir",
                           default=str(Path.home() / "fyp-isabelle-fuzz" / "recon_results"))

    args = parser.parse_args()
    if args.cmd == "generate":
        cmd_generate(args)
    elif args.cmd == "build":
        cmd_build(args)
    elif args.cmd == "analyse":
        cmd_analyse(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()