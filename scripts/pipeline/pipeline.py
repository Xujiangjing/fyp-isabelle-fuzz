#!/usr/bin/env python3
"""
pipeline.py — One-command fuzzing pipeline for Isabelle-Sledgehammer-ATP interface.

Stages:
  1. Generate / mutate seeds (.thy or .p)
  2. Export via Sledgehammer (if .thy input)
  3. Dedup collected .p files
  4. Replay through Zipperposition harnesses
  5. Classify results into failure families
  6. Write report

Usage:
    # Full pipeline: generate .thy → Sledgehammer → replay → classify
    python3 pipeline.py full --rounds 10 --zp /path/to/zipperposition

    # TPTP-only: mutate existing .p files → replay → classify (no Isabelle needed)
    python3 pipeline.py tptp-only --input-dir ~/fyp-isabelle-fuzz/unique_inputs \
                                  --mutants 100 --zp /path/to/zipperposition

    # Classify-only: just re-classify existing inputs
    python3 pipeline.py classify-only --input-dir ~/fyp-isabelle-fuzz/unique_inputs \
                                      --zp /path/to/zipperposition
"""

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

# Import our modules (same directory)
from classify_results import run_all, build_summary, write_report, Report
from mutate import generate_mutated_thy, mutate_tptp


BASE = Path.home() / "fyp-isabelle-fuzz"


def stage_banner(name: str):
    print(f"\n{'='*60}")
    print(f"  STAGE: {name}")
    print(f"{'='*60}\n")


# ── Stage 1: Generate seeds ─────────────────────────────────────────

def stage_generate_thy(session_dir: Path, round_id: int, count_per_round: int = 10):
    """Generate mutated .thy files for one round."""
    import random

    # Clean old .thy files
    for p in session_dir.glob("*.thy"):
        p.unlink()
    root = session_dir / "ROOT"
    if root.exists():
        root.unlink()

    theories = []
    for i in range(count_per_round):
        name = f"R{round_id:03d}_Mut{i:03d}"
        content = generate_mutated_thy(name, num_lemmas=random.randint(5, 15))
        (session_dir / f"{name}.thy").write_text(content, encoding="utf-8")
        theories.append(name)

    # Write ROOT
    root_lines = ["session AutoSeeds = HOL +", "  theories"]
    for th in theories:
        root_lines.append(f"    {th}")
    (session_dir / "ROOT").write_text("\n".join(root_lines) + "\n")

    print(f"  Generated {len(theories)} .thy files in {session_dir}")
    return theories


# ── Stage 2: Sledgehammer export ────────────────────────────────────

def stage_sledgehammer_export(session_dir: Path, collect_dir: Path, log_dir: Path) -> list[Path]:
    """Run isabelle build and collect .p files."""
    isabelle_home = Path.home() / ".isabelle"
    run_id = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_out = collect_dir / f"run_{run_id}"
    run_out.mkdir(parents=True, exist_ok=True)
    log_dir.mkdir(parents=True, exist_ok=True)
    build_log = log_dir / f"build_{run_id}.log"

    # Clean old problem files
    for f in isabelle_home.rglob("prob_*.p"):
        f.unlink()

    print(f"  Running isabelle build (this may take a while)...")
    result = subprocess.run(
        ["isabelle", "build", "-c", "-j1", "-o", "threads=1", "-D", str(session_dir)],
        capture_output=True, text=True,
    )
    build_log.write_text(result.stdout + result.stderr)

    # Collect .p files
    collected = []
    for f in sorted(isabelle_home.rglob("prob_*.p")):
        dest = run_out / f"{run_id}_{f.name}"
        shutil.copy2(f, dest)
        collected.append(dest)

    print(f"  Collected {len(collected)} .p files → {run_out}")
    if result.returncode != 0:
        print(f"  [!] Build had non-zero exit. Check log: {build_log}")

    return collected


# ── Stage 3: Dedup ──────────────────────────────────────────────────

def stage_dedup(source_dir: Path, dest_dir: Path) -> int:
    """SHA256 dedup of .p files."""
    dest_dir.mkdir(parents=True, exist_ok=True)

    # Clear destination
    for f in dest_dir.glob("*.p"):
        f.unlink()

    seen = {}
    count = 0
    for f in sorted(source_dir.rglob("*.p")):
        if f.name.endswith("_proof.p"):
            continue
        h = hashlib.sha256(f.read_bytes()).hexdigest()
        if h not in seen:
            out = dest_dir / f"{count:04d}_{f.name}"
            shutil.copy2(f, out)
            seen[h] = f.name
            count += 1

    print(f"  Deduped: {count} unique .p files → {dest_dir}")
    return count


# ── Stage 4+5: Replay + Classify ───────────────────────────────────

def stage_classify(zp: str, input_dir: Path, output_dir: Path, timeout: int = 10):
    """Run both harnesses and classify results."""
    results = run_all(zp, input_dir, timeout)
    summary = build_summary(results)
    report = Report(results=results, summary=summary)
    write_report(report, output_dir)

    # Print quick summary
    print("\n  Quick summary:")
    for harness, counts in sorted(summary.items()):
        print(f"    {harness}:")
        for cat, n in sorted(counts.items(), key=lambda x: -x[1]):
            print(f"      {cat:25s} {n}")

    return report


# ── Stage: TPTP mutation (no Isabelle) ──────────────────────────────

def stage_mutate_tptp(input_dir: Path, output_dir: Path, count: int) -> int:
    """Mutate existing .p files."""
    import random

    output_dir.mkdir(parents=True, exist_ok=True)
    seeds = list(input_dir.glob("*.p"))
    if not seeds:
        print(f"  [!] No .p files in {input_dir}")
        return 0

    for i in range(count):
        base = random.choice(seeds)
        content = base.read_text(encoding="utf-8", errors="replace")
        mutated = mutate_tptp(content)
        (output_dir / f"mut_{i:04d}_{base.name}").write_text(mutated, encoding="utf-8")

    print(f"  Generated {count} mutated .p files → {output_dir}")
    return count


# ══════════════════════════════════════════════════════════════════════
#  PIPELINE MODES
# ══════════════════════════════════════════════════════════════════════

def cmd_full(args):
    """Full pipeline: generate → export → dedup → classify."""
    session_dir = BASE / "session"
    collect_dir = BASE / "collected"
    master_dir = BASE / "master_seeds"
    unique_dir = BASE / "unique_inputs"
    log_dir = BASE / "logs"
    report_dir = BASE / "classify_results"

    for d in [session_dir, collect_dir, master_dir, unique_dir, log_dir]:
        d.mkdir(parents=True, exist_ok=True)

    start = time.time()

    for round_id in range(1, args.rounds + 1):
        stage_banner(f"Round {round_id}/{args.rounds} — Generate")
        stage_generate_thy(session_dir, round_id)

        stage_banner(f"Round {round_id}/{args.rounds} — Sledgehammer export")
        collected = stage_sledgehammer_export(session_dir, collect_dir, log_dir)

        # Merge into master
        for f in collected:
            shutil.copy2(f, master_dir / f"r{round_id:03d}_{f.name}")

    stage_banner("Dedup")
    stage_dedup(master_dir, unique_dir)

    stage_banner("Classify")
    stage_classify(args.zp, unique_dir, report_dir, args.timeout)

    elapsed = time.time() - start
    print(f"\n[*] Full pipeline done in {elapsed:.1f}s")


def cmd_tptp_only(args):
    """TPTP-only: mutate .p files → classify (no Isabelle needed)."""
    input_dir = Path(args.input_dir)
    mutated_dir = BASE / "mutated_p"
    combined_dir = BASE / "combined_inputs"
    report_dir = BASE / "classify_results"

    stage_banner("Mutate TPTP files")
    stage_mutate_tptp(input_dir, mutated_dir, args.mutants)

    stage_banner("Combine original + mutated")
    combined_dir.mkdir(parents=True, exist_ok=True)
    for f in combined_dir.glob("*.p"):
        f.unlink()

    count = 0
    for src in [input_dir, mutated_dir]:
        for f in sorted(src.glob("*.p")):
            dest = combined_dir / f"{count:04d}_{f.name}"
            shutil.copy2(f, dest)
            count += 1

    stage_banner("Dedup")
    unique_dir = BASE / "unique_combined"
    stage_dedup(combined_dir, unique_dir)

    stage_banner("Classify")
    stage_classify(args.zp, unique_dir, report_dir, args.timeout)


def cmd_classify_only(args):
    """Just classify existing inputs."""
    input_dir = Path(args.input_dir)
    report_dir = Path(args.output_dir) if args.output_dir else BASE / "classify_results"

    stage_banner("Classify")
    stage_classify(args.zp, input_dir, report_dir, args.timeout)


def main():
    parser = argparse.ArgumentParser(
        description="Unified fuzzing pipeline for Isabelle-Sledgehammer-ATP"
    )
    parser.add_argument("--zp", default="zipperposition", help="Path to Zipperposition")
    parser.add_argument("--timeout", type=int, default=10, help="Per-file timeout in seconds")

    sub = parser.add_subparsers(dest="mode")

    # Full pipeline
    p_full = sub.add_parser("full", help="Full pipeline: .thy → Sledgehammer → classify")
    p_full.add_argument("--rounds", type=int, default=10)

    # TPTP-only
    p_tptp = sub.add_parser("tptp-only", help="Mutate .p files → classify (no Isabelle)")
    p_tptp.add_argument("--input-dir", required=True)
    p_tptp.add_argument("--mutants", type=int, default=100)

    # Classify-only
    p_cls = sub.add_parser("classify-only", help="Classify existing .p files")
    p_cls.add_argument("--input-dir", required=True)
    p_cls.add_argument("--output-dir", default=None)

    args = parser.parse_args()
    if args.mode == "full":
        cmd_full(args)
    elif args.mode == "tptp-only":
        cmd_tptp_only(args)
    elif args.mode == "classify-only":
        cmd_classify_only(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()