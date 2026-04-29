#!/usr/bin/env python3
"""
prepare_baseline.py — Prepare baseline input set for coverage comparison.

Creates a "random/untargeted" baseline by sampling from:
  1. TPTP library problems (if available)
  2. Sledgehammer-exported .p files (simple lemmas, no source-informed targeting)

The point of the baseline: it represents what a naive fuzzer or random test
generator would exercise. Comparing this against our source-informed targeted
inputs shows whether reading the source code to guide input construction
actually improves code coverage.

Usage:
    # From TPTP library (best option if you have TPTP installed)
    python3 prepare_baseline.py --tptp-dir ~/TPTP/Problems --output-dir ~/fyp-isabelle-fuzz/baseline_inputs --sample 100

    # From existing .p files (random subset, no targeting)
    python3 prepare_baseline.py --from-existing ~/fyp-isabelle-fuzz/unique_inputs --output-dir ~/fyp-isabelle-fuzz/baseline_inputs --sample 50

    # Generate trivial FOF/TFF/THF problems as minimal baseline
    python3 prepare_baseline.py --generate --output-dir ~/fyp-isabelle-fuzz/baseline_inputs --count 60
"""

import argparse
import random
import shutil
import sys
from pathlib import Path

random.seed(42)  # reproducible


def sample_tptp(tptp_dir: Path, output_dir: Path, n: int):
    """Sample n problems from the TPTP library."""
    # Collect all .p files recursively
    all_problems = list(tptp_dir.rglob("*.p"))
    if not all_problems:
        print(f"[!] No .p files found in {tptp_dir}")
        sys.exit(1)

    # Prefer a mix of FOF, TFF, THF
    fof = [f for f in all_problems if f.name.startswith(("FOF", "fof")) or "/FOF/" in str(f)]
    tff = [f for f in all_problems if f.name.startswith(("TFF", "tff")) or "/TFF/" in str(f)]
    thf = [f for f in all_problems if f.name.startswith(("THF", "thf")) or "/THF/" in str(f)]
    other = [f for f in all_problems if f not in fof + tff + thf]

    # Proportional sampling
    total_avail = len(all_problems)
    sample = []
    for pool, label in [(fof, "FOF"), (tff, "TFF"), (thf, "THF"), (other, "other")]:
        if pool:
            k = max(1, int(n * len(pool) / total_avail))
            sample.extend(random.sample(pool, min(k, len(pool))))

    # Fill up to n
    remaining = [f for f in all_problems if f not in sample]
    if len(sample) < n and remaining:
        sample.extend(random.sample(remaining, min(n - len(sample), len(remaining))))

    sample = sample[:n]
    output_dir.mkdir(parents=True, exist_ok=True)
    for f in sample:
        shutil.copy2(f, output_dir / f.name)

    print(f"[*] Sampled {len(sample)} problems from TPTP library → {output_dir}")


def sample_existing(existing_dir: Path, output_dir: Path, n: int):
    """Random subset of existing .p files (simulating blind selection)."""
    files = sorted(existing_dir.glob("*.p"))
    if not files:
        print(f"[!] No .p files in {existing_dir}")
        sys.exit(1)

    sample = random.sample(files, min(n, len(files)))
    output_dir.mkdir(parents=True, exist_ok=True)
    for f in sample:
        shutil.copy2(f, output_dir / f"baseline_{f.name}")

    print(f"[*] Sampled {len(sample)} files from {existing_dir} → {output_dir}")


def generate_trivial(output_dir: Path, count: int):
    """
    Generate trivial TPTP problems that exercise only basic parsing paths.
    These do NOT target any specific crash-prone code — they're the control group.
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    templates = {
        "fof": [
            # Simple propositional
            "fof(ax1, axiom, p => q).\nfof(goal, conjecture, p => q).",
            "fof(ax1, axiom, p & q => r).\nfof(ax2, axiom, p).\nfof(ax3, axiom, q).\nfof(goal, conjecture, r).",
            "fof(ax1, axiom, ![X]: (p(X) => q(X))).\nfof(ax2, axiom, p(a)).\nfof(goal, conjecture, q(a)).",
            "fof(ax1, axiom, ![X,Y]: (r(X,Y) => r(Y,X))).\nfof(goal, conjecture, ![X,Y]: (r(X,Y) => r(Y,X))).",
            "fof(ax1, axiom, ?[X]: p(X)).\nfof(goal, conjecture, ?[X]: p(X)).",
        ],
        "tff": [
            "tff(ty, type, a: $i).\ntff(ty2, type, p: $i > $o).\ntff(ax, axiom, p(a)).\ntff(g, conjecture, p(a)).",
            "tff(ty, type, f: $i > $i).\ntff(ax, axiom, ![X: $i]: (f(X) = X)).\ntff(g, conjecture, ![X: $i]: (f(X) = X)).",
            "tff(ty, type, n: $int).\ntff(ax, axiom, $sum(n, 0) = n).\ntff(g, conjecture, $sum(n, 0) = n).",
        ],
        "thf": [
            "thf(ty, type, p: $o).\nthf(ax, axiom, p).\nthf(g, conjecture, p).",
            "thf(ty, type, f: $i > $i).\nthf(ax, axiom, (f = (^[X: $i]: X))).\nthf(g, conjecture, (f = (^[X: $i]: X))).",
            "thf(ty, type, p: $i > $o).\nthf(ty2, type, a: $i).\nthf(ax, axiom, (p @ a)).\nthf(g, conjecture, (p @ a)).",
        ],
    }

    idx = 0
    while idx < count:
        for fmt, tmpls in templates.items():
            for tmpl in tmpls:
                if idx >= count:
                    break
                filename = f"baseline_{fmt}_{idx:04d}.p"
                # Add some variation: extra axioms, different variable names
                content = f"% Baseline problem {idx} ({fmt})\n{tmpl}\n"
                (output_dir / filename).write_text(content)
                idx += 1

    print(f"[*] Generated {count} trivial baseline problems → {output_dir}")


def main():
    parser = argparse.ArgumentParser(description="Prepare baseline inputs for coverage comparison")
    parser.add_argument("--tptp-dir", help="TPTP library Problems directory")
    parser.add_argument("--from-existing", help="Sample from existing .p directory")
    parser.add_argument("--generate", action="store_true", help="Generate trivial problems")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--sample", type=int, default=50, help="Number of files to sample")
    parser.add_argument("--count", type=int, default=60, help="Number of files to generate (with --generate)")
    args = parser.parse_args()

    output_dir = Path(args.output_dir)

    if args.tptp_dir:
        sample_tptp(Path(args.tptp_dir), output_dir, args.sample)
    elif args.from_existing:
        sample_existing(Path(args.from_existing), output_dir, args.sample)
    elif args.generate:
        generate_trivial(output_dir, args.count)
    else:
        print("[!] Specify one of: --tptp-dir, --from-existing, --generate")
        sys.exit(1)


if __name__ == "__main__":
    main()
