#!/usr/bin/env python3
"""
classify_results.py — Auto-classify Zipperposition replay results.

Runs each .p file through two harnesses (main + lambda-free check),
classifies the output into fine-grained failure families, and writes
a structured report.

Usage:
    python3 classify_results.py [--zp PATH] [--input-dir DIR] [--output-dir DIR] [--timeout SEC]

Defaults:
    --zp           zipperposition  (on $PATH)
    --input-dir    ~/fyp-isabelle-fuzz/unique_inputs
    --output-dir   ~/fyp-isabelle-fuzz/classify_results
    --timeout      10
"""

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional


# ── Failure family patterns ──────────────────────────────────────────
# Each family is (name, compiled_regex).  Order matters: first match wins.
FAILURE_FAMILIES = [
    ("family_a", re.compile(
        r'Failure\("Argument of a term has out-of-fragment type \[F\d+'
    )),
    ("family_b", re.compile(
        r'Failure\("Argument of a term has out-of-fragment type \[zip_tseitin'
    )),
    ("family_c", re.compile(
        r'Failure\("Constant has out-of-fragment type'
    )),
    ("parse_error", re.compile(
        r'parse error', re.IGNORECASE
    )),
    ("unknown_failure", re.compile(
        r'Failure\(', re.IGNORECASE
    )),
    ("exception", re.compile(
        r'exception|Error|Fatal', re.IGNORECASE
    )),
]


@dataclass
class RunResult:
    file: str
    harness: str          # "main" or "lambda_free"
    exit_code: int
    category: str         # ok | timeout | family_a | family_b | ... | unknown
    matched_line: Optional[str] = None


@dataclass
class Report:
    results: list[RunResult] = field(default_factory=list)
    summary: dict = field(default_factory=dict)


def classify_output(exit_code: int, output: str, timed_out: bool) -> tuple[str, Optional[str]]:
    """Return (category, matched_line) for a single run."""
    if timed_out:
        return "timeout", None
    if exit_code == 0:
        return "ok", None

    # Walk the output lines looking for the first matching family
    for line in output.splitlines():
        for family_name, pattern in FAILURE_FAMILIES:
            if pattern.search(line):
                return family_name, line.strip()

    return "nonzero_other", None


def run_zipperposition(
    zp: str, filepath: Path, extra_args: list[str], timeout: int
) -> tuple[int, str, bool]:
    """Run Zipperposition and return (exit_code, combined_output, timed_out)."""
    cmd = [zp, "--input", "tptp", "--output", "none"] + extra_args + [str(filepath)]
    timed_out = False
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout
        )
        return proc.returncode, proc.stdout + proc.stderr, False
    except subprocess.TimeoutExpired:
        return -1, "", True


def run_all(
    zp: str, input_dir: Path, timeout: int
) -> list[RunResult]:
    """Run both harnesses on every .p file and classify."""
    results = []
    files = sorted(input_dir.glob("*.p"))
    total = len(files)

    harnesses = {
        "main":        ["--steps", "1", "--timeout", "1"],
        "lambda_free": ["--check-lambda-free", "only"],
    }

    for idx, filepath in enumerate(files, 1):
        for harness_name, args in harnesses.items():
            exit_code, output, timed_out = run_zipperposition(
                zp, filepath, args, timeout
            )
            category, matched = classify_output(exit_code, output, timed_out)
            results.append(RunResult(
                file=filepath.name,
                harness=harness_name,
                exit_code=exit_code,
                category=category,
                matched_line=matched,
            ))
        # Progress
        print(f"\r  [{idx}/{total}] {filepath.name}", end="", flush=True)

    print()  # newline after progress
    return results


def build_summary(results: list[RunResult]) -> dict:
    """Group counts by harness × category."""
    summary = {}
    for r in results:
        key = r.harness
        if key not in summary:
            summary[key] = Counter()
        summary[key][r.category] += 1
    # Convert Counter to plain dict for JSON
    return {k: dict(v) for k, v in summary.items()}


def write_report(report: Report, output_dir: Path):
    """Write JSON report + human-readable summary."""
    output_dir.mkdir(parents=True, exist_ok=True)

    # JSON (machine-readable, for further analysis)
    json_path = output_dir / "classify_report.json"
    with open(json_path, "w") as f:
        json.dump(
            {"summary": report.summary, "results": [asdict(r) for r in report.results]},
            f, indent=2,
        )

    # Human-readable summary
    txt_path = output_dir / "classify_summary.txt"
    lines = ["=" * 60, "CLASSIFICATION SUMMARY", "=" * 60, ""]
    for harness, counts in sorted(report.summary.items()):
        lines.append(f"Harness: {harness}")
        for cat, n in sorted(counts.items(), key=lambda x: -x[1]):
            lines.append(f"  {cat:25s} {n:4d}")
        lines.append("")

    # List interesting (non-ok) files
    lines.append("=" * 60)
    lines.append("INTERESTING FILES (non-ok)")
    lines.append("=" * 60)
    for r in report.results:
        if r.category not in ("ok",):
            line = f"  [{r.harness:12s}] {r.category:20s}  {r.file}"
            if r.matched_line:
                line += f"\n{'':38s}→ {r.matched_line[:120]}"
            lines.append(line)

    txt_path.write_text("\n".join(lines) + "\n")

    print(f"\n[*] JSON report:   {json_path}")
    print(f"[*] Text summary:  {txt_path}")


def main():
    parser = argparse.ArgumentParser(description="Classify Zipperposition replay results")
    parser.add_argument("--zp", default="zipperposition", help="Path to Zipperposition binary")
    parser.add_argument("--input-dir", default=str(Path.home() / "fyp-isabelle-fuzz" / "unique_inputs"))
    parser.add_argument("--output-dir", default=str(Path.home() / "fyp-isabelle-fuzz" / "classify_results"))
    parser.add_argument("--timeout", type=int, default=10)
    args = parser.parse_args()

    input_dir = Path(args.input_dir)
    output_dir = Path(args.output_dir)

    if not input_dir.exists():
        print(f"[!] Input directory not found: {input_dir}")
        sys.exit(1)

    files = list(input_dir.glob("*.p"))
    if not files:
        print(f"[!] No .p files in {input_dir}")
        sys.exit(1)

    print(f"[*] Classifying {len(files)} files with Zipperposition: {args.zp}")
    print(f"[*] Timeout: {args.timeout}s per run")

    results = run_all(args.zp, input_dir, args.timeout)
    summary = build_summary(results)
    report = Report(results=results, summary=summary)
    write_report(report, output_dir)


if __name__ == "__main__":
    main()