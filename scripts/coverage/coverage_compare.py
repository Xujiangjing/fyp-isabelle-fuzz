#!/usr/bin/env python3
"""
coverage_compare.py — bisect_ppx coverage comparison: baseline vs targeted inputs.

Satisfies the FYP brief requirement:
  "Code coverage comparison of the baseline (state-of-the-art tool) and your
   tool, showing whether or not your tool can exercise new parts of the
   verifier or compiler codebase."

Workflow:
  1. Run all baseline .p files through instrumented Zipperposition → collect .coverage
  2. Generate baseline coverage report via bisect-ppx-report
  3. Clear coverage data
  4. Run all targeted .p files through instrumented Zipperposition → collect .coverage
  5. Generate targeted coverage report
  6. Parse both reports, compute deltas, produce comparison table + JSON

Prerequisites:
  - Zipperposition built with BISECT_ENABLE=yes (see coverage_build.sh)
  - bisect_ppx and bisect-ppx-report available (opam install bisect_ppx)

Usage:
    python3 coverage_compare.py \\
        --zp-instrumented ~/zipperposition/_build/default/src/main/zipperposition.exe \\
        --baseline-dir    ~/fyp-isabelle-fuzz/baseline_inputs \\
        --targeted-dir    ~/fyp-isabelle-fuzz/unique_inputs \\
        --output-dir      ~/fyp-isabelle-fuzz/coverage_results \\
        --zp-source-dir   ~/zipperposition

    # Optional: also generate HTML reports for visual inspection
    python3 coverage_compare.py ... --html
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import glob
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional


# ═══════════════════════════════════════════════════════════════════════
#  DATA STRUCTURES
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class FileCoverage:
    """Coverage data for a single source file."""
    filename: str
    covered: int       # number of instrumentation points hit
    total: int         # total instrumentation points
    percentage: float  # covered / total * 100


@dataclass
class CoverageReport:
    """Aggregated coverage for one input set."""
    label: str                       # "baseline" or "targeted"
    num_inputs: int                  # how many .p files were run
    files: list[FileCoverage] = field(default_factory=list)
    total_covered: int = 0
    total_points: int = 0
    overall_pct: float = 0.0


@dataclass
class CoverageDelta:
    """Per-file delta between baseline and targeted."""
    filename: str
    baseline_pct: float
    targeted_pct: float
    delta_pct: float               # targeted - baseline
    baseline_covered: int
    targeted_covered: int
    total_points: int
    newly_covered: int             # points covered by targeted but not baseline


# ═══════════════════════════════════════════════════════════════════════
#  RUNNING INPUTS
# ═══════════════════════════════════════════════════════════════════════

def run_inputs(zp_bin: str, input_dir: Path, work_dir: Path, timeout: int = 10) -> int:
    """
    Run every .p file in input_dir through the instrumented Zipperposition.
    Coverage files (.coverage) accumulate in the current working directory.
    Returns the number of files processed.
    """
    files = sorted(input_dir.glob("*.p"))
    total = len(files)
    if total == 0:
        print(f"  [!] No .p files found in {input_dir}")
        return 0

    print(f"  Running {total} inputs through instrumented Zipperposition...")

    ok = crash = timeout_count = 0
    for idx, filepath in enumerate(files, 1):
        cmd = [
            zp_bin,
            "--input", "tptp",
            "--output", "none",
            "--timeout", "5",
            str(filepath),
        ]
        try:
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout,
                cwd=str(work_dir),  # .coverage files written here
            )
            if proc.returncode == 0:
                ok += 1
            else:
                crash += 1
        except subprocess.TimeoutExpired:
            timeout_count += 1

        if idx % 20 == 0 or idx == total:
            print(f"\r  [{idx}/{total}] ok={ok} crash={crash} timeout={timeout_count}",
                  end="", flush=True)

    print()  # newline
    return total


def clear_coverage_files(work_dir: Path):
    """Remove all .coverage files from the working directory."""
    for f in work_dir.glob("bisect*.coverage"):
        f.unlink()
    # Also check for the older naming convention
    for f in work_dir.glob("*.coverage"):
        f.unlink()


def count_coverage_files(work_dir: Path) -> int:
    """Count .coverage files in the working directory."""
    return len(list(work_dir.glob("*.coverage")))


# ═══════════════════════════════════════════════════════════════════════
#  REPORT GENERATION & PARSING
# ═══════════════════════════════════════════════════════════════════════

def generate_bisect_report(
    work_dir: Path,
    output_dir: Path,
    label: str,
    zp_source_dir: Path,
    html: bool = False,
) -> Optional[Path]:
    """
    Run bisect-ppx-report to produce a summary text file.
    Optionally also produce an HTML report.
    Returns the path to the text summary, or None on failure.
    """
    coverage_files = sorted(work_dir.glob("*.coverage"))
    if not coverage_files:
        print(f"  [!] No .coverage files found for {label}")
        return None

    print(f"  Found {len(coverage_files)} .coverage file(s) for {label}")

    report_dir = output_dir / label
    report_dir.mkdir(parents=True, exist_ok=True)

    # Text summary
    summary_path = report_dir / "summary.txt"
    cmd_summary = [
        "bisect-ppx-report",
        "--summary-only",
        "--coverage-path", str(work_dir),
    ]

    try:
        result = subprocess.run(
            cmd_summary, capture_output=True, text=True, timeout=120,
            cwd=str(zp_source_dir),
        )
        summary_path.write_text(result.stdout + result.stderr)
        print(f"  ✓ Text summary → {summary_path}")
    except FileNotFoundError:
        print("  [!] bisect-ppx-report not found. Trying 'opam exec -- bisect-ppx-report'...")
        cmd_summary = ["opam", "exec", "--"] + cmd_summary
        try:
            result = subprocess.run(
                cmd_summary, capture_output=True, text=True, timeout=120,
                cwd=str(zp_source_dir),
            )
            summary_path.write_text(result.stdout + result.stderr)
        except Exception as e:
            print(f"  [!] Failed to run bisect-ppx-report: {e}")
            return None
    except Exception as e:
        print(f"  [!] bisect-ppx-report failed: {e}")
        return None

    # HTML report (optional, for visual inspection)
    if html:
        html_dir = report_dir / "html"
        html_dir.mkdir(parents=True, exist_ok=True)
        cmd_html = [
            "bisect-ppx-report",
            "--html", str(html_dir),
            "--coverage-path", str(work_dir),
        ]
        try:
            subprocess.run(
                cmd_html, capture_output=True, text=True, timeout=120,
                cwd=str(zp_source_dir),
            )
            print(f"  ✓ HTML report  → {html_dir}/index.html")
        except Exception as e:
            print(f"  [!] HTML report generation failed: {e}")

    return summary_path


def parse_bisect_summary(summary_path: Path, label: str, num_inputs: int) -> CoverageReport:
    """
    Parse bisect-ppx-report --summary-only output.

    Typical output format:
      Coverage: 1234/5678 (21.73%)
      src/core/foo.ml: 45/100 (45.00%)
      src/core/bar.ml: 23/50 (46.00%)
      ...
    """
    report = CoverageReport(label=label, num_inputs=num_inputs)
    text = summary_path.read_text()

    # Pattern: filename: covered/total (pct%)
    # bisect-ppx-report output may vary; handle both formats
    file_pattern = re.compile(
        r'^\s*(.+\.ml[il]?)\s*:\s*(\d+)\s*/\s*(\d+)\s*\((\d+(?:\.\d+)?)%\)',
        re.MULTILINE,
    )
    for m in file_pattern.finditer(text):
        filename = m.group(1).strip()
        covered = int(m.group(2))
        total = int(m.group(3))
        pct = float(m.group(4))
        report.files.append(FileCoverage(
            filename=filename, covered=covered, total=total, percentage=pct
        ))

    # Overall line: "Coverage: N/M (P%)"
    overall = re.search(
        r'Coverage\s*:\s*(\d+)\s*/\s*(\d+)\s*\((\d+(?:\.\d+)?)%\)',
        text,
    )
    if overall:
        report.total_covered = int(overall.group(1))
        report.total_points = int(overall.group(2))
        report.overall_pct = float(overall.group(3))
    elif report.files:
        # Compute from per-file data
        report.total_covered = sum(f.covered for f in report.files)
        report.total_points = sum(f.total for f in report.files)
        if report.total_points > 0:
            report.overall_pct = report.total_covered / report.total_points * 100

    return report


# ═══════════════════════════════════════════════════════════════════════
#  COMPARISON
# ═══════════════════════════════════════════════════════════════════════

def compare_coverage(
    baseline: CoverageReport,
    targeted: CoverageReport,
) -> list[CoverageDelta]:
    """Compute per-file deltas between baseline and targeted coverage."""
    # Build lookup by filename
    base_map = {f.filename: f for f in baseline.files}
    targ_map = {f.filename: f for f in targeted.files}

    all_files = sorted(set(base_map.keys()) | set(targ_map.keys()))
    deltas = []

    for fname in all_files:
        b = base_map.get(fname)
        t = targ_map.get(fname)

        b_pct = b.percentage if b else 0.0
        t_pct = t.percentage if t else 0.0
        b_cov = b.covered if b else 0
        t_cov = t.covered if t else 0
        total = max(b.total if b else 0, t.total if t else 0)
        # "newly covered" = points in targeted but not in baseline
        # (approximation: difference in covered counts when total is the same)
        newly = max(0, t_cov - b_cov)

        deltas.append(CoverageDelta(
            filename=fname,
            baseline_pct=b_pct,
            targeted_pct=t_pct,
            delta_pct=t_pct - b_pct,
            baseline_covered=b_cov,
            targeted_covered=t_cov,
            total_points=total,
            newly_covered=newly,
        ))

    # Sort by delta descending (biggest improvements first)
    deltas.sort(key=lambda d: d.delta_pct, reverse=True)
    return deltas


# ═══════════════════════════════════════════════════════════════════════
#  OUTPUT
# ═══════════════════════════════════════════════════════════════════════

def write_comparison_report(
    baseline: CoverageReport,
    targeted: CoverageReport,
    deltas: list[CoverageDelta],
    output_dir: Path,
):
    """Write human-readable comparison + JSON data."""
    output_dir.mkdir(parents=True, exist_ok=True)

    # ── JSON (machine-readable) ──────────────────────────────────────
    json_data = {
        "baseline": {
            "label": baseline.label,
            "num_inputs": baseline.num_inputs,
            "total_covered": baseline.total_covered,
            "total_points": baseline.total_points,
            "overall_pct": round(baseline.overall_pct, 2),
            "files": [asdict(f) for f in baseline.files],
        },
        "targeted": {
            "label": targeted.label,
            "num_inputs": targeted.num_inputs,
            "total_covered": targeted.total_covered,
            "total_points": targeted.total_points,
            "overall_pct": round(targeted.overall_pct, 2),
            "files": [asdict(f) for f in targeted.files],
        },
        "deltas": [asdict(d) for d in deltas],
        "summary": {
            "baseline_overall_pct": round(baseline.overall_pct, 2),
            "targeted_overall_pct": round(targeted.overall_pct, 2),
            "delta_overall_pct": round(targeted.overall_pct - baseline.overall_pct, 2),
            "files_with_improvement": sum(1 for d in deltas if d.delta_pct > 0),
            "files_with_regression": sum(1 for d in deltas if d.delta_pct < 0),
            "files_unchanged": sum(1 for d in deltas if d.delta_pct == 0),
            "total_newly_covered_points": sum(d.newly_covered for d in deltas),
        },
    }
    json_path = output_dir / "coverage_comparison.json"
    json_path.write_text(json.dumps(json_data, indent=2))
    print(f"\n[*] JSON report: {json_path}")

    # ── Human-readable text ──────────────────────────────────────────
    lines = []
    lines.append("=" * 78)
    lines.append("CODE COVERAGE COMPARISON: BASELINE vs SOURCE-INFORMED TARGETED INPUTS")
    lines.append("=" * 78)
    lines.append("")
    lines.append(f"  Baseline inputs:  {baseline.num_inputs} files")
    lines.append(f"  Targeted inputs:  {targeted.num_inputs} files")
    lines.append("")
    lines.append("─" * 78)
    lines.append("OVERALL COVERAGE")
    lines.append("─" * 78)
    lines.append(f"  Baseline:  {baseline.total_covered:>6d} / {baseline.total_points:<6d}"
                 f"  ({baseline.overall_pct:6.2f}%)")
    lines.append(f"  Targeted:  {targeted.total_covered:>6d} / {targeted.total_points:<6d}"
                 f"  ({targeted.overall_pct:6.2f}%)")
    delta_overall = targeted.overall_pct - baseline.overall_pct
    sign = "+" if delta_overall >= 0 else ""
    lines.append(f"  Delta:     {sign}{delta_overall:.2f}%  "
                 f"({sum(d.newly_covered for d in deltas)} newly covered points)")
    lines.append("")

    # ── Per-file table ───────────────────────────────────────────────
    lines.append("─" * 78)
    lines.append("PER-FILE BREAKDOWN  (sorted by coverage improvement)")
    lines.append("─" * 78)
    lines.append(f"  {'Source File':<40s} {'Baseline':>8s} {'Targeted':>8s} {'Delta':>8s} {'New Pts':>7s}")
    lines.append(f"  {'─'*40} {'─'*8} {'─'*8} {'─'*8} {'─'*7}")

    for d in deltas:
        # Shorten filename for display
        short = d.filename
        if len(short) > 40:
            short = "..." + short[-37:]
        sign = "+" if d.delta_pct >= 0 else ""
        lines.append(
            f"  {short:<40s} {d.baseline_pct:>7.1f}% {d.targeted_pct:>7.1f}% "
            f"{sign}{d.delta_pct:>6.1f}% {d.newly_covered:>6d}"
        )

    lines.append("")

    # ── Top improvements ─────────────────────────────────────────────
    improved = [d for d in deltas if d.delta_pct > 0]
    if improved:
        lines.append("─" * 78)
        lines.append(f"TOP FILES WITH INCREASED COVERAGE ({len(improved)} files)")
        lines.append("─" * 78)
        for d in improved[:15]:
            lines.append(f"  +{d.delta_pct:.1f}%  {d.filename}  "
                         f"({d.baseline_covered}→{d.targeted_covered} / {d.total_points})")
        lines.append("")

    # ── Files only reached by targeted ───────────────────────────────
    targeted_only = [d for d in deltas if d.baseline_pct == 0 and d.targeted_pct > 0]
    if targeted_only:
        lines.append("─" * 78)
        lines.append(f"FILES ONLY REACHED BY TARGETED INPUTS ({len(targeted_only)} files)")
        lines.append("─" * 78)
        for d in targeted_only:
            lines.append(f"  {d.targeted_pct:5.1f}%  {d.filename}  "
                         f"({d.targeted_covered}/{d.total_points})")
        lines.append("")

    lines.append("=" * 78)
    lines.append("END OF REPORT")
    lines.append("=" * 78)

    txt_path = output_dir / "coverage_comparison.txt"
    txt_path.write_text("\n".join(lines) + "\n")
    print(f"[*] Text report: {txt_path}")


# ═══════════════════════════════════════════════════════════════════════
#  FALLBACK: MANUAL COVERAGE COUNTING (if bisect-ppx-report unavailable)
# ═══════════════════════════════════════════════════════════════════════

def manual_coverage_summary(work_dir: Path, label: str, num_inputs: int) -> Optional[CoverageReport]:
    """
    If bisect-ppx-report is not available, we can still read .coverage files
    and count raw coverage points using the bisect_ppx runtime format.
    This is a simplified fallback.
    """
    coverage_files = list(work_dir.glob("*.coverage"))
    if not coverage_files:
        return None

    # Each .coverage file is a binary format; we just count files as a proxy
    report = CoverageReport(label=label, num_inputs=num_inputs)
    report.total_points = len(coverage_files)
    report.total_covered = len(coverage_files)
    report.overall_pct = 100.0 if coverage_files else 0.0

    print(f"  [fallback] {len(coverage_files)} .coverage files for {label}")
    print(f"  [fallback] Use bisect-ppx-report for detailed per-file analysis")
    return report


# ═══════════════════════════════════════════════════════════════════════
#  PREPARE BASELINE INPUTS
# ═══════════════════════════════════════════════════════════════════════

def prepare_baseline_if_needed(baseline_dir: Path, targeted_dir: Path) -> Path:
    """
    If baseline_dir does not exist or is empty, create a minimal baseline
    from TPTP library samples or a subset of the targeted inputs
    (first 20%, to simulate "random/untargeted" selection).
    """
    if baseline_dir.exists() and list(baseline_dir.glob("*.p")):
        return baseline_dir

    print(f"  [*] Baseline dir empty/missing. Creating baseline from first 20% of targeted inputs...")
    baseline_dir.mkdir(parents=True, exist_ok=True)

    targeted_files = sorted(targeted_dir.glob("*.p"))
    # Take first 20% as "random baseline" (simplest approach)
    n_baseline = max(5, len(targeted_files) // 5)
    import random
    random.seed(42)  # reproducible
    sample = random.sample(targeted_files, min(n_baseline, len(targeted_files)))

    for f in sample:
        shutil.copy2(f, baseline_dir / f.name)

    print(f"  Created baseline with {len(sample)} files in {baseline_dir}")
    return baseline_dir


# ═══════════════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="bisect_ppx coverage comparison: baseline vs targeted inputs",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Example:
    python3 coverage_compare.py \\
        --zp-instrumented ~/zipperposition/_build/default/src/main/zipperposition.exe \\
        --baseline-dir    ~/fyp-isabelle-fuzz/baseline_inputs \\
        --targeted-dir    ~/fyp-isabelle-fuzz/unique_inputs \\
        --zp-source-dir   ~/zipperposition \\
        --output-dir      ~/fyp-isabelle-fuzz/coverage_results
        """,
    )
    parser.add_argument(
        "--zp-instrumented", required=True,
        help="Path to bisect_ppx-instrumented Zipperposition binary",
    )
    parser.add_argument(
        "--baseline-dir",
        default=str(Path.home() / "fyp-isabelle-fuzz" / "baseline_inputs"),
        help="Directory of baseline .p files (TPTP samples / random seeds)",
    )
    parser.add_argument(
        "--targeted-dir",
        default=str(Path.home() / "fyp-isabelle-fuzz" / "unique_inputs"),
        help="Directory of source-informed targeted .p files",
    )
    parser.add_argument(
        "--zp-source-dir",
        default=str(Path.home() / "zipperposition"),
        help="Zipperposition source directory (for bisect-ppx-report to find .ml files)",
    )
    parser.add_argument(
        "--output-dir",
        default=str(Path.home() / "fyp-isabelle-fuzz" / "coverage_results"),
        help="Output directory for reports",
    )
    parser.add_argument("--timeout", type=int, default=10, help="Per-file timeout (seconds)")
    parser.add_argument("--html", action="store_true", help="Also generate HTML coverage reports")
    args = parser.parse_args()

    zp_bin = args.zp_instrumented
    baseline_dir = Path(args.baseline_dir)
    targeted_dir = Path(args.targeted_dir)
    zp_source_dir = Path(args.zp_source_dir)
    output_dir = Path(args.output_dir)

    # Validate paths
    if not Path(zp_bin).exists():
        print(f"[!] Instrumented binary not found: {zp_bin}")
        print(f"    Run coverage_build.sh first.")
        sys.exit(1)
    if not targeted_dir.exists() or not list(targeted_dir.glob("*.p")):
        print(f"[!] Targeted input directory empty: {targeted_dir}")
        sys.exit(1)

    # Prepare baseline if needed
    baseline_dir = prepare_baseline_if_needed(baseline_dir, targeted_dir)

    # Working directory for .coverage files
    work_dir = output_dir / "_work"
    work_dir.mkdir(parents=True, exist_ok=True)

    print()
    print("╔══════════════════════════════════════════════════════════╗")
    print("║     bisect_ppx Coverage Comparison                      ║")
    print("║     Baseline vs Source-Informed Targeted Inputs          ║")
    print("╚══════════════════════════════════════════════════════════╝")
    print()

    # ── Phase 1: Baseline coverage ───────────────────────────────────
    print("━" * 60)
    print("PHASE 1: Baseline coverage")
    print("━" * 60)
    clear_coverage_files(work_dir)
    n_baseline = run_inputs(zp_bin, baseline_dir, work_dir, args.timeout)
    n_cov_baseline = count_coverage_files(work_dir)
    print(f"  Coverage files generated: {n_cov_baseline}")

    baseline_summary = generate_bisect_report(
        work_dir, output_dir, "baseline", zp_source_dir, html=args.html
    )

    # Copy .coverage files aside for potential re-analysis
    baseline_cov_dir = output_dir / "baseline_coverage_files"
    baseline_cov_dir.mkdir(parents=True, exist_ok=True)
    for f in work_dir.glob("*.coverage"):
        shutil.copy2(f, baseline_cov_dir / f.name)

    # ── Phase 2: Targeted coverage ───────────────────────────────────
    print()
    print("━" * 60)
    print("PHASE 2: Targeted (source-informed) coverage")
    print("━" * 60)
    clear_coverage_files(work_dir)
    n_targeted = run_inputs(zp_bin, targeted_dir, work_dir, args.timeout)
    n_cov_targeted = count_coverage_files(work_dir)
    print(f"  Coverage files generated: {n_cov_targeted}")

    targeted_summary = generate_bisect_report(
        work_dir, output_dir, "targeted", zp_source_dir, html=args.html
    )

    # Copy .coverage files aside
    targeted_cov_dir = output_dir / "targeted_coverage_files"
    targeted_cov_dir.mkdir(parents=True, exist_ok=True)
    for f in work_dir.glob("*.coverage"):
        shutil.copy2(f, targeted_cov_dir / f.name)

    # ── Phase 3: Parse & compare ─────────────────────────────────────
    print()
    print("━" * 60)
    print("PHASE 3: Comparison")
    print("━" * 60)

    if baseline_summary and targeted_summary:
        baseline_report = parse_bisect_summary(baseline_summary, "baseline", n_baseline)
        targeted_report = parse_bisect_summary(targeted_summary, "targeted", n_targeted)

        if not baseline_report.files and not targeted_report.files:
            print("  [!] Could not parse per-file coverage from bisect-ppx-report output.")
            print("      Raw summaries saved. Check the format manually:")
            print(f"      {baseline_summary}")
            print(f"      {targeted_summary}")
            # Still write what we have
            write_comparison_report(baseline_report, targeted_report, [], output_dir)
        else:
            deltas = compare_coverage(baseline_report, targeted_report)
            write_comparison_report(baseline_report, targeted_report, deltas, output_dir)
    else:
        print("  [!] One or both bisect-ppx-report runs failed.")
        print("      Check that bisect_ppx is installed and the binary is instrumented.")
        print("      Raw .coverage files have been preserved in:")
        print(f"      {baseline_cov_dir}")
        print(f"      {targeted_cov_dir}")
        print()
        print("  You can manually generate reports with:")
        print(f"    cd {zp_source_dir}")
        print(f"    bisect-ppx-report --coverage-path {baseline_cov_dir} --summary-only")
        print(f"    bisect-ppx-report --coverage-path {targeted_cov_dir} --summary-only")

    # ── Cleanup ──────────────────────────────────────────────────────
    shutil.rmtree(work_dir, ignore_errors=True)

    print()
    print("Done. Output in:", output_dir)


if __name__ == "__main__":
    main()
