#!/usr/bin/env python3
"""
fuzz_sledgehammer_tptp_v2.py
---------------------------------
A more reliable source-informed fuzzer for Sledgehammer's TPTP generation.

Main improvements over v1:
  - Build ONE theory at a time
  - Clean old prob_*.p files before each build
  - Recursively search ~/.isabelle for new prob_*.p files
  - Preserve mapping: theory -> collected .p file(s)
  - Emit a manifest JSON for reproducibility
  - More conservative discrepancy classification

Typical workflow:
  1) Generate theories
     python3 fuzz_sledgehammer_tptp_v2.py generate \
         --output-dir ~/fyp-isabelle-fuzz/sledgehammer_attack_v2

  2) Collect TPTP problems by building theories one-by-one
     python3 fuzz_sledgehammer_tptp_v2.py collect \
         --session-dir ~/fyp-isabelle-fuzz/sledgehammer_attack_v2

  3) Differentially test collected .p files
     python3 fuzz_sledgehammer_tptp_v2.py test \
         --input-dir ~/fyp-isabelle-fuzz/sledgehammer_attack_v2/collected_p \
         --zp ~/zipperposition-test/_build/default/src/main/zipperposition.exe \
         --e /Applications/Isabelle2025.app/contrib/e-3.1-1/x86_64-darwin/eprover \
         --vampire /opt/homebrew/bin/vampire
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Optional, List, Dict, Tuple


# ---------------------------------------------------------------------------
# Theory generation
# ---------------------------------------------------------------------------

def build_lemma_list(prover: str):
    sh = f"sledgehammer [prover = {prover}, slices = 1, timeout = 30, overlord]"
    lemmas = []

    def add(name, lemma, imports="Main", preamble=""):
        lemmas.append((name, imports, preamble, lemma, sh))

    # === ATTACK SURFACE 1: Symbol escaping ===
    for kw in ["fof", "tff", "cnf", "thf", "include"]:
        add(f"kw_{kw}", f'"({kw}::nat) = {kw}"')
    for name in ["implies", "iff", "xor", "equal", "apply"]:
        add(f"conn_{name}", f'"({name}::nat) = {name}"')
    for role in ["axiom", "hypothesis", "conjecture", "plain", "unknown", "corollary"]:
        add(f"role_{role}", f'"({role}::nat) = {role}"')
    for sym in ["ite", "distinct", "sum", "product", "difference", "quotient", "uminus", "floor", "ceiling"]:
        add(f"dollar_{sym}", f'"({sym}::nat) = {sym}"')
    for name in ["int", "nat", "bool", "set", "list", "option"]:
        add(f"shadow_{name}", f'"({name}::nat) = {name}"')
    add("short_O", '"(O::nat) = O"')
    add("short_I", '"(I::nat) = I"')
    add("short_T", '"(T::nat) = T"')
    add("long_name", f'"({"a" * 80}::nat) = {"a" * 80}"')
    add("kw_pair_fof_tff", '"(fof::nat) + tff = tff + fof"')

    # === ATTACK SURFACE 2: Type encoding ===
    for ty in ["nat", "int", "bool"]:
        add(f"type_{ty}", f'"(x::{ty}) = x"')
    add("type_nat_list", '"(x::nat list) = x"')
    add("type_int_list", '"(x::int list) = x"')
    add("type_nat_set", '"(x::nat set) = x"')
    add("type_nat_option", '"(x::nat option) = x"')
    add("type_list_list", '"(x::nat list list) = x"')
    add("type_option_list", '"(x::nat option list) = x"')
    add("type_list_option", '"(x::nat list option) = x"')
    add("type_poly_a", '"(x::\'a) = x"')
    add("type_poly_list", '"(x::\'a list) = x"')
    add("type_poly_fun", '"(f::\'a \\<Rightarrow> \'b) = f"')
    add("type_prod", '"fst (a, b) = (a::nat)"')
    add("type_prod_nested", '"fst (fst ((a, b), c)) = (a::nat)"')

    # === ATTACK SURFACE 3: Formula structure ===
    add("deep_add", '"((((((x::nat) + 0) + 0) + 0) + 0) + 0) = x"')
    add("ite_simple", '"(if True then (x::nat) else 0) = x"')
    add("ite_nested", '"(if True then (if False then 0 else (x::nat)) else 0) = x"')
    add("let_simple", '"(let y = (x::nat) in y) = x"')
    add("let_multi", '"(let y = (x::nat); z = y in z) = x"')
    add("let_nested", '"(let y = (let z = (x::nat) in z) in y) = x"')
    add("lambda_id", '"(\\<lambda>x::nat. x) y = (y::nat)"')
    add("lambda_const", '"(\\<lambda>x::nat. 0) y = (0::nat)"')
    add("lambda_nested", '"(\\<lambda>x::nat. \\<lambda>y::nat. x + y) a b = a + (b::nat)"')
    add("case_nat", '"(case (0::nat) of 0 \\<Rightarrow> True | Suc n \\<Rightarrow> False)"')
    add("case_list", '"(case [x::nat] of [] \\<Rightarrow> 0 | y # ys \\<Rightarrow> y) = x"')
    add("case_option", '"(case Some (x::nat) of None \\<Rightarrow> 0 | Some v \\<Rightarrow> v) = x"')
    add("forall_simple", '"\\<forall>x::nat. x + 0 = x"')
    add("exists_simple", '"\\<exists>x::nat. x = 0"')
    add("nested_quant", '"\\<forall>x::nat. \\<exists>y::nat. y = x"')
    add("bool_eq", '"((x::nat) = y) = ((y::nat) = x)"')
    add("large_num", '"(2147483647::nat) + 1 = 2147483648"')
    add("neg_int", '"(- (1::int)) + 1 = 0"')
    add("div_nat", '"(6::nat) div 2 = 3"')
    add("mod_nat", '"(7::nat) mod 3 = 1"')
    add("list_rev", '"rev (rev xs) = (xs::nat list)"')
    add("list_append", '"length (xs @ ys) = length xs + length (ys::nat list)"')
    add("set_member", '"(x::nat) \\<in> set [x, y]"')

    # === ATTACK SURFACE 4: Special constructs ===
    add(
        "dt_color",
        '"\\<forall>c::color. c = Red \\<or> c = Green \\<or> c = Blue"',
        preamble="datatype color = Red | Green | Blue\n"
    )
    add(
        "dt_tree",
        '"Leaf \\<noteq> Node Leaf (0::nat) Leaf"',
        preamble="datatype nat_tree = Leaf | Node nat_tree nat nat_tree\n"
    )
    add(
        "dt_param",
        '"Nil \\<noteq> Cons (0::nat) Nil"',
        preamble="datatype 'a mylist = Nil | Cons 'a \"'a mylist\"\n"
    )
    add(
        "primrec_len",
        '"mylen [] = (0::nat)"',
        preamble=(
            "primrec mylen :: \"'a list \\<Rightarrow> nat\" where\n"
            "  \"mylen [] = 0\"\n"
            "| \"mylen (x # xs) = Suc (mylen xs)\"\n"
        )
    )
    add(
        "fun_fib",
        '"fib 0 = (0::nat)"',
        preamble=(
            "fun fib :: \"nat \\<Rightarrow> nat\" where\n"
            "  \"fib 0 = 0\"\n"
            "| \"fib (Suc 0) = 1\"\n"
            "| \"fib (Suc (Suc n)) = fib n + fib (Suc n)\"\n"
        )
    )
    add(
        "record_point",
        '"xcoord (\\<lparr> xcoord = 1, ycoord = 2 \\<rparr>) = (1::nat)"',
        preamble=(
            "record point =\n"
            "  xcoord :: nat\n"
            "  ycoord :: nat\n"
        )
    )

    return lemmas


def write_root_file(out: Path, theories: List[str]):
    root = ["session SledgehammerAttackV2 = HOL +", "  theories"]
    for th in theories:
        root.append(f"    {th}")
    (out / "ROOT").write_text("\n".join(root) + "\n", encoding="utf-8")


def cmd_generate(args):
    out = Path(args.output_dir).expanduser().resolve()
    out.mkdir(parents=True, exist_ok=True)

    prover = args.prover
    lemmas = build_lemma_list(prover)

    multi = []
    base = [
        ("mp_refl", "Main", "", '"(x::nat) = x"'),
        ("mp_comm", "Main", "", '"(x::nat) + y = y + x"'),
        ("mp_lambda", "Main", "", '"(\\<lambda>x::nat. x) y = (y::nat)"'),
        ("mp_kw_fof", "Main", "", '"(fof::nat) = fof"'),
    ]
    for bname, imp, pre, lem in base:
        for p in ["zipperposition", "e", "vampire"]:
            sh = f"sledgehammer [prover = {p}, slices = 1, timeout = 30, overlord]"
            multi.append((f"{bname}_{p}", imp, pre, lem, sh))

    all_lemmas = lemmas + multi
    theories = []
    manifest = []

    for name, imports, preamble, lemma_stmt, sh_cmd in all_lemmas:
        thy_name = f"A_{name}"
        content = (
            f"theory {thy_name}\n"
            f"imports {imports}\n"
            f"begin\n\n"
            f"{preamble}\n"
            f"lemma test_{name}: {lemma_stmt}\n"
            f"  {sh_cmd}\n"
            f"  oops\n\n"
            f"end\n"
        )
        (out / f"{thy_name}.thy").write_text(content, encoding="utf-8")
        theories.append(thy_name)
        manifest.append({
            "theory": thy_name,
            "lemma_name": f"test_{name}",
            "imports": imports,
            "preamble": preamble,
            "lemma_stmt": lemma_stmt,
            "sledgehammer_cmd": sh_cmd,
        })

    write_root_file(out, theories)
    (out / "generation_manifest.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8"
    )

    print(f"[*] Generated {len(theories)} theories -> {out}")
    print(f"[*] Session name: SledgehammerAttackV2")
    print()
    print("Next step:")
    print(f"  python3 {Path(__file__).name} collect --session-dir {out}")


# ---------------------------------------------------------------------------
# Collect overlord .p files by building theories one-by-one
# ---------------------------------------------------------------------------

def find_isabelle_prob_files() -> List[Path]:
    home = Path.home()
    isabelle_root = home / ".isabelle"
    if not isabelle_root.exists():
        return []
    return sorted(isabelle_root.rglob("prob_*.p"))


def remove_old_prob_files(verbose: bool = False) -> int:
    files = find_isabelle_prob_files()
    removed = 0
    for f in files:
        try:
            f.unlink()
            removed += 1
            if verbose:
                print(f"    removed old: {f}")
        except Exception as e:
            print(f"[warn] Failed to remove {f}: {e}", file=sys.stderr)
    return removed


def md5_bytes(data: bytes) -> str:
    return hashlib.md5(data).hexdigest()


def safe_read_bytes(path: Path) -> bytes:
    with open(path, "rb") as fh:
        return fh.read()


def collect_new_prob_files(before: Dict[str, float]) -> List[Path]:
    """
    Compare current prob_*.p files with a 'before' snapshot.
    A file is considered new if:
      - it wasn't in the snapshot, or
      - its mtime increased.
    """
    current = find_isabelle_prob_files()
    new_files = []
    for p in current:
        key = str(p)
        mtime = p.stat().st_mtime
        if key not in before or mtime > before[key]:
            new_files.append(p)
    return sorted(new_files)


def snapshot_prob_files() -> Dict[str, float]:
    snap = {}
    for p in find_isabelle_prob_files():
        try:
            snap[str(p)] = p.stat().st_mtime
        except FileNotFoundError:
            pass
    return snap


def extract_prover_from_prob_name(path: Path) -> str:
    m = re.match(r"prob_([A-Za-z0-9_+-]+)_\d+\.p$", path.name)
    if m:
        return m.group(1)
    return "unknown"


def run_isabelle_build_for_theory(session_dir: Path, theory: str, timeout: int) -> Tuple[int, str]:
    """
    Build the session directory. Since the session ROOT contains all generated theories,
    this compiles the session; however, our collection strategy is one-theory-at-a-time
    through temporary ROOT rewriting.
    """
    cmd = [
        "isabelle", "build",
        "-d", str(session_dir),
        "-o", f"timeout={timeout}",
        "SledgehammerAttackV2",
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    output = (proc.stdout or "") + "\n" + (proc.stderr or "")
    return proc.returncode, output


def write_single_theory_root(session_dir: Path, theory: str):
    root = [
        "session SledgehammerAttackV2 = HOL +",
        "  theories",
        f"    {theory}",
    ]
    (session_dir / "ROOT").write_text("\n".join(root) + "\n", encoding="utf-8")


def restore_root(session_dir: Path, original_root: str):
    (session_dir / "ROOT").write_text(original_root, encoding="utf-8")


def cmd_collect(args):
    session_dir = Path(args.session_dir).expanduser().resolve()
    collected_dir = session_dir / "collected_p"
    logs_dir = session_dir / "build_logs"
    collected_dir.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    root_path = session_dir / "ROOT"
    if not root_path.exists():
        print(f"[!] ROOT not found in {session_dir}", file=sys.stderr)
        sys.exit(1)

    theories = sorted(p.stem for p in session_dir.glob("A_*.thy"))
    if not theories:
        print(f"[!] No A_*.thy theories found in {session_dir}", file=sys.stderr)
        sys.exit(1)

    original_root = root_path.read_text(encoding="utf-8")
    manifest = []

    print(f"[*] Found {len(theories)} theories")
    print(f"[*] Collected .p files -> {collected_dir}")
    print()

    try:
        for idx, theory in enumerate(theories, 1):
            print(f"[{idx:4d}/{len(theories)}] Building {theory}")

            removed = remove_old_prob_files(verbose=False)
            if removed:
                print(f"         cleaned {removed} old prob_*.p files")

            before = snapshot_prob_files()
            write_single_theory_root(session_dir, theory)

            rc, build_output = run_isabelle_build_for_theory(
                session_dir=session_dir,
                theory=theory,
                timeout=args.build_timeout,
            )

            log_path = logs_dir / f"{theory}.log"
            log_path.write_text(build_output, encoding="utf-8")

            new_prob_files = collect_new_prob_files(before)

            copied = []
            for src in new_prob_files:
                try:
                    data = safe_read_bytes(src)
                    digest = md5_bytes(data)[:12]
                    prover = extract_prover_from_prob_name(src)
                    dst_name = f"{theory}__{prover}__{src.name}__{digest}.p"
                    dst = collected_dir / dst_name
                    dst.write_bytes(data)
                    copied.append({
                        "source_path": str(src),
                        "copied_path": str(dst),
                        "source_name": src.name,
                        "prover_from_name": prover,
                        "md5_prefix": digest,
                    })
                except Exception as e:
                    copied.append({
                        "source_path": str(src),
                        "copy_error": str(e),
                    })

            build_status = "ok" if rc == 0 else "build_failed"
            manifest.append({
                "theory": theory,
                "build_returncode": rc,
                "build_status": build_status,
                "log_path": str(log_path),
                "num_prob_files": len(new_prob_files),
                "copied": copied,
            })

            if copied:
                print(f"         captured {len(copied)} prob file(s)")
            else:
                print(f"         captured 0 prob files")

    finally:
        restore_root(session_dir, original_root)

    manifest_path = session_dir / "collection_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print()
    print("=" * 60)
    print("COLLECTION SUMMARY")
    print("=" * 60)
    print(f"Theories processed: {len(theories)}")
    print(f"Manifest: {manifest_path}")
    print(f"Collected dir: {collected_dir}")
    print("=" * 60)


# ---------------------------------------------------------------------------
# Differential testing
# ---------------------------------------------------------------------------

@dataclass
class ProverResult:
    solver: str
    exit_code: int
    answer: str
    elapsed_ms: int
    raw_output: str
    error_msg: Optional[str] = None


def classify_solver_output(proc_returncode: int, output: str) -> Tuple[str, Optional[str]]:
    out_lower = output.lower()

    m = re.search(r"SZS status\s+([A-Za-z_]+)", output)
    if m:
        return m.group(1), None

    if proc_returncode < 0:
        return "Crash", "terminated by signal"

    if "parse error" in out_lower or "syntax error" in out_lower:
        for line in output.splitlines():
            if "parse error" in line.lower() or "syntax error" in line.lower():
                return "ParseError", line.strip()[:300]
        return "ParseError", "parse/syntax error"

    if re.search(r'Failure\(', output) or "fatal error" in out_lower:
        for line in output.splitlines():
            if "Failure(" in line or "fatal error" in line.lower():
                return "Crash", line.strip()[:300]
        return "Crash", "failure/fatal error"

    # "exception" alone is too broad; do not auto-upgrade to Crash.
    if "exception" in out_lower:
        for line in output.splitlines():
            if "exception" in line.lower():
                return "Error", line.strip()[:300]
        return "Error", "exception in output"

    if "error" in out_lower:
        for line in output.splitlines():
            if "error" in line.lower():
                return "Error", line.strip()[:300]
        return "Error", "generic error"

    if "time limit" in out_lower or "timeout" in out_lower:
        return "Timeout", "timeout"

    return "Unknown", None


def run_prover(solver_path: str, solver_name: str, filepath: Path, timeout: int = 30) -> ProverResult:
    if solver_name == "zipperposition":
        cmd = [solver_path, "--input", "tptp", "--output", "tptp", "--timeout", str(timeout), str(filepath)]
    elif solver_name == "e":
        cmd = [solver_path, "--auto", "--tptp3-format", f"--cpu-limit={timeout}", str(filepath)]
    elif solver_name == "vampire":
        cmd = [solver_path, "--input_syntax", "tptp", "--time_limit", str(timeout), str(filepath)]
    else:
        cmd = [solver_path, str(filepath)]

    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 5)
        elapsed = int((time.monotonic() - start) * 1000)
        output = (proc.stdout or "") + "\n" + (proc.stderr or "")
        answer, error_msg = classify_solver_output(proc.returncode, output)
        return ProverResult(
            solver=solver_name,
            exit_code=proc.returncode,
            answer=answer,
            elapsed_ms=elapsed,
            raw_output=output[:4000],
            error_msg=error_msg,
        )
    except subprocess.TimeoutExpired:
        elapsed = int((time.monotonic() - start) * 1000)
        return ProverResult(
            solver=solver_name,
            exit_code=-1,
            answer="Timeout",
            elapsed_ms=elapsed,
            raw_output="TIMEOUT",
            error_msg="timeout",
        )
    except FileNotFoundError as e:
        return ProverResult(
            solver=solver_name,
            exit_code=-999,
            answer="ToolMissing",
            elapsed_ms=0,
            raw_output=str(e),
            error_msg=str(e),
        )


def validate_solver_paths(provers: Dict[str, str]):
    bad = []
    for name, path in provers.items():
        p = Path(path).expanduser()
        if not p.exists():
            bad.append((name, str(p)))
    if bad:
        print("[!] Missing solver path(s):", file=sys.stderr)
        for name, path in bad:
            print(f"    {name}: {path}", file=sys.stderr)
        sys.exit(1)


def extract_metadata_from_collected_name(filename: str) -> Dict[str, str]:
    """
    Expected format:
      THEORY__PROVER__prob_xxx_n.p__HASH.p
    """
    m = re.match(r"^(.*?)__(.*?)__(prob_.*?\.p)__(.*?)\.p$", filename)
    if not m:
        return {
            "theory": "unknown",
            "overlord_prover": "unknown",
            "original_prob_name": filename,
            "hash": "unknown",
        }
    return {
        "theory": m.group(1),
        "overlord_prover": m.group(2),
        "original_prob_name": m.group(3),
        "hash": m.group(4),
    }


def cmd_test(args):
    input_dir = Path(args.input_dir).expanduser().resolve()
    output_dir = Path(args.output_dir).expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    files = sorted(input_dir.glob("*.p"))
    if not files:
        print(f"[!] No .p files in {input_dir}", file=sys.stderr)
        sys.exit(1)

    provers = {}
    if args.zp:
        provers["zipperposition"] = str(Path(args.zp).expanduser())
    if args.e:
        provers["e"] = str(Path(args.e).expanduser())
    if args.vampire:
        provers["vampire"] = str(Path(args.vampire).expanduser())

    if not provers:
        print("[!] Specify at least one prover (--zp, --e, --vampire)", file=sys.stderr)
        sys.exit(1)

    validate_solver_paths(provers)

    print(f"[*] Testing {len(files)} .p files against {list(provers.keys())}")
    print()

    findings = []

    for idx, f in enumerate(files, 1):
        meta = extract_metadata_from_collected_name(f.name)
        results = {pn: run_prover(pp, pn, f, timeout=args.timeout) for pn, pp in provers.items()}
        answers = {pn: r.answer for pn, r in results.items()}

        status = " | ".join(f"{pn}={ans}" for pn, ans in answers.items())

        crashes = [pn for pn, r in results.items() if r.answer == "Crash"]
        parse_err = [pn for pn, r in results.items() if r.answer == "ParseError"]
        theorem = [pn for pn, r in results.items() if r.answer == "Theorem"]
        csat = [pn for pn, r in results.items() if r.answer == "CounterSatisfiable"]

        classification = None
        severity = None
        description = None

        if crashes:
            classification = "crash_candidate"
            severity = "high"
            description = f"{', '.join(crashes)} crashed"
        elif theorem and csat:
            classification = "soundness_candidate"
            severity = "high"
            description = f"{', '.join(theorem)} reported Theorem but {', '.join(csat)} reported CounterSatisfiable"
        elif parse_err and (theorem or csat):
            classification = "parse_accept_mismatch"
            severity = "medium"
            description = f"{', '.join(parse_err)} rejected input while other prover(s) accepted semantically"
        elif parse_err and len(parse_err) != len(results):
            classification = "parse_support_mismatch"
            severity = "low"
            description = f"{', '.join(parse_err)} parse error but others did not"

        if classification:
            print(f"[{idx:4d}/{len(files)}] *** {severity.upper():6s} *** {f.name}")
            print(f"         {status}")
            print(f"         {description}")
            findings.append({
                "file": f.name,
                "path": str(f),
                "metadata": meta,
                "classification": classification,
                "severity": severity,
                "description": description,
                "answers": answers,
                "details": {pn: asdict(r) for pn, r in results.items()},
            })
        elif idx % 10 == 0 or idx == len(files):
            print(f"[{idx:4d}/{len(files)}] {status}")

    summary = {}
    for k in ["crash_candidate", "soundness_candidate", "parse_accept_mismatch", "parse_support_mismatch"]:
        summary[k] = sum(1 for x in findings if x["classification"] == k)

    report = {
        "total_files": len(files),
        "tested_provers": list(provers.keys()),
        "summary": summary,
        "findings": findings,
    }

    report_path = output_dir / "sledgehammer_fuzz_report_v2.json"
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")

    print()
    print("=" * 60)
    print("SLEDGEHAMMER TPTP FUZZING REPORT V2")
    print("=" * 60)
    print(f"Files: {len(files)}")
    print(f"Provers: {', '.join(provers.keys())}")
    for key, value in summary.items():
        print(f"{key + ':':28s} {value}")
    print(f"Report: {report_path}")
    print("=" * 60)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Sledgehammer TPTP fuzzer v2")
    sub = parser.add_subparsers(dest="cmd")

    p = sub.add_parser("generate", help="Generate one-lemma theories")
    p.add_argument("--output-dir", required=True)
    p.add_argument("--prover", default="zipperposition")

    p = sub.add_parser("collect", help="Build one theory at a time and collect overlord .p files")
    p.add_argument("--session-dir", required=True)
    p.add_argument("--build-timeout", type=int, default=180)

    p = sub.add_parser("test", help="Differentially test collected .p files")
    p.add_argument("--input-dir", required=True)
    p.add_argument("--output-dir", default=str(Path.home() / "fyp-isabelle-fuzz" / "sledgehammer_results_v2"))
    p.add_argument("--zp", default=None)
    p.add_argument("--e", default=None)
    p.add_argument("--vampire", default=None)
    p.add_argument("--timeout", type=int, default=30)

    args = parser.parse_args()

    if args.cmd == "generate":
        cmd_generate(args)
    elif args.cmd == "collect":
        cmd_collect(args)
    elif args.cmd == "test":
        cmd_test(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()