#!/usr/bin/env python3
"""
fuzz_sledgehammer_tptp.py — Source-informed fuzzing of Sledgehammer's TPTP generation.

Key design:
  - ONE lemma per theory file → overlord .p files won't overwrite each other
  - Each theory name encodes the attack surface being tested
  - Automatic .p collection script generated alongside theories
  - Differential testing against Zipperposition, E, Vampire

Attack surfaces (from reading atp_problem.ML):
  1. Symbol escaping: avoid_clash is identity for TPTP (line ~992)
  2. Type encoding: polymorphism, nested parameterised types
  3. Formula structure: let, lambda, case, if-then-else, quantifiers
  4. Special constructs: datatypes, records, recursive functions
  5. Multi-prover: same lemma to different provers

Usage:
    python3 fuzz_sledgehammer_tptp.py generate --output-dir ~/fyp-isabelle-fuzz/sledgehammer_attack
    # Then follow the printed instructions
"""

import argparse
import json
import random
import re
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Optional


def build_lemma_list(prover):
    SH = f"sledgehammer [prover = {prover}, slices = 1, timeout = 30, overlord]"
    lemmas = []

    def add(name, lemma, imports="Main", preamble=""):
        lemmas.append((name, imports, preamble, lemma, SH))

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
    add("dt_color", '"\\<forall>c::color. c = Red \\<or> c = Green \\<or> c = Blue"',
        preamble="datatype color = Red | Green | Blue\n")
    add("dt_tree", '"Leaf \\<noteq> Node Leaf (0::nat) Leaf"',
        preamble="datatype nat_tree = Leaf | Node nat_tree nat nat_tree\n")
    add("dt_param", '"Nil \\<noteq> Cons (0::nat) Nil"',
        preamble="datatype 'a mylist = Nil | Cons 'a \"'a mylist\"\n")
    add("primrec_len", '"mylen [] = (0::nat)"',
        preamble="primrec mylen :: \"'a list \\<Rightarrow> nat\" where\n  \"mylen [] = 0\"\n| \"mylen (x # xs) = Suc (mylen xs)\"\n")
    add("fun_fib", '"fib 0 = (0::nat)"',
        preamble="fun fib :: \"nat \\<Rightarrow> nat\" where\n  \"fib 0 = 0\"\n| \"fib (Suc 0) = 1\"\n| \"fib (Suc (Suc n)) = fib n + fib (Suc n)\"\n")
    add("record_point", '"xcoord (\\<lparr> xcoord = 1, ycoord = 2 \\<rparr>) = (1::nat)"',
        preamble="record point = xcoord :: nat  ycoord :: nat\n")

    return lemmas


def cmd_generate(args):
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    prover = args.prover
    lemmas = build_lemma_list(prover)

    # Multi-prover versions for a subset
    multi = []
    base = [("mp_refl", "Main", "", '"(x::nat) = x"'),
            ("mp_comm", "Main", "", '"(x::nat) + y = y + x"'),
            ("mp_lambda", "Main", "", '"(\\<lambda>x::nat. x) y = (y::nat)"'),
            ("mp_kw_fof", "Main", "", '"(fof::nat) = fof"')]
    for bname, imp, pre, lem in base:
        for p in ["zipperposition", "e", "vampire"]:
            sh = f"sledgehammer [prover = {p}, slices = 1, timeout = 30, overlord]"
            multi.append((f"{bname}_{p}", imp, pre, lem, sh))

    all_lemmas = lemmas + multi
    theories = []

    for name, imports, preamble, lemma_stmt, sh_cmd in all_lemmas:
        thy_name = f"A_{name}"
        sess_dir = out / thy_name
        sess_dir.mkdir(parents=True, exist_ok=True)

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
        (sess_dir / f"{thy_name}.thy").write_text(content, encoding="utf-8")

        root = (
            f"session {thy_name} = HOL +\n"
            f"  theories\n"
            f"    {thy_name}\n"
        )
        (sess_dir / "ROOT").write_text(root, encoding="utf-8")

        theories.append(thy_name)

    # Build script — runs each session independently, continues on failure
    build_script = (
        '#!/bin/bash\n'
        '# Build each session independently. Failures do not block others.\n'
        'PASS=0; FAIL=0; TOTAL=0\n'
        'SESSIONS=(\n'
    )
    for th in theories:
        build_script += f'  "{th}"\n'
    build_script += (
        ')\n\n'
        'mkdir -p collected_p\n'
        'for S in "${SESSIONS[@]}"; do\n'
        '  TOTAL=$((TOTAL + 1))\n'
        '  echo "[${TOTAL}/${#SESSIONS[@]}] Building $S ..."\n'
        '  isabelle build -D "./$S" -v -o timeout=60 "$S"\n'
        '  RC=$?\n'
        '  find ~/.isabelle -type f -name "prob_*.p" 2>/dev/null | while read -r F; do\n'
        '    [ -f "$F" ] || continue\n'
        '    BASE=$(basename "$F")\n'
        '    cp "$F" "./collected_p/${S}__${BASE}" 2>/dev/null || true\n'
        '  done\n'
        '  if [ $RC -eq 0 ]; then\n'
        '    PASS=$((PASS + 1))\n'
        '  else\n'
        '    FAIL=$((FAIL + 1))\n'
        '    echo "  FAILED: $S"\n'
        '  fi\n'
        'done\n\n'
        'echo ""\n'
        'echo "Done: $PASS passed, $FAIL failed, $TOTAL total"\n'
    )
    (out / "build_all.sh").write_text(build_script)
    (out / "build_all.sh").chmod(0o755)

    # Monitor script
    (out / "monitor_p_files.sh").write_text(
        '#!/bin/bash\n'
        'DEST="${1:-./collected_p}"\n'
        'mkdir -p "$DEST"\n'
        'SEEN=""\n'
        'echo "[*] Monitoring ~/.isabelle/prob_*.p ... (Ctrl-C to stop)"\n'
        'while true; do\n'
        '    for src in ~/.isabelle/prob_*.p; do\n'
        '        [ -f "$src" ] || continue\n'
        '        HASH=$(md5 -q "$src" 2>/dev/null || md5sum "$src" | cut -d" " -f1)\n'
        '        KEY="${HASH}_$(basename $src)"\n'
        '        if ! echo "$SEEN" | grep -q "$KEY"; then\n'
        '            cp "$src" "$DEST/$KEY"\n'
        '            echo "  Captured: $KEY"\n'
        '            SEEN="$SEEN $KEY"\n'
        '        fi\n'
        '    done\n'
        '    sleep 0.3\n'
        'done\n'
    )
    (out / "monitor_p_files.sh").chmod(0o755)

    print(f"[*] Generated {len(theories)} theories (1 lemma each) -> {out}")
    n1 = sum(1 for n,_,_,_,_ in all_lemmas if any(n.startswith(p) for p in ['kw_','conn_','role_','dollar_','shadow_','short_','long_']))
    n2 = sum(1 for n,_,_,_,_ in all_lemmas if n.startswith('type_'))
    n3 = sum(1 for n,_,_,_,_ in all_lemmas if any(n.startswith(p) for p in ['deep_','ite_','let_','lambda_','case_','forall_','exists_','nested_','bool_','large_','neg_','div_','mod_','list_','set_']))
    n4 = sum(1 for n,_,_,_,_ in all_lemmas if any(n.startswith(p) for p in ['dt_','primrec_','fun_','record_']))
    n5 = sum(1 for n,_,_,_,_ in all_lemmas if n.startswith('mp_'))
    print(f"    Symbol escaping: {n1}")
    print(f"    Type encoding:   {n2}")
    print(f"    Formula stress:  {n3}")
    print(f"    Constructs:      {n4}")
    print(f"    Multi-prover:    {n5}")
    print()
    print(f"  步骤:")
    print(f"    1. 终端 A: cd {out} && bash monitor_p_files.sh ./collected_p")
    print(f"    2. 终端 B: cd {out} && bash build_all.sh 2>&1 | tee build.log")
    print(f"    3. Build 完成后 Ctrl-C 终端 A")
    print(f"    4. python3 fuzz_sledgehammer_tptp.py test --input-dir {out}/collected_p \\")
    print(f"           --zp ~/zipperposition-test/_build/default/src/main/zipperposition.exe \\")
    print(f"           --e /Applications/Isabelle2025.app/contrib/e-3.1-1/x86_64-darwin/eprover")


@dataclass
class ProverResult:
    solver: str
    exit_code: int
    answer: str
    elapsed_ms: int
    raw_output: str
    error_msg: Optional[str] = None


def run_prover(solver_path, solver_name, filepath, timeout=30):
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
        output = proc.stdout + "\n" + proc.stderr
        answer = "Unknown"
        m = re.search(r'SZS status\s+(\w+)', output)
        if m:
            answer = m.group(1)
        elif proc.returncode < 0:
            answer = "Crash"
        elif "parse error" in output.lower() or "syntax error" in output.lower():
            answer = "ParseError"
        elif re.search(r'Failure\(|exception|Fatal error', output):
            answer = "Crash"
        elif "error" in output.lower():
            answer = "Error"
        error_msg = None
        if answer in ("Crash", "ParseError", "Error"):
            for line in output.splitlines():
                if "error" in line.lower() or "Failure" in line:
                    error_msg = line.strip()[:200]
                    break
        return ProverResult(solver=solver_name, exit_code=proc.returncode,
                           answer=answer, elapsed_ms=elapsed,
                           raw_output=output[:2000], error_msg=error_msg)
    except subprocess.TimeoutExpired:
        elapsed = int((time.monotonic() - start) * 1000)
        return ProverResult(solver=solver_name, exit_code=-1, answer="Timeout",
                           elapsed_ms=elapsed, raw_output="TIMEOUT", error_msg="timeout")


def cmd_test(args):
    input_dir = Path(args.input_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    files = sorted(input_dir.glob("*.p"))
    if not files:
        print(f"[!] No .p files in {input_dir}")
        sys.exit(1)
    provers = {}
    if args.zp: provers["zipperposition"] = args.zp
    if args.e: provers["e"] = args.e
    if args.vampire: provers["vampire"] = args.vampire
    if not provers:
        print("[!] Specify at least one prover (--zp, --e, --vampire)")
        sys.exit(1)
    print(f"[*] Testing {len(files)} .p files against {list(provers.keys())}\n")
    bugs = []
    for idx, f in enumerate(files, 1):
        pr = {}
        for pn, pp in provers.items():
            pr[pn] = run_prover(pp, pn, f, timeout=args.timeout)
        answers = {pn: r.answer for pn, r in pr.items()}
        status = " | ".join(f"{pn}={a}" for pn, a in answers.items())
        bug_type = severity = description = None
        parse_err = [pn for pn, r in pr.items() if r.answer == "ParseError"]
        solvers = [pn for pn, a in answers.items() if a in ("Theorem", "CounterSatisfiable")]
        crashes = [pn for pn, r in pr.items() if r.answer == "Crash"]
        thm = [pn for pn, a in answers.items() if a == "Theorem"]
        csat = [pn for pn, a in answers.items() if a == "CounterSatisfiable"]

        if crashes:
            bug_type, severity = "crash", "critical"
            description = f"{', '.join(crashes)} crashed: {pr[crashes[0]].error_msg}"
        elif thm and csat:
            bug_type, severity = "soundness", "critical"
            description = f"{', '.join(thm)} Theorem vs {', '.join(csat)} CounterSatisfiable"
        elif parse_err and solvers:
            bug_type, severity = "parse_discrepancy", "high"
            description = f"{', '.join(parse_err)} reject but {', '.join(solvers)} accept"
        elif parse_err and not solvers:
            errs = [pn for pn, r in pr.items() if r.answer in ("Error", "ParseError")]
            others = [pn for pn, a in answers.items() if a not in ("Error", "ParseError", "Crash")]
            if errs and others:
                bug_type, severity = "error_discrepancy", "medium"
                description = f"{', '.join(errs)} error but {', '.join(others)} = {[answers[o] for o in others]}"

        if bug_type:
            print(f"  [{idx:4d}/{len(files)}] *** {severity.upper():8s} *** {f.name}")
            print(f"           {status}")
            print(f"           {description}")
            bugs.append({"file": f.name, "path": str(f), "bug_type": bug_type,
                         "severity": severity, "description": description,
                         "answers": answers,
                         "details": {pn: asdict(r) for pn, r in pr.items()}})
        elif idx % 10 == 0:
            print(f"  [{idx:4d}/{len(files)}] {status}")

    report = {"total": len(files), "provers": list(provers.keys()), "bugs": bugs,
              "summary": {bt: len([b for b in bugs if b["bug_type"] == bt])
                          for bt in ["crash", "soundness", "parse_discrepancy", "error_discrepancy"]}}
    rp = output_dir / "sledgehammer_fuzz_report.json"
    rp.write_text(json.dumps(report, indent=2))
    print(f"\n{'='*60}")
    print(f"  SLEDGEHAMMER TPTP FUZZING REPORT")
    print(f"{'='*60}")
    print(f"  Files: {len(files)}  Provers: {', '.join(provers.keys())}")
    for bt, c in report["summary"].items():
        print(f"  {bt.replace('_',' ').title() + ':':22s} {c}")
    print(f"{'='*60}")
    print(f"  Report: {rp}")


def main():
    parser = argparse.ArgumentParser(description="Sledgehammer TPTP fuzzer")
    sub = parser.add_subparsers(dest="cmd")
    p = sub.add_parser("generate")
    p.add_argument("--output-dir", required=True)
    p.add_argument("--prover", default="zipperposition")
    p = sub.add_parser("test")
    p.add_argument("--input-dir", required=True)
    p.add_argument("--output-dir", default=str(Path.home() / "fyp-isabelle-fuzz" / "sledgehammer_results"))
    p.add_argument("--zp", default=None)
    p.add_argument("--e", default=None)
    p.add_argument("--vampire", default=None)
    p.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    if args.cmd == "generate": cmd_generate(args)
    elif args.cmd == "test": cmd_test(args)
    else: parser.print_help()

if __name__ == "__main__":
    main()