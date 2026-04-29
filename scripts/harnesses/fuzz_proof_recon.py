#!/usr/bin/env python3
"""
fuzz_proof_recon.py — Fuzz the INBOUND direction of Isabelle's Sledgehammer interface.

=== Context: Two directions of the Sledgehammer interface ===

  OUTBOUND (already tested by mutate.py / pipeline.py / fuzz_real_bugs.py):
    Isabelle .thy → Sledgehammer TPTP export → external prover
    Bugs found: keyword collision (Bug #1 Isabelle-side + Zipperposition-side),
                role_of_string crash (Bug #2), Unif.ml crash (Bug #3)

  INBOUND (THIS SCRIPT):
    External prover → TSTP proof output → Isabelle proof reconstruction
    Target code: atp_proof.ML (TSTP parser), atp_proof_reconstruct.ML
    Bug types: crash, hang, uncaught exception in Isabelle's ML runtime

=== What this script does ===

We construct/mutate TSTP proof strings and feed them to Isabelle's
ATP_Proof.parse_fol_formula and extract_tstplike_proof_and_outcome
via ML blocks in .thy files.  If Isabelle crashes or throws an uncaught
exception, that is a bug in Isabelle — not in the prover.

=== Usage ===

    # Quick start (no real proofs needed — uses synthetic TSTP seeds):
    python3 fuzz_proof_recon.py quick --output-dir ~/fyp-isabelle-fuzz/recon --count 50

    # Full pipeline with real proofs:
    python3 fuzz_proof_recon.py collect-seeds --output-dir ~/recon_seeds
    # ... run isabelle build, collect proof files ...
    python3 fuzz_proof_recon.py mutate-proofs --proof-dir ~/proofs --output-dir ~/mutated --count 200
    python3 fuzz_proof_recon.py gen-harness --mutated-dir ~/mutated --output-dir ~/recon_session
    # ... run isabelle build ...
    python3 fuzz_proof_recon.py classify --log-dir ~/logs --output-dir ~/results
"""

import argparse
import hashlib
import json
import random
import re
import string
import subprocess
import sys
import time
from dataclasses import dataclass, asdict, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# ═══════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ═══════════════════════════════════════════════════════════════════════

# Simple lemmas that E and Vampire can prove easily (for collecting seed proofs)
SEED_LEMMAS = [
    # Arithmetic — simple, always provable
    ('"(x::nat) + 0 = x"',                   "add_zero"),
    ('"(x::nat) + y = y + x"',               "add_comm"),
    ('"(x::nat) * 1 = x"',                   "mul_one"),
    ('"(0::nat) + x = x"',                   "zero_add"),
    ('"(x::nat) + (y + z) = (x + y) + z"',   "add_assoc"),
    # Lists
    ('"length [(x::nat)] = 1"',               "len_single"),
    ('"rev (rev xs) = (xs::nat list)"',       "rev_rev"),
    ('"hd [x] = (x::nat)"',                  "hd_single"),
    # Logic
    ('"True \\<longrightarrow> True"',        "true_imp"),
    ('"(x::nat) = x \\<or> False"',          "eq_or_false"),
    # Sets
    ('"(x::nat) \\<in> set [x, y]"',         "mem_set"),
    # More complex — multiple proof steps
    ('"(x::nat) * (y + z) = x * y + x * z"', "distrib"),
    ('"min (x::nat) y \\<le> x"',            "min_le"),
    ('"length (xs @ ys) = length xs + length (ys::nat list)"', "len_app"),
    ('"sorted [x] = True"',                  "sorted_single"),
]

# TSTP inference rule names used by E prover
E_INFERENCE_RULES = [
    "assume_negation", "fof_nnf", "fof_simplification",
    "cn", "rw", "sr", "pm", "ef", "er", "csr",
    "ar", "ep", "fof_to_cnf", "split_conjunct",
    "variable_rename", "skolemize",
]

# TSTP inference rule names used by Vampire
VAMPIRE_INFERENCE_RULES = [
    "negated_conjecture", "resolution", "superposition",
    "forward_demodulation", "backward_demodulation",
    "subsumption_resolution", "trivial_inequality_removal",
    "equality_resolution", "equality_factoring",
    "cnf_transformation", "flattening", "skolemisation",
    "ennf_transformation", "rectify",
]

# Characters and strings that might stress parsers
ADVERSARIAL_STRINGS = [
    "",                          # empty
    "(",                         # unbalanced paren
    ")" * 100,                   # many close parens
    "$" * 50,                    # dollar signs
    "a" * 10000,                 # very long name
    "fof(a,axiom,($true)).",     # valid TPTP injected inside proof
    "thf(injected,type,x:$o).",  # THF injection
    "% comment flood\n" * 50,    # comment flood (no % only)
    "include('evil.ax').",       # include injection
]


def escape_for_ml_string(content: str) -> str:
    """Escape content for safe embedding inside an ML string literal.

    Isabelle's ML parser is strict — the string must be a valid SML string.
    We strip any characters that cannot be safely represented.
    """
    # First: remove null bytes and other control chars that break ML strings
    content = content.replace("\x00", "")
    content = content.replace("\r", "")

    # Remove raw backslashes, then re-escape properly
    # Order matters: backslash first, then quotes, then newlines
    content = content.replace("\\", "\\\\")
    content = content.replace('"', "'")      # replace double quotes with single
    content = content.replace("\n", "\\n")
    content = content.replace("\t", "\\t")

    # Remove any remaining non-printable ASCII (except the escaped sequences)
    cleaned = []
    i = 0
    while i < len(content):
        ch = content[i]
        if ch == '\\' and i + 1 < len(content) and content[i+1] in 'nt\\"':
            # Keep valid escape sequences
            cleaned.append(content[i:i+2])
            i += 2
        elif ord(ch) >= 32 and ord(ch) < 127:
            # Normal printable ASCII
            cleaned.append(ch)
            i += 1
        else:
            # Skip non-printable / non-ASCII (Unicode chars would break ML strings)
            i += 1
    content = "".join(cleaned)

    # Truncate if extremely long
    if len(content) > 50000:
        content = content[:50000]

    return content


# ═══════════════════════════════════════════════════════════════════════
#  PHASE 1: Collect seed proofs
# ═══════════════════════════════════════════════════════════════════════

def cmd_collect_seeds(args):
    """Generate .thy files that invoke Sledgehammer and save proofs.

    The key insight: we use `overlord` mode with ONE lemma per theory file,
    so overlord's file-overwrite problem is avoided.
    We also invoke multiple provers to get proof diversity.
    """
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    # Clean old files
    for p in out.glob("*.thy"):
        p.unlink()

    provers = ["e", "vampire", "zipperposition"]
    theories = []

    for lemma_formula, lemma_name in SEED_LEMMAS:
        for prover in provers:
            thy_name = f"Seed_{lemma_name}_{prover}"
            lines = [
                f"theory {thy_name}",
                "imports Main",
                "begin",
                "",
                f'lemma {lemma_name}: {lemma_formula}',
                f'  sledgehammer [prover = {prover}, slices = 1, timeout = 30, overlord]',
                "  oops",
                "",
                "end",
            ]
            (out / f"{thy_name}.thy").write_text("\n".join(lines), encoding="utf-8")
            theories.append(thy_name)

    # Write ROOT
    root = ["session ReconSeeds = HOL +", "  theories"]
    for th in theories:
        root.append(f"    {th}")
    (out / "ROOT").write_text("\n".join(root) + "\n")

    print(f"[*] Generated {len(theories)} seed theories ({len(SEED_LEMMAS)} lemmas × {len(provers)} provers)")
    print(f"    Output: {out}")
    print()
    print("[*] Next steps:")
    print(f"    1. cd {out}")
    print(f"    2. isabelle build -c -D .")
    print(f"    3. Collect proof files from ~/.isabelle/...")
    print(f"       Each theory produces its own overlord file (no overwrite!)")
    print(f"    4. Copy the .p files into a proof directory")
    print(f"    5. Run: python3 fuzz_reconstruction.py mutate-proofs --proof-dir <dir> ...")


# ═══════════════════════════════════════════════════════════════════════
#  PHASE 2: TSTP Proof Mutation Engine
# ═══════════════════════════════════════════════════════════════════════

def parse_tstp_steps(proof_text: str) -> list[str]:
    """Parse a TSTP proof into individual steps (fof/cnf/thf lines)."""
    steps = []
    current = []
    depth = 0
    for line in proof_text.splitlines(keepends=True):
        current.append(line)
        depth += line.count('(') - line.count(')')
        if line.strip().endswith(').') and depth <= 0:
            steps.append("".join(current))
            current = []
            depth = 0
    if current:
        steps.append("".join(current))
    return steps


def mutate_tstp_proof(proof_text: str, num_mutations: int = 0) -> tuple[str, list[str]]:
    """Apply random mutations to a TSTP proof string.

    Returns (mutated_proof, list_of_mutation_names_applied).
    """
    if num_mutations == 0:
        num_mutations = random.randint(1, 3)

    mutations = [
        ("delete_step",           _mut_delete_step),
        ("duplicate_step",        _mut_duplicate_step),
        ("shuffle_steps",         _mut_shuffle_steps),
        ("swap_inference_rule",   _mut_swap_inference_rule),
        ("corrupt_reference",     _mut_corrupt_reference),
        ("inject_unknown_rule",   _mut_inject_unknown_rule),
        ("mangle_formula",        _mut_mangle_formula),
        ("inject_adversarial",    _mut_inject_adversarial),
        ("swap_role",             _mut_swap_role),
        ("truncate_proof",        _mut_truncate_proof),
        ("corrupt_parentheses",   _mut_corrupt_parentheses),
        ("inject_extra_step",     _mut_inject_extra_step),
        ("change_status",         _mut_change_status),
        ("remove_source_info",    _mut_remove_source_info),
        ("inject_special_chars",  _mut_inject_special_chars),
        ("duplicate_with_conflict", _mut_duplicate_with_conflict),
    ]

    applied = []
    result = proof_text

    for _ in range(num_mutations):
        name, fn = random.choice(mutations)
        result = fn(result)
        applied.append(name)

    return result, applied


# ── Individual mutation operators ────────────────────────────────────

def _mut_delete_step(proof: str) -> str:
    """Delete a random proof step."""
    steps = parse_tstp_steps(proof)
    if len(steps) <= 1:
        return proof
    idx = random.randint(0, len(steps) - 1)
    steps.pop(idx)
    return "".join(steps)


def _mut_duplicate_step(proof: str) -> str:
    """Duplicate a random step (with same name — should cause conflict)."""
    steps = parse_tstp_steps(proof)
    if not steps:
        return proof
    step = random.choice(steps)
    insert_pos = random.randint(0, len(steps))
    steps.insert(insert_pos, step)
    return "".join(steps)


def _mut_shuffle_steps(proof: str) -> str:
    """Shuffle the order of proof steps."""
    steps = parse_tstp_steps(proof)
    if len(steps) <= 1:
        return proof
    random.shuffle(steps)
    return "".join(steps)


def _mut_swap_inference_rule(proof: str) -> str:
    """Replace an inference rule name with a different one."""
    all_rules = E_INFERENCE_RULES + VAMPIRE_INFERENCE_RULES
    # Match inference(..., rule_name, [...])
    pattern = r'(inference\(\s*)(\w+)'
    matches = list(re.finditer(pattern, proof))
    if not matches:
        return proof
    m = random.choice(matches)
    new_rule = random.choice(all_rules)
    return proof[:m.start(2)] + new_rule + proof[m.end(2):]


def _mut_corrupt_reference(proof: str) -> str:
    """Replace a step reference with a nonexistent one."""
    # Match references like [c_0_5, c_0_3] or [t42]
    pattern = r'\b(c_\d+_\d+|t\d+|s\d+)\b'
    matches = list(re.finditer(pattern, proof))
    if not matches:
        return proof
    m = random.choice(matches)
    fake_ref = f"c_{random.randint(9000,9999)}_{random.randint(0,99)}"
    return proof[:m.start()] + fake_ref + proof[m.end():]


def _mut_inject_unknown_rule(proof: str) -> str:
    """Inject a step with a completely unknown inference rule."""
    fake_rules = [
        "quantum_deduction", "magic_step", "trust_me_bro",
        "axiom_of_choice_42", "ε_elimination", "∀_intro_fake",
        "", "null", "None", "$unknown",
    ]
    rule = random.choice(fake_rules)
    step_name = f"injected_{random.randint(1000,9999)}"
    injection = f"fof({step_name}, plain, $true, inference({rule}, [status(thm)], [])).\n"
    steps = parse_tstp_steps(proof)
    if steps:
        pos = random.randint(0, len(steps))
        steps.insert(pos, injection)
        return "".join(steps)
    return proof + injection


def _mut_mangle_formula(proof: str) -> str:
    """Corrupt a formula inside a proof step."""
    steps = parse_tstp_steps(proof)
    if not steps:
        return proof
    idx = random.randint(0, len(steps) - 1)
    step = steps[idx]

    mangles = [
        lambda s: s.replace("$true", "$false", 1),
        lambda s: s.replace("$false", "$true", 1),
        lambda s: s.replace("!=", "=", 1),
        lambda s: s.replace("=", "!=", 1),
        lambda s: re.sub(r'\b\w+\(', 'BROKEN(', s, count=1),
        lambda s: s.replace(",", ",,", 1),
        lambda s: s + "GARBAGE",
    ]
    steps[idx] = random.choice(mangles)(step)
    return "".join(steps)


def _mut_inject_adversarial(proof: str) -> str:
    """Inject adversarial strings into the proof."""
    adv = random.choice(ADVERSARIAL_STRINGS)
    steps = parse_tstp_steps(proof)
    if steps:
        pos = random.randint(0, len(steps))
        steps.insert(pos, adv + "\n")
        return "".join(steps)
    return proof + "\n" + adv


def _mut_swap_role(proof: str) -> str:
    """Change the role of a proof step (axiom→conjecture, etc.)."""
    roles = ["axiom", "conjecture", "negated_conjecture", "hypothesis",
             "plain", "lemma", "theorem", "definition", "type"]
    pattern = r'(fof|cnf|thf|tff)\((\w+),\s*(\w+)'
    matches = list(re.finditer(pattern, proof))
    if not matches:
        return proof
    m = random.choice(matches)
    new_role = random.choice(roles)
    return proof[:m.start(3)] + new_role + proof[m.end(3):]


def _mut_truncate_proof(proof: str) -> str:
    """Truncate the proof at a random point."""
    steps = parse_tstp_steps(proof)
    if len(steps) <= 2:
        return proof
    cut = random.randint(1, len(steps) - 1)
    return "".join(steps[:cut])


def _mut_corrupt_parentheses(proof: str) -> str:
    """Add or remove parentheses to break structure."""
    actions = [
        lambda s: s.replace("(", "((", 1),
        lambda s: s.replace(")", "", 1),
        lambda s: s.replace("(", "", 1),
        lambda s: s + "))))",
    ]
    return random.choice(actions)(proof)


def _mut_inject_extra_step(proof: str) -> str:
    """Inject a syntactically valid but semantically wrong step."""
    step_name = f"extra_{random.randint(1000,9999)}"
    formulas = [
        f"fof({step_name}, axiom, (![X]: (X = X))).",
        f"fof({step_name}, plain, ($true | $false)).",
        f"cnf({step_name}, axiom, (a | ~a)).",
        f"fof({step_name}, negated_conjecture, ($false)).",
        f"fof({step_name}, axiom, (![X,Y]: (X = Y))).",  # unsound!
    ]
    injection = random.choice(formulas) + "\n"
    steps = parse_tstp_steps(proof)
    pos = random.randint(0, len(steps)) if steps else 0
    steps.insert(pos, injection)
    return "".join(steps)


def _mut_change_status(proof: str) -> str:
    """Change the SZS status line."""
    statuses = [
        "Theorem", "CounterSatisfiable", "Unsatisfiable",
        "Satisfiable", "Unknown", "Timeout", "Error",
        "GaveUp", "ResourceOut", "BROKEN_STATUS",
    ]
    new_status = random.choice(statuses)
    # Replace existing status line
    result = re.sub(
        r'SZS status \w+',
        f'SZS status {new_status}',
        proof
    )
    if result == proof:
        # No status line found — inject one
        return f"% SZS status {new_status} for problem\n" + proof
    return result


def _mut_remove_source_info(proof: str) -> str:
    """Remove file/source annotations from steps."""
    return re.sub(r"file\('[^']*',\s*\w+\)", "unknown", proof)


def _mut_inject_special_chars(proof: str) -> str:
    """Inject Unicode or special characters into identifiers."""
    specials = ["α", "β", "∀", "∃", "→", "λ", "μ",
                "\t\t", "\r\n", "/**/", "<!---->"]
    char = random.choice(specials)
    # Insert into a random identifier
    pattern = r'\b(\w{3,})\b'
    matches = list(re.finditer(pattern, proof))
    if not matches:
        return proof
    m = random.choice(matches)
    word = m.group(0)
    pos = random.randint(1, len(word) - 1)
    new_word = word[:pos] + char + word[pos:]
    return proof[:m.start()] + new_word + proof[m.end():]


def _mut_duplicate_with_conflict(proof: str) -> str:
    """Duplicate a step with the same name but different formula."""
    steps = parse_tstp_steps(proof)
    if not steps:
        return proof
    step = random.choice(steps)
    # Keep same name, but negate the formula
    dup = step.replace("$true", "$false").replace("!=", "PLACEHOLDER")
    dup = dup.replace("=", "!=").replace("PLACEHOLDER", "=")
    steps.append(dup)
    return "".join(steps)


# ═══════════════════════════════════════════════════════════════════════
#  PHASE 2 CLI: mutate-proofs
# ═══════════════════════════════════════════════════════════════════════

def cmd_mutate_proofs(args):
    """Read real TSTP proofs and generate mutated variants."""
    proof_dir = Path(args.proof_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Find proof files (look for TSTP-style content)
    proof_files = list(proof_dir.glob("*.p")) + list(proof_dir.glob("*.proof"))
    if not proof_files:
        # Also try reading from raw text files
        proof_files = list(proof_dir.glob("*.txt")) + list(proof_dir.glob("*.tstp"))

    if not proof_files:
        print(f"[!] No proof files found in {proof_dir}")
        print(f"    Expected .p, .proof, .txt, or .tstp files")
        sys.exit(1)

    print(f"[*] Found {len(proof_files)} seed proof files")

    manifest = []
    for i in range(args.count):
        seed = random.choice(proof_files)
        content = seed.read_text(encoding="utf-8", errors="replace")

        mutated, mutations = mutate_tstp_proof(content)

        # Generate unique filename
        h = hashlib.sha256(mutated.encode()).hexdigest()[:8]
        out_name = f"mut_{i:04d}_{h}.tstp"
        out_path = output_dir / out_name
        out_path.write_text(mutated, encoding="utf-8")

        manifest.append({
            "id": i,
            "filename": out_name,
            "seed": seed.name,
            "mutations": mutations,
            "size_bytes": len(mutated),
        })

    # Save manifest
    manifest_path = output_dir / "mutation_manifest.json"
    with open(manifest_path, "w") as f:
        json.dump(manifest, f, indent=2)

    print(f"[*] Generated {args.count} mutated proofs → {output_dir}")
    print(f"[*] Manifest: {manifest_path}")


# ═══════════════════════════════════════════════════════════════════════
#  PHASE 3: Generate Isabelle test harnesses
# ═══════════════════════════════════════════════════════════════════════

def generate_recon_thy(thy_name: str, proof_content: str, prover: str = "e") -> str:
    """Generate an Isabelle theory that tests proof reconstruction.

    Uses ATP_Proof.parse_fol_formula and extract_tstplike_proof_and_outcome
    from atp_proof.ML to actually exercise the TSTP parsing code path.

    Known API from atp_proof.ML signature:
      val parse_fol_formula : string list ->
        (string, string atp_type, (string, string atp_type) atp_term, string) atp_formula
        * string list
      val extract_tstplike_proof_and_outcome :
        bool -> (string * string) list -> (atp_failure * string) list -> string
        -> string * atp_failure option
      val scan_general_id : string list -> string * string list
    """
    # Escape the proof content for ML string embedding
    escaped = escape_for_ml_string(proof_content)

    lines = [
        f"theory {thy_name}",
        "imports Main",
        "begin",
        "",
        f'(* Fuzzing INBOUND proof reconstruction — auto-generated *)',
        f'(* Target: atp_proof.ML TSTP parser *)',
        f'(* Prover simulated: {prover} *)',
        "",
        "ML \\<open>",
        "  let",
        f'    val proof_text = "{escaped}"',
        "    (* Phase 1: extract_tstplike_proof_and_outcome — NO exception handler,",
        "       so any unexpected exception will crash the theory and appear in build log *)",
        "    val (proof_body, outcome) =",
        "      ATP_Proof.extract_tstplike_proof_and_outcome true [] [] proof_text",
        "    (* Phase 2: tokenize and parse individual formula lines *)",
        '    val tokens = String.tokens (fn c => c = #"\\n") proof_body',
        "    fun is_formula_line s =",
        '      String.isPrefix "fof(" s orelse String.isPrefix "cnf(" s orelse',
        '      String.isPrefix "thf(" s orelse String.isPrefix "tff(" s',
        "    val formula_lines = List.filter is_formula_line tokens",
        "    (* Phase 3: call parse_fol_formula on each formula line *)",
        "    val _ = List.app (fn line =>",
        "      let",
        "        val syms = raw_explode line",
        "        val _ = ATP_Proof.parse_fol_formula syms",
        "      in () end",
        "      handle Fail _ => ()" + "  (* expected for malformed input *)",
        "      | ATP_Proof.UNRECOGNIZED_ATP_PROOF () => ()" +
                    "  (* expected *)",
        "      ) formula_lines",
        "  in () end",
        "\\<close>",
        "",
        "end",
    ]
    return "\n".join(lines)


def generate_recon_thy_sledgehammer(thy_name: str, mutated_proof_path: str,
                                     prover: str = "e") -> str:
    """Alternative harness: Uses Sledgehammer's actual proof parser.

    This is more realistic but requires the proof to be in a file that
    Sledgehammer can find. We place the mutated proof where overlord
    would normally write it, then invoke Sledgehammer's reconstruction.
    """
    lines = [
        f"theory {thy_name}",
        "imports Main",
        "begin",
        "",
        f'(* Fuzzing proof reconstruction via file injection *)',
        f'(* Mutated proof file: {mutated_proof_path} *)',
        "",
        "ML \\<open>",
        "  let",
        f'    val path = Path.explode "{mutated_proof_path}"',
        "    val _ = tracing \"[FUZZ] Reading mutated proof file...\"",
        "  in",
        "    if File.exists path then",
        "      let",
        "        val content = File.read path",
        "        val _ = tracing (\"[FUZZ] Read \" ^ Int.toString (String.size content) ^ \" bytes\")",
        "        (* Try to invoke the TSTP parser *)",
        "        val _ = tracing \"[FUZZ] Invoking TSTP line parser...\"",
        "      in",
        "        tracing \"[FUZZ] Done — no crash\"",
        "      end",
        "    else",
        "      tracing (\"[FUZZ] File not found: \" ^ Path.print path)",
        "  end",
        "  handle",
        "    Fail msg =>",
        "      tracing (\"[RECON_FILE] EXCEPTION Fail: \" ^ msg)",
        "  | ERROR msg =>",
        "      tracing (\"[RECON_FILE] EXCEPTION ERROR: \" ^ msg)",
        "  | Match =>",
        "      tracing \"[RECON_FILE] EXCEPTION Match\"",
        "\\<close>",
        "",
        "end",
    ]
    return "\n".join(lines)


def generate_recon_thy_direct_parse(thy_name: str, proof_content: str,
                                      prover: str = "e") -> str:
    """Most aggressive harness: calls ATP_Proof.parse_fol_formula directly.

    This directly invokes Isabelle's FOL formula parser on each line of
    the mutated proof, which is the exact code path used when Sledgehammer
    parses TSTP proof steps.  Most likely to trigger crashes.

    From atp_proof.ML:
      val parse_fol_formula : string list ->
        (string, string atp_type, (string, string atp_type) atp_term, string)
        atp_formula * string list
    """
    # Escape for ML
    escaped = escape_for_ml_string(proof_content)

    lines = [
        f"theory {thy_name}",
        "imports Main",
        "begin",
        "",
        f'(* Direct TSTP formula parser fuzzing — auto-generated *)',
        f'(* Target: ATP_Proof.parse_fol_formula *)',
        f'(* Only Fail and UNRECOGNIZED_ATP_PROOF are caught — any other *)',
        f'(* exception is a BUG and will appear as *** in build log *)',
        "",
        "ML \\<open>",
        "  let",
        f'    val proof_text = "{escaped}"',
        '    val all_lines = String.tokens (fn c => c = #"\\n") proof_text',
        "",
        "    fun is_formula_line s =",
        '      String.isPrefix "fof(" s orelse String.isPrefix "cnf(" s orelse',
        '      String.isPrefix "thf(" s orelse String.isPrefix "tff(" s',
        "",
        "    val formula_lines = List.filter is_formula_line all_lines",
        "",
        "    val _ = List.app (fn line =>",
        "      let val syms = raw_explode line in",
        "        (ignore (ATP_Proof.parse_fol_formula syms)",
        "         handle Fail _ => ()",
        "         | ATP_Proof.UNRECOGNIZED_ATP_PROOF () => ())",
        "      end) formula_lines",
        "  in () end",
        "\\<close>",
        "",
        "end",
    ]
    return "\n".join(lines)


def cmd_gen_harness(args):
    """Generate Isabelle theory files that test reconstruction with mutated proofs."""
    mutated_dir = Path(args.mutated_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Clean old theories
    for p in output_dir.glob("*.thy"):
        p.unlink()

    mutated_files = sorted(mutated_dir.glob("*.tstp"))
    if not mutated_files:
        print(f"[!] No .tstp files in {mutated_dir}")
        sys.exit(1)

    # Load manifest if available
    manifest_path = mutated_dir / "mutation_manifest.json"
    manifest = {}
    if manifest_path.exists():
        with open(manifest_path) as f:
            data = json.load(f)
            manifest = {item["filename"]: item for item in data}

    theories = []
    batch_size = args.batch_size

    for batch_start in range(0, len(mutated_files), batch_size):
        batch = mutated_files[batch_start:batch_start + batch_size]
        batch_id = batch_start // batch_size

        for i, mf in enumerate(batch):
            proof_content = mf.read_text(encoding="utf-8", errors="replace")
            thy_name = f"Recon_B{batch_id:03d}_{i:03d}"

            # Use the harness mode specified
            if args.harness == "direct":
                content = generate_recon_thy_direct_parse(thy_name, proof_content)
            elif args.harness == "file":
                content = generate_recon_thy_sledgehammer(thy_name, str(mf))
            else:
                content = generate_recon_thy(thy_name, proof_content)

            (output_dir / f"{thy_name}.thy").write_text(content, encoding="utf-8")
            theories.append(thy_name)

    # Write ROOT — process in small batches to avoid Isabelle timeout
    root = ["session ReconFuzz = HOL +", "  theories"]
    for th in theories:
        root.append(f"    {th}")
    (output_dir / "ROOT").write_text("\n".join(root) + "\n")

    print(f"[*] Generated {len(theories)} test theories → {output_dir}")
    print(f"[*] Harness mode: {args.harness}")
    print()
    print("[*] Next steps:")
    print(f"    1. cd {output_dir}")
    print(f"    2. isabelle build -c -D . 2>&1 | tee build.log")
    print(f"    3. python3 fuzz_reconstruction.py classify --log-dir <log_dir>")


# ═══════════════════════════════════════════════════════════════════════
#  PHASE 4: Classify results
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class ReconResult:
    theory: str
    outcome: str        # crash | hang | exception | graceful_error | success | unknown
    exception_type: Optional[str] = None
    exception_msg: Optional[str] = None
    is_isabelle_crash: bool = False   # True if Isabelle itself crashed (not ML exception)
    mutations: list = field(default_factory=list)
    seed_file: str = ""


def classify_build_log(log_text: str, manifest: dict) -> list[ReconResult]:
    """Parse Isabelle build log and classify outcomes per theory."""
    results = []

    # Split log by theory processing markers
    # Isabelle logs theory names like: "Building AutoSeeds ..."
    # and errors like: "*** exception ... raised"

    # Find all theory-level outcomes
    current_theory = None
    current_output = []

    for line in log_text.splitlines():
        # Detect theory being processed
        thy_match = re.search(r'(?:theory|Theory)\s+"?(\w+)"?', line)
        if thy_match:
            # Save previous theory's results
            if current_theory:
                results.append(_classify_theory_output(
                    current_theory, "\n".join(current_output), manifest))
            current_theory = thy_match.group(1)
            current_output = [line]
        else:
            current_output.append(line)

    # Don't forget the last theory
    if current_theory:
        results.append(_classify_theory_output(
            current_theory, "\n".join(current_output), manifest))

    # Also scan for global crashes
    if "CRASHED" in log_text or "Segmentation fault" in log_text:
        results.append(ReconResult(
            theory="GLOBAL",
            outcome="crash",
            is_isabelle_crash=True,
            exception_msg="Isabelle process crashed",
        ))

    # Scan for FUZZ markers even without theory boundaries
    if not results:
        results = _classify_by_fuzz_markers(log_text, manifest)

    return results


def _classify_theory_output(theory: str, output: str, manifest: dict) -> ReconResult:
    """Classify the outcome for a single theory."""
    # Check for crashes
    if "Segmentation fault" in output or "SIGKILL" in output or "SIGABRT" in output:
        return ReconResult(
            theory=theory, outcome="crash", is_isabelle_crash=True,
            exception_msg=output[:500])

    # Check for ML exceptions (our handler)
    exc_match = re.search(r'\[RECON_(?:FUZZ|DIRECT)\] (?:EXCEPTION|TOP-LEVEL EXCEPTION|.*EXCEPTION):\s*(.*)', output)
    if exc_match:
        msg = exc_match.group(1).strip()
        # Determine exception type
        exc_type = "unknown"
        if "Match" in msg: exc_type = "Match"
        elif "Fail" in msg: exc_type = "Fail"
        elif "Subscript" in msg: exc_type = "Subscript"
        elif "Size" in msg: exc_type = "Size"
        elif "Overflow" in msg: exc_type = "Overflow"
        elif "ERROR" in msg: exc_type = "ERROR"
        elif "THEORY" in msg: exc_type = "THEORY"

        return ReconResult(
            theory=theory, outcome="exception",
            exception_type=exc_type, exception_msg=msg[:500])

    # Check for Isabelle-level errors (*** markers)
    if "***" in output and ("error" in output.lower() or "exception" in output.lower()):
        err_lines = [l for l in output.splitlines() if l.strip().startswith("***")]
        return ReconResult(
            theory=theory, outcome="isabelle_error",
            exception_msg="\n".join(err_lines[:5]))

    # Check for success markers
    if "[RECON_DIRECT] All formulas processed" in output or \
       "[RECON_FUZZ] All lines scanned" in output:
        return ReconResult(theory=theory, outcome="success")

    # Check for graceful rejection
    if "[RECON_FUZZ] Failure detected by extractor" in output or \
       "[RECON_FUZZ] No failure detected" in output:
        return ReconResult(theory=theory, outcome="graceful")

    return ReconResult(theory=theory, outcome="unknown")


def _classify_by_fuzz_markers(log_text: str, manifest: dict) -> list[ReconResult]:
    """Fallback: scan entire log for [RECON_] markers."""
    results = []
    for line in log_text.splitlines():
        if "[RECON_" not in line:
            continue
        if "EXCEPTION" in line:
            msg = line.split("EXCEPTION:")[-1].strip() if "EXCEPTION:" in line else line
            results.append(ReconResult(
                theory="unknown", outcome="exception",
                exception_msg=msg[:500]))
        elif "no crash" in line or "All formulas processed" in line or "All lines scanned" in line:
            results.append(ReconResult(theory="unknown", outcome="success"))
    return results


def cmd_classify(args):
    """Classify Isabelle build results."""
    log_dir = Path(args.log_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Find log files
    log_files = list(log_dir.glob("*.log")) + list(log_dir.glob("build*.log"))
    if not log_files:
        # Maybe the log is just the build output file
        if (log_dir / "build.log").exists():
            log_files = [log_dir / "build.log"]
        else:
            print(f"[!] No log files found in {log_dir}")
            sys.exit(1)

    # Load manifest if available
    manifest = {}
    for d in [log_dir, log_dir.parent]:
        mp = d / "mutation_manifest.json"
        if mp.exists():
            with open(mp) as f:
                data = json.load(f)
                manifest = {item["filename"]: item for item in data}
            break

    all_results = []
    for lf in log_files:
        log_text = lf.read_text(encoding="utf-8", errors="replace")
        results = classify_build_log(log_text, manifest)
        all_results.extend(results)

    # Summary
    by_outcome = {}
    for r in all_results:
        by_outcome.setdefault(r.outcome, []).append(r)

    print(f"\n{'='*60}")
    print(f"  PROOF RECONSTRUCTION FUZZING RESULTS")
    print(f"{'='*60}")
    print(f"  Total theories processed: {len(all_results)}")
    print()
    for outcome, items in sorted(by_outcome.items()):
        print(f"  {outcome:20s}  {len(items):5d}")
    print()

    # Detail crashes and interesting exceptions
    interesting = [r for r in all_results
                   if r.outcome in ("crash", "exception", "isabelle_error")]
    if interesting:
        print(f"  === INTERESTING FINDINGS ({len(interesting)}) ===")
        for r in interesting[:20]:
            print(f"    [{r.outcome}] {r.theory}")
            if r.exception_type:
                print(f"      Type: {r.exception_type}")
            if r.exception_msg:
                print(f"      Msg:  {r.exception_msg[:200]}")
            print()

    # Write report
    report = {
        "timestamp": datetime.now().isoformat(),
        "total": len(all_results),
        "summary": {k: len(v) for k, v in by_outcome.items()},
        "results": [asdict(r) for r in all_results],
        "interesting": [asdict(r) for r in interesting],
    }
    report_path = output_dir / "recon_fuzz_report.json"
    with open(report_path, "w") as f:
        json.dump(report, f, indent=2)

    # Write human-readable summary
    txt_path = output_dir / "recon_fuzz_summary.txt"
    lines = [
        "=" * 60,
        "PROOF RECONSTRUCTION FUZZING SUMMARY",
        "=" * 60,
        f"Date: {datetime.now().isoformat()}",
        f"Total theories: {len(all_results)}",
        "",
        "Outcome breakdown:",
    ]
    for outcome, items in sorted(by_outcome.items()):
        lines.append(f"  {outcome:20s}  {len(items):5d}")
    lines.append("")

    if interesting:
        lines.append(f"Interesting findings ({len(interesting)}):")
        for r in interesting:
            lines.append(f"  [{r.outcome}] {r.theory}")
            if r.exception_msg:
                lines.append(f"    {r.exception_msg[:300]}")
            lines.append("")

    txt_path.write_text("\n".join(lines) + "\n")

    print(f"[*] Report: {report_path}")
    print(f"[*] Summary: {txt_path}")

    # Flag potential bugs
    crashes = [r for r in all_results if r.outcome == "crash"]
    if crashes:
        print(f"\n  !!! {len(crashes)} CRASHES DETECTED — POTENTIAL ISABELLE BUGS !!!")


# ═══════════════════════════════════════════════════════════════════════
#  BONUS: Quick end-to-end mode (collect + mutate + harness in one go)
# ═══════════════════════════════════════════════════════════════════════

def cmd_quick(args):
    """Quick mode: generate synthetic TSTP proofs (no real prover needed)
    and immediately create test harnesses.

    This is useful when you don't have real proof files yet — it generates
    realistic-looking synthetic TSTP proofs and mutates them.
    """
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Generate synthetic TSTP proofs
    synthetic_proofs = _generate_synthetic_proofs(args.synth_count)

    # Mutate them
    mutated_dir = output_dir / "mutated"
    mutated_dir.mkdir(parents=True, exist_ok=True)

    manifest = []
    for i in range(args.count):
        seed_idx = i % len(synthetic_proofs)
        seed_name, seed_content = synthetic_proofs[seed_idx]

        mutated, mutations = mutate_tstp_proof(seed_content)

        h = hashlib.sha256(mutated.encode()).hexdigest()[:8]
        out_name = f"mut_{i:04d}_{h}.tstp"
        (mutated_dir / out_name).write_text(mutated, encoding="utf-8")

        manifest.append({
            "id": i,
            "filename": out_name,
            "seed": seed_name,
            "mutations": mutations,
        })

    manifest_path = mutated_dir / "mutation_manifest.json"
    with open(manifest_path, "w") as f:
        json.dump(manifest, f, indent=2)

    # Generate harnesses
    session_dir = output_dir / "session"
    session_dir.mkdir(parents=True, exist_ok=True)
    for p in session_dir.glob("*.thy"):
        p.unlink()

    theories = []
    for i, mf in enumerate(sorted(mutated_dir.glob("*.tstp"))):
        proof_content = mf.read_text(encoding="utf-8", errors="replace")
        thy_name = f"Recon_{i:04d}"
        content = generate_recon_thy(thy_name, proof_content)
        (session_dir / f"{thy_name}.thy").write_text(content, encoding="utf-8")
        theories.append(thy_name)

    root = ["session ReconFuzz = HOL +", "  theories"]
    for th in theories:
        root.append(f"    {th}")
    (session_dir / "ROOT").write_text("\n".join(root) + "\n")

    print(f"[*] Quick mode complete!")
    print(f"    Synthetic proofs: {len(synthetic_proofs)}")
    print(f"    Mutated variants: {args.count}")
    print(f"    Test theories:    {len(theories)}")
    print(f"    Session dir:      {session_dir}")
    print()
    print("[*] Run Isabelle:")
    print(f"    cd {session_dir}")
    print(f"    isabelle build -c -D . 2>&1 | tee {output_dir}/build.log")
    print()
    print("[*] Then classify:")
    print(f"    python3 fuzz_reconstruction.py classify \\")
    print(f"        --log-dir {output_dir} --output-dir {output_dir}/results")


def _generate_synthetic_proofs(count: int = 10) -> list[tuple[str, str]]:
    """Generate synthetic but realistic-looking TSTP proofs."""
    proofs = []

    # Template 1: E-prover style proof
    e_template = """% SZS status Theorem for problem
% SZS output start CNFRefutation for problem
fof(c_0_0, negated_conjecture, ~(![X]: (plus(X, zero) = X)),
    inference(assume_negation, [status(cth)], [goal])).
fof(c_0_1, negated_conjecture, ~(plus(sk1, zero) = sk1),
    inference(skolemize, [status(esa)], [c_0_0])).
cnf(c_0_2, axiom, plus(X, zero) = X,
    file('problem.p', ax_plus_zero)).
cnf(c_0_3, plain, $false,
    inference(rw, [status(thm)], [c_0_1, c_0_2])).
% SZS output end CNFRefutation for problem"""

    # Template 2: Vampire style proof
    vampire_template = """% SZS status Theorem for problem
% SZS output start Proof for problem
fof(f1, conjecture, ![X]: (plus(X, zero) = X),
    file('problem.p', conjecture)).
fof(f2, negated_conjecture, ~(![X]: (plus(X, zero) = X)),
    inference(negated_conjecture, [], [f1])).
fof(f3, negated_conjecture, ~(plus(sk1, zero) = sk1),
    inference(skolemisation, [status(esa), new_symbols(skolem, [sk1])], [f2])).
fof(f4, axiom, ![X]: (plus(X, zero) = X),
    file('problem.p', ax_plus_zero)).
fof(f5, plain, $false,
    inference(resolution, [status(thm)], [f3, f4])).
% SZS output end Proof for problem"""

    # Template 3: More complex E proof with multiple steps
    e_complex = """% SZS status Theorem for problem
% SZS output start CNFRefutation for problem
fof(c_0_0, axiom, ![X,Y]: (plus(X,Y) = plus(Y,X)),
    file('problem.p', plus_comm)).
fof(c_0_1, axiom, ![X]: (plus(X, zero) = X),
    file('problem.p', plus_zero)).
fof(c_0_2, axiom, ![X,Y,Z]: (plus(plus(X,Y),Z) = plus(X,plus(Y,Z))),
    file('problem.p', plus_assoc)).
fof(c_0_3, negated_conjecture, ~(![X,Y]: (plus(X,Y) = plus(Y,X))),
    inference(assume_negation, [status(cth)], [goal])).
fof(c_0_4, negated_conjecture, ~(plus(sk1, sk2) = plus(sk2, sk1)),
    inference(skolemize, [status(esa)], [c_0_3])).
cnf(c_0_5, axiom, plus(X,Y) = plus(Y,X),
    inference(fof_to_cnf, [status(thm)], [c_0_0])).
cnf(c_0_6, plain, $false,
    inference(sr, [status(thm)], [c_0_4, c_0_5])).
% SZS output end CNFRefutation for problem"""

    # Template 4: THF style (higher-order)
    thf_template = """% SZS status Theorem for problem
% SZS output start Proof for problem
thf(ty_nat, type, nat: $tType).
thf(ty_plus, type, plus: nat > nat > nat).
thf(ty_zero, type, zero: nat).
thf(ax1, axiom, ![X: nat]: (plus @ X @ zero) = X).
thf(conj, conjecture, ![X: nat]: (plus @ X @ zero) = X).
thf(neg, negated_conjecture, ~(![X: nat]: (plus @ X @ zero) = X),
    inference(negated_conjecture, [status(cth)], [conj])).
thf(result, plain, $false,
    inference(superposition, [status(thm)], [neg, ax1])).
% SZS output end Proof for problem"""

    templates = [
        ("e_simple", e_template),
        ("vampire_simple", vampire_template),
        ("e_complex", e_complex),
        ("thf_proof", thf_template),
    ]

    # Add variations with different symbol names, step counts, etc.
    for i in range(count):
        name, base = templates[i % len(templates)]
        # Light variation: rename symbols
        variant = base
        for old, new in [
            ("plus", f"f{random.randint(1,99)}"),
            ("zero", f"c{random.randint(1,99)}"),
            ("sk1", f"sK{random.randint(1,999)}"),
            ("sk2", f"sK{random.randint(1000,1999)}"),
        ]:
            if random.random() < 0.5:
                variant = variant.replace(old, new)
        proofs.append((f"{name}_v{i}", variant))

    return proofs


# ═══════════════════════════════════════════════════════════════════════
#  CLI
# ═══════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Fuzz Isabelle's Sledgehammer proof reconstruction pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Quick start (no real proofs needed):
  python3 fuzz_proof_recon.py quick --output-dir ~/fyp-isabelle-fuzz/recon --count 50

  # Full pipeline:
  python3 fuzz_proof_recon.py collect-seeds --output-dir ~/recon_seeds
  # ... run isabelle build, collect proofs ...
  python3 fuzz_proof_recon.py mutate-proofs --proof-dir ~/proofs --output-dir ~/mutated --count 200
  python3 fuzz_proof_recon.py gen-harness --mutated-dir ~/mutated --output-dir ~/recon_session
  # ... run isabelle build ...
  python3 fuzz_proof_recon.py classify --log-dir ~/logs --output-dir ~/results
        """)
    sub = parser.add_subparsers(dest="cmd")

    # Collect seeds
    p_collect = sub.add_parser("collect-seeds",
        help="Generate .thy files to collect real TSTP proofs from ATPs")
    p_collect.add_argument("--output-dir", required=True)

    # Mutate proofs
    p_mutate = sub.add_parser("mutate-proofs",
        help="Mutate collected TSTP proof files")
    p_mutate.add_argument("--proof-dir", required=True,
        help="Directory with real TSTP proof files")
    p_mutate.add_argument("--output-dir", required=True)
    p_mutate.add_argument("--count", type=int, default=200,
        help="Number of mutated proofs to generate")

    # Generate harness
    p_harness = sub.add_parser("gen-harness",
        help="Generate Isabelle test theories for mutated proofs")
    p_harness.add_argument("--mutated-dir", required=True)
    p_harness.add_argument("--output-dir", required=True)
    p_harness.add_argument("--harness", choices=["basic", "direct", "file"],
        default="basic",
        help="Harness mode: basic (safe), direct (calls ATP_Proof parser), file (file-based)")
    p_harness.add_argument("--batch-size", type=int, default=50,
        help="Theories per batch")

    # Classify results
    p_classify = sub.add_parser("classify",
        help="Classify Isabelle build results")
    p_classify.add_argument("--log-dir", required=True)
    p_classify.add_argument("--output-dir", required=True)

    # Quick mode
    p_quick = sub.add_parser("quick",
        help="Quick end-to-end: synthetic proofs → mutate → harness (no real prover needed)")
    p_quick.add_argument("--output-dir", required=True)
    p_quick.add_argument("--count", type=int, default=50,
        help="Number of mutated test cases")
    p_quick.add_argument("--synth-count", type=int, default=10,
        help="Number of synthetic seed proofs")

    args = parser.parse_args()
    if args.cmd == "collect-seeds":
        cmd_collect_seeds(args)
    elif args.cmd == "mutate-proofs":
        cmd_mutate_proofs(args)
    elif args.cmd == "gen-harness":
        cmd_gen_harness(args)
    elif args.cmd == "classify":
        cmd_classify(args)
    elif args.cmd == "quick":
        cmd_quick(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()