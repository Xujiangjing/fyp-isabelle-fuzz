#!/usr/bin/env python3
"""
mutate.py — Mutation strategies for Isabelle-Sledgehammer-ATP fuzzing.

Two levels of mutation:
  1. THY-level:  Mutate the Isabelle .thy source before Sledgehammer export.
  2. TPTP-level: Mutate the exported .p files directly (faster, no Isabelle needed).

Usage:
    # Mutate .thy templates and write new .thy files
    python3 mutate.py thy --output-dir ./mutated_thy --count 50

    # Mutate existing .p files
    python3 mutate.py tptp --input-dir ~/fyp-isabelle-fuzz/unique_inputs \
                           --output-dir ./mutated_p --count 50
"""

import argparse
import random
import re
import string
import sys
from pathlib import Path
from copy import deepcopy


# ── Constants ────────────────────────────────────────────────────────

# TPTP statement-level keywords (known to cause parser clashes)
TPTP_KEYWORDS = ["fof", "tff", "cnf", "thf", "tcf", "include"]

# TPTP role-level keywords (should be safe but worth testing)
TPTP_ROLES = ["type", "axiom", "conjecture", "hypothesis", "definition",
              "lemma", "theorem", "plain", "negated_conjecture"]

# Isabelle types to use in generated lemmas
ISABELLE_TYPES = ["nat", "int", "bool", "real", "char", "string",
                  "nat list", "int list", "nat set", "nat option"]

# Operators and formula patterns at different complexity levels
SIMPLE_PATTERNS = [
    '{v} = ({v}::{t})',
    '{v} + 0 = ({v}::{t})',
    '{v} * 1 = ({v}::{t})',
]

MEDIUM_PATTERNS = [
    '({v}::{t}) < {v} + 1',
    '{v} + {v} = 2 * ({v}::{t})',
    'length [({v}::{t})] = 1',
    'rev [({v}::{t})] = [{v}]',
    'hd [{v}] = ({v}::{t})',
]

COMPLEX_PATTERNS = [
    '({v}::{t}) + {w} = {w} + {v}',
    '({v}::{t}) * ({w} + 1) = {v} * {w} + {v}',
    'min ({v}::{t}) {w} <= max {v} {w}',
    'sorted (sort [({v}::{t}), {w}])',
    'set [({v}::{t}), {w}] = {{v, {w}}}',
]

# Names that stress the boundary between safe and problematic
EDGE_CASE_NAMES = (
    TPTP_KEYWORDS
    + TPTP_ROLES
    + ["type_", "fof_x", "tff1", "cnf_", "True", "False",
       "o", "i", "t", "s", "p", "c",  # very short names
       "a" * 64,                        # very long name
       "x_y_z", "x'", "x1"]            # special chars
)


# ══════════════════════════════════════════════════════════════════════
#  THY-LEVEL MUTATIONS
# ══════════════════════════════════════════════════════════════════════

def random_var_name() -> str:
    """Pick a variable name: sometimes safe, sometimes adversarial."""
    if random.random() < 0.3:
        return random.choice(EDGE_CASE_NAMES)
    return random.choice(list(string.ascii_lowercase)) + str(random.randint(0, 9))


def random_type() -> str:
    """Pick a random Isabelle type."""
    return random.choice(ISABELLE_TYPES)


def generate_mutated_thy(theory_name: str, num_lemmas: int = 10) -> str:
    """Generate a .thy file with randomised variable names, types, and patterns."""
    lines = [
        f"theory {theory_name}",
        "imports Main",
        "begin",
        "",
    ]

    all_patterns = SIMPLE_PATTERNS + MEDIUM_PATTERNS + COMPLEX_PATTERNS

    for i in range(1, num_lemmas + 1):
        v = random_var_name()
        w = random_var_name()
        t = random_type()
        pat = random.choice(all_patterns)

        # Some types only work with certain patterns; fall back to simple if needed
        try:
            formula = pat.format(v=v, w=w, t=t)
        except (KeyError, IndexError):
            formula = f'{v} = ({v}::{t})'

        lines.append(f'lemma mut_{i}: "{formula}"')
        lines.append(f'  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]')
        lines.append("  oops")
        lines.append("")

    lines.append("end")
    return "\n".join(lines)


def mutate_existing_thy(content: str) -> str:
    """Apply random mutations to an existing .thy file."""
    mutations = [
        _mut_thy_swap_varname,
        _mut_thy_swap_type,
        _mut_thy_duplicate_lemma,
        _mut_thy_inject_keyword_var,
        _mut_thy_change_prover_option,
    ]

    # Apply 1-3 random mutations
    for _ in range(random.randint(1, 3)):
        mut = random.choice(mutations)
        content = mut(content)

    return content


def _mut_thy_swap_varname(content: str) -> str:
    """Replace a random variable-like token with something adversarial."""
    tokens = re.findall(r'\b([a-z][a-z0-9_]*)\b', content)
    if not tokens:
        return content
    old = random.choice(tokens)
    new = random_var_name()
    # Replace only the first occurrence to keep things interesting
    return content.replace(old, new, 1)


def _mut_thy_swap_type(content: str) -> str:
    """Replace a type annotation with a different type."""
    types_found = re.findall(r'::\s*(\w+(?:\s+\w+)*)\)', content)
    if not types_found:
        return content
    old = random.choice(types_found)
    new = random_type()
    return content.replace(f'::{old})', f'::{new})', 1)


def _mut_thy_duplicate_lemma(content: str) -> str:
    """Duplicate a random lemma (to increase problem size)."""
    lemmas = re.findall(r'(lemma \w+:.*?oops)', content, re.DOTALL)
    if not lemmas:
        return content
    lemma = random.choice(lemmas)
    dup = lemma.replace("lemma ", f"lemma dup_{random.randint(100,999)}_", 1)
    return content.replace("end", f"{dup}\n\nend", 1)


def _mut_thy_inject_keyword_var(content: str) -> str:
    """Add a new lemma using a TPTP keyword as variable name."""
    kw = random.choice(TPTP_KEYWORDS)
    t = random_type()
    new_lemma = (
        f'lemma kw_inject: "{kw} = ({kw}::{t})"\n'
        f'  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]\n'
        f'  oops\n'
    )
    return content.replace("end", f"{new_lemma}\nend", 1)


def _mut_thy_change_prover_option(content: str) -> str:
    """Tweak sledgehammer options (slices, timeout)."""
    new_slices = random.choice([1, 2, 3])
    new_timeout = random.choice([3, 5, 10, 15])
    content = re.sub(r'slices\s*=\s*\d+', f'slices = {new_slices}', content)
    content = re.sub(r'timeout\s*=\s*\d+', f'timeout = {new_timeout}', content)
    return content


# ══════════════════════════════════════════════════════════════════════
#  TPTP-LEVEL MUTATIONS (directly on .p files, no Isabelle needed)
# ══════════════════════════════════════════════════════════════════════

def mutate_tptp(content: str) -> str:
    """Apply random mutations to a TPTP .p file."""
    mutations = [
        _mut_tptp_swap_symbol_name,
        _mut_tptp_inject_keyword_symbol,
        _mut_tptp_remove_block,
        _mut_tptp_duplicate_block,
        _mut_tptp_change_role,
        _mut_tptp_swap_type,
    ]

    for _ in range(random.randint(1, 3)):
        mut = random.choice(mutations)
        content = mut(content)

    return content


def _split_tptp_blocks(content: str) -> list[str]:
    """Split TPTP content into declaration blocks."""
    blocks = []
    current = []
    for line in content.splitlines(keepends=True):
        current.append(line)
        if line.strip().endswith(")."):
            blocks.append("".join(current))
            current = []
    if current:
        blocks.append("".join(current))
    return blocks


def _mut_tptp_swap_symbol_name(content: str) -> str:
    """Replace a random symbol name with something different."""
    # Match TPTP symbol names like sy_v_foo, sy_c_bar, etc.
    symbols = re.findall(r'\b(sy_[vcft]_\w+)\b', content)
    if not symbols:
        return content
    old = random.choice(symbols)
    suffix = random.choice(EDGE_CASE_NAMES + ["mutated_" + str(random.randint(0, 999))])
    new = f"sy_v_{suffix}"
    return content.replace(old, new)


def _mut_tptp_inject_keyword_symbol(content: str) -> str:
    """Inject a type declaration using a TPTP keyword as the symbol name."""
    kw = random.choice(TPTP_KEYWORDS)
    injection = f"thf(mut_kw_{kw}, type,\n    {kw} : $o).\n\n"
    return injection + content


def _mut_tptp_remove_block(content: str) -> str:
    """Remove a random thf/tff/fof block (ablation-style)."""
    blocks = _split_tptp_blocks(content)
    if len(blocks) <= 2:
        return content
    idx = random.randint(0, len(blocks) - 1)
    blocks.pop(idx)
    return "".join(blocks)


def _mut_tptp_duplicate_block(content: str) -> str:
    """Duplicate a random block with a renamed identifier."""
    blocks = _split_tptp_blocks(content)
    if not blocks:
        return content
    block = random.choice(blocks)
    # Rename the block identifier to avoid duplicate name
    dup = re.sub(
        r'(thf|tff|fof|cnf)\((\w+)',
        lambda m: f'{m.group(1)}(mut_{random.randint(100,9999)}_{m.group(2)}',
        block,
        count=1
    )
    return content + "\n" + dup


def _mut_tptp_change_role(content: str) -> str:
    """Change the role of a random declaration (type→axiom, axiom→conjecture, etc.)."""
    roles = ["type", "axiom", "conjecture", "hypothesis", "definition", "plain"]
    blocks = _split_tptp_blocks(content)
    if not blocks:
        return content
    idx = random.randint(0, len(blocks) - 1)
    new_role = random.choice(roles)
    blocks[idx] = re.sub(
        r'(thf|tff|fof|cnf)\((\w+),\s*(\w+)',
        lambda m: f'{m.group(1)}({m.group(2)}, {new_role}',
        blocks[idx],
        count=1
    )
    return "".join(blocks)


def _mut_tptp_swap_type(content: str) -> str:
    """Replace a TPTP type with another ($o, $i, $int, $rat, $real)."""
    tptp_types = ["$o", "$i", "$int", "$rat", "$real", "$tType"]
    old_types = re.findall(r'(\$\w+)', content)
    if not old_types:
        return content
    old = random.choice(old_types)
    new = random.choice(tptp_types)
    return content.replace(old, new, 1)


# ══════════════════════════════════════════════════════════════════════
#  CLI
# ══════════════════════════════════════════════════════════════════════

def cmd_thy(args):
    """Generate mutated .thy files."""
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    if args.seed_dir:
        # Mutate existing .thy files
        seed_dir = Path(args.seed_dir)
        seeds = list(seed_dir.glob("*.thy"))
        if not seeds:
            print(f"[!] No .thy files in {seed_dir}")
            sys.exit(1)
        for i in range(args.count):
            base = random.choice(seeds)
            content = base.read_text(encoding="utf-8", errors="replace")
            mutated = mutate_existing_thy(content)
            name = f"Mut{i:04d}"
            # Fix theory name to match filename
            mutated = re.sub(r'theory \w+', f'theory {name}', mutated, count=1)
            (out / f"{name}.thy").write_text(mutated, encoding="utf-8")
        print(f"[*] Wrote {args.count} mutated .thy files to {out}")
    else:
        # Generate fresh mutated .thy files
        for i in range(args.count):
            name = f"Mut{i:04d}"
            content = generate_mutated_thy(name, num_lemmas=random.randint(5, 20))
            (out / f"{name}.thy").write_text(content, encoding="utf-8")
        print(f"[*] Wrote {args.count} fresh mutated .thy files to {out}")

    # Write ROOT file
    theories = [f.stem for f in sorted(out.glob("*.thy"))]
    root = ["session MutatedSeeds = HOL +", "  theories"]
    for th in theories:
        root.append(f"    {th}")
    (out / "ROOT").write_text("\n".join(root) + "\n")
    print(f"[*] ROOT file written with {len(theories)} theories")


def cmd_tptp(args):
    """Mutate existing .p files."""
    inp = Path(args.input_dir)
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    seeds = list(inp.glob("*.p"))
    if not seeds:
        print(f"[!] No .p files in {inp}")
        sys.exit(1)

    for i in range(args.count):
        base = random.choice(seeds)
        content = base.read_text(encoding="utf-8", errors="replace")
        mutated = mutate_tptp(content)
        out_name = f"mut_{i:04d}_{base.name}"
        (out / out_name).write_text(mutated, encoding="utf-8")

    print(f"[*] Wrote {args.count} mutated .p files to {out}")


def main():
    parser = argparse.ArgumentParser(
        description="Mutation strategies for Isabelle-Sledgehammer-ATP fuzzing"
    )
    sub = parser.add_subparsers(dest="cmd")

    # THY subcommand
    p_thy = sub.add_parser("thy", help="Generate or mutate .thy files")
    p_thy.add_argument("--output-dir", required=True)
    p_thy.add_argument("--seed-dir", default=None, help="Existing .thy files to mutate (omit for fresh generation)")
    p_thy.add_argument("--count", type=int, default=50)

    # TPTP subcommand
    p_tptp = sub.add_parser("tptp", help="Mutate existing .p files directly")
    p_tptp.add_argument("--input-dir", required=True)
    p_tptp.add_argument("--output-dir", required=True)
    p_tptp.add_argument("--count", type=int, default=50)

    args = parser.parse_args()
    if args.cmd == "thy":
        cmd_thy(args)
    elif args.cmd == "tptp":
        cmd_tptp(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()