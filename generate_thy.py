from pathlib import Path

session_dir = Path.home() / "fyp-isabelle-fuzz" / "session"
session_dir.mkdir(parents=True, exist_ok=True)

safe_vars = ["x", "y", "z", "foo", "bar", "u", "v", "n", "m"]
keyword_vars = ["fof", "tff", "cnf", "thf", "tcf", "include"]

safe_patterns = [
    '{v} = ({v}::nat)',
    '{v} + 0 = ({v}::nat)',
    '{v} * 1 = ({v}::nat)',
    '({v}::nat) <= {v}',
    '({v}::nat) < {v} + 1',
]

keyword_patterns = [
    '{v} = ({v}::nat)',
    '{v} + 0 = ({v}::nat)',
    '{v} * 1 = ({v}::nat)',
]

theories = []

def write_theory(theory_name, vars_list, patterns):
    theories.append(theory_name)
    lines = [
        f"theory {theory_name}",
        "imports Main",
        "begin",
        ""
    ]
    lemma_id = 0
    for v in vars_list:
        for pat in patterns:
            lemma_id += 1
            formula = pat.format(v=v)
            lines.append(f'lemma seed_{lemma_id}: "{formula}"')
            lines.append('  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]')
            lines.append("  oops")
            lines.append("")
    lines.append("end")
    (session_dir / f"{theory_name}.thy").write_text("\n".join(lines), encoding="utf-8")

write_theory("SafeSeeds", safe_vars, safe_patterns)
write_theory("KeywordSeeds", keyword_vars, keyword_patterns)

root_lines = ["session AutoSeeds = HOL +", "  theories"]
for th in theories:
    root_lines.append(f"    {th}")
(session_dir / "ROOT").write_text("\n".join(root_lines) + "\n", encoding="utf-8")

print("Generated:", ", ".join(theories))