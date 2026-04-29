import subprocess
import shutil
from pathlib import Path
from datetime import datetime

BASE = Path.home() / "fyp-isabelle-fuzz"
SESSION_DIR = BASE / "session"
COLLECTED_DIR = BASE / "collected"
MASTER_SEEDS_DIR = BASE / "master_seeds"
RUN_SCRIPT = BASE / "run_and_collect.sh"

SESSION_DIR.mkdir(parents=True, exist_ok=True)
COLLECTED_DIR.mkdir(parents=True, exist_ok=True)
MASTER_SEEDS_DIR.mkdir(parents=True, exist_ok=True)

safe_var_groups = [
    ["x", "y", "z"],
    ["foo", "bar", "u"],
    ["v", "n", "m"],
    ["a", "b", "c"],
    ["p", "q", "r"],
]

keyword_groups = [
    ["fof", "tff", "cnf"],
    ["thf", "tcf", "include"],
    ["fof", "include", "cnf"],
    ["tff", "thf", "tcf"],
]

safe_patterns_sets = [
    [
        '{v} = ({v}::nat)',
        '{v} + 0 = ({v}::nat)',
        '{v} * 1 = ({v}::nat)',
    ],
    [
        '{v} = ({v}::nat)',
        '({v}::nat) < {v} + 1',
        '{v} + 1 = {v} + 1',
    ],
    [
        '{v} = ({v}::nat)',
        '{v} + 0 = {v}',
        '{v} * 1 = {v}',
    ],
]

keyword_patterns = [
    '{v} = ({v}::nat)',
    '{v} + 0 = ({v}::nat)',
    '{v} * 1 = ({v}::nat)',
]

def write_theory(theory_name: str, vars_list: list[str], patterns: list[str], prover: str = "zipperposition"):
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
            lines.append(f'  sledgehammer [prover = {prover}, slices = 1, timeout = 5, overlord]')
            lines.append("  oops")
            lines.append("")

    lines.append("end")
    (SESSION_DIR / f"{theory_name}.thy").write_text("\n".join(lines), encoding="utf-8")


def write_root(theory_names: list[str]):
    root_lines = ["session AutoSeeds = HOL +", "  theories"]
    for th in theory_names:
        root_lines.append(f"    {th}")
    (SESSION_DIR / "ROOT").write_text("\n".join(root_lines) + "\n", encoding="utf-8")


def generate_round(round_id: int):
    # 清掉旧 theory
    for p in SESSION_DIR.glob("*.thy"):
        p.unlink()
    root = SESSION_DIR / "ROOT"
    if root.exists():
        root.unlink()

    safe_vars = safe_var_groups[round_id % len(safe_var_groups)]
    kw_vars = keyword_groups[round_id % len(keyword_groups)]
    safe_patterns = safe_patterns_sets[round_id % len(safe_patterns_sets)]

    write_theory("SafeSeeds", safe_vars, safe_patterns, prover="zipperposition")
    write_theory("KeywordSeeds", kw_vars, keyword_patterns, prover="zipperposition")
    write_root(["SafeSeeds", "KeywordSeeds"])


def latest_run_dir() -> Path | None:
    runs = sorted(COLLECTED_DIR.glob("run_*"))
    return runs[-1] if runs else None


def merge_latest_run_into_master(round_id: int):
    run_dir = latest_run_dir()
    if run_dir is None:
        print(f"[round {round_id}] No run directory found.")
        return 0

    copied = 0
    for f in sorted(run_dir.glob("*.p")):
        new_name = f"round{round_id:03d}_{f.name}"
        shutil.copy2(f, MASTER_SEEDS_DIR / new_name)
        copied += 1
    return copied


def run_shell_script():
    result = subprocess.run(
        [str(RUN_SCRIPT)],
        text=True,
        capture_output=True
    )
    print(result.stdout)
    if result.returncode != 0:
        print(result.stderr)
        raise RuntimeError(f"run_and_collect.sh failed with code {result.returncode}")


def main(rounds: int = 10):
    print(f"[*] Starting driver with {rounds} rounds")
    total = 0

    for i in range(1, rounds + 1):
        print("=" * 70)
        print(f"[*] Round {i}")

        generate_round(i)
        print(f"[*] Generated theories for round {i}")

        run_shell_script()

        copied = merge_latest_run_into_master(i)
        total += copied
        print(f"[*] Round {i}: copied {copied} files into {MASTER_SEEDS_DIR}")

    print("=" * 70)
    print(f"[*] Done. Total copied into master_seeds: {total}")
    print(f"[*] master_seeds dir: {MASTER_SEEDS_DIR}")


if __name__ == "__main__":
    main(rounds=10)