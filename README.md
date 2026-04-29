# fyp-isabelle-fuzz

Reproduction artifact for the Sledgehammer / external automated theorem
prover (ATP) integration test campaign described in **"Validating the
Verifier: Automated Testing for Isabelle/HOL Proof Assistant"** (2026,
Section 3.4 / 4.4) and in the BSc dissertation *"Trust Me, I Am a
Verifier!"* (King's College London, 6CCS3PRJ, 2025/26).

This repository contains the Python harnesses, shell drivers, mutators,
seed generators, and result archives used to identify three
previously-unknown defects on the normal Sledgehammer call path: one in
the outbound TPTP serialiser (`atp_problem.ML`) interacting with
Zipperposition's lexer, one in Zipperposition's higher-order unifier,
and one in E prover's TSTP source parser.

---

## Confirmed defects

| # | Component | Defect | Status |
|---|-----------|--------|--------|
| 1 | `atp_problem.ML` ↔ Zipperposition `Lex_tptp.mll` | TPTP reserved keywords (`fof`, `tff`, `cnf`, `thf`, `include`) emitted unrenamed by Sledgehammer; rejected by Zipperposition's context-insensitive lexer | Reported, two-sided fix proposed (Zipperposition GH issue #102, PR #103, branch `fix-parser-keyword-collision`, commit `5f4c9c1`) |
| 2 | Zipperposition `Unif.ml` | `CCOption.get_exn` fatal exception in `restrict_fun2.mk_rhs` on polymorphic THF input (`ANA088^1.p`) due to mismatch between `T.is_bvar_i` and `T.equal` | Reported, fix proposed (Zipperposition GH issue #104, PR #105) |
| 3 | E prover `ccl_clauses.c` | `TSTPSkipSource` aborts on list-form source fields (`[]`) routinely emitted by Sledgehammer | **Fixed upstream** by Prof. Stephan Schulz (commit `ebb74302`) |

A fourth observation — `failwith` on unknown TPTP roles in
Zipperposition's `role_of_string` — is documented as a code-quality
observation rather than a bug, since Sledgehammer never produces the
triggering roles.

---

## Repository layout

```
fyp-isabelle-fuzz/
├── README.md
├── LICENSE
├── main.md                       ← working notebook of campaign notes
│
├── scripts/
│   ├── pipeline/                 ← core fuzzing pipeline
│   ├── harnesses/                ← bug-specific fuzzers
│   ├── coverage/                 ← coverage instrumentation and analysis
│   └── utils/                    ← replay, version provenance, misc
│
├── theories/                     ← Isabelle .thy seed corpus
├── recon_seeds/                  ← seeds for the proof-reconstruction harness
│
├── ho_format_bug/                ← Bug 1 working directory + reproducer
├── real_bugs/                    ← Bug 2 working directory + reproducer
├── reproduce/                    ← Bug 3 reproducer
├── repro_chain/                  ← cross-bug minimal reproducers
│
├── sledgehammer_attack/          ← source-informed attack-surface campaign (Bug 1 lead)
├── recon_results/, recon*/       ← proof-reconstruction campaign sessions
├── targeted_results*/            ← targeted root-cause analysis runs
├── deep_results*/                ← deep root-cause analysis runs
├── diff_baseline/, diff_mutated/ ← differential testing inputs
├── soundness_session/, soundness_small/ ← soundness-check sessions (negative result)
├── replay_batch_results/         ← replay run outputs
├── validation/                   ← bug-validity check outputs
├── round3_blocks/                ← block-level delta-debugging artefacts
│
├── coverage_results/             ← aggregated coverage reports
└── bisect*.coverage              ← bisect_ppx raw coverage data (April 2026)
```

---

## Scripts

### `scripts/pipeline/` — core pipeline

| File | Purpose |
|------|---------|
| `pipeline.py` | Campaign orchestrator (generate → run → classify) |
| `driver.py` | Per-input prover driver |
| `generate_thy.py` | Isabelle `.thy` seed generator |
| `mutate.py` | `.thy` and `.tptp` mutators |
| `dedup_seeds.py` | Seed deduplication |
| `rebuild_tptp.py` | Rebuilds TPTP problems from Sledgehammer overlord output |
| `split_tptp_blocks.py` | Splits a `.p` problem into `thf(...)` blocks for delta-debugging |
| `classify_results.py` | Classifies prover outputs into pass / fail / crash / parse error |
| `validate_bugs.py` | Discriminates real bugs from noise; checks reproducibility |

### `scripts/harnesses/` — bug-specific fuzzers

| File | Purpose |
|------|---------|
| `fuzz_sledgehammer_tptp.py` | Source-informed fuzzer targeting the six attack surfaces in `atp_problem.ML`; produced **Bug 1** |
| `fuzz_real_bugs.py` | True/false lemma harness (soundness check); produced **Bug 2** lead |
| `fuzz_reconstruction.py` | Outbound proof-reconstruction pipeline; produced **Bug 3** |
| `fuzz_proof_recon.py` | Inbound TSTP-parser harness (`atp_proof.ML`); negative result, not in paper |
| `targeted_fuzz.py`, `targeted_fuzz_deep.py` | Targeted fuzzers used during root-cause analysis |
| `differential_fuzz.py` | Cross-prover differential driver (Zipperposition / E / Vampire) |
| `smt_diff_fuzz_v4.py` | Final SMT-LIB differential fuzzer (CVC5 1.2.0 vs 1.3.4-dev). `smt_diff_fuzz.py`, `_v2.py`, `_v3.py` are earlier iterations kept for provenance |
| `edge_case_generator.py` | Hand-crafted TPTP edge-case generator |
| `negate_conjectures.py` | Negates TPTP conjectures for soundness testing |

### `scripts/coverage/` — coverage measurement

| File | Purpose |
|------|---------|
| `coverage_build.sh` | Builds Zipperposition with `bisect_ppx` instrumentation |
| `coverage_compare.py` | Aggregates and diffs coverage reports |
| `prepare_baseline.py` | Prepares baseline corpus for differential coverage |

### `scripts/utils/` — replay, provenance, misc

| File | Purpose |
|------|---------|
| `replay_batch.sh`, `replay_unique.sh` | Replay a saved corpus of inputs |
| `run_and_collect.sh` | One-shot run-and-collect wrapper |
| `collect_soundness.sh` | Builds individual `.thy` files in `soundness_session/` and collects their `.p` outputs |
| `generate_smt_seeds.sh` | SMT-LIB seed generator |
| `test_ho_format_bug.sh` | Bug 1 reproduction script |
| `version_provenance.sh` | Records exact versions of all provers used (writes to `version_provenance.txt`) |

`version_provenance.txt` (in the repo root) is the recorded output for the
versions used in the campaigns.

---

## Environment

Experiments were performed on:

- **Hardware:** MacBook Pro (14-inch, 2024), Apple M4, 16 GiB RAM
- **OS:** macOS 15.4
- **Isabelle:** Isabelle2025-2 (with bundled provers)
- **Zipperposition:** 2.1; opam switches `default` for production runs and
  `4.14.0+afl` for AFL++ campaigns
- **E prover:** 3.2.5-ho ("Puttabong Moondrop", commit `be41955`); the
  Isabelle-bundled binary is x86\_64 via Rosetta on Apple Silicon
- **Vampire:** 4.8 (Isabelle-bundled, x86\_64 via Rosetta) — used as the
  differential reference
- **CVC5:** 1.2.0 (Isabelle-bundled, native arm64) and self-built 1.3.4-dev
- **AFL++:** 4.35c

`version_provenance.txt` records the exact versions used during the
campaigns.

---

## Reproducing the three defects

All commands below are run from the repository root unless otherwise
noted. Scripts that take an `--output-dir` accept an absolute path; the
defaults assume the repo lives at `~/fyp-isabelle-fuzz`.

### Bug 1 — TPTP keyword collision

```bash
cd ho_format_bug
# See the included theory and minimised .p file. With a stock
# Isabelle2025-2 + bundled Zipperposition 2.1, Sledgehammer dispatches
# but Zipperposition reports a syntax error on the unrenamed `cnf`
# constant.
```

The two-sided fix lives in the patched fork of Zipperposition (branch
`fix-parser-keyword-collision`, commit `5f4c9c1`) and is mirrored as
GitHub issue #102 / PR #103 against the upstream Zipperposition repo.

### Bug 2 — `CCOption.get_exn` in `Unif.ml`

```bash
cd real_bugs
zipperposition --input tptp ANA088^1.p
# → Fatal exception: CCOption.get_exn (Unif.ml)
```

Vampire returns `Theorem` on the same input in 0.053 s, confirming the
problem is in Zipperposition's unifier rather than the input.
GitHub issue #104 / PR #105.

### Bug 3 — E prover `TSTPSkipSource` on list-form sources

```bash
cd reproduce
eprover --auto bug3_minimal.p
# → Fatal: TSTPSkipSource: unrecognised source format
```

The fix has been merged upstream as commit `ebb74302`. Build E from a
revision newer than that to verify the crash is gone.

---

## Reproducing the AFL++ negative result

```bash
opam switch create 4.14.0+afl
opam switch 4.14.0+afl
# Build Zipperposition with the AFL-instrumented OCaml compiler, then:
afl-fuzz -i recon_seeds/ -o findings/ -- ./zipperposition.exe @@
```

The campaign reported in the paper ran for 70 hours, executed 22.9 million
inputs at an average of 91 exec/sec, with map density 0.17 % and stability
46–65 %. **Zero crashes were saved.** All 100 retained "hangs" were
legitimate `ResourceOut` timeouts on lambda-heavy benchmarks, not defects.

We treat this as a substantive negative result: blind coverage-guided
fuzzing is poorly matched to a saturation-based theorem prover. A separate
`bisect_ppx`-instrumented build (see `scripts/coverage/coverage_build.sh`),
run after the AFL++ campaign, confirmed that the campaign explored a
small, shallow region of the program.

---

## Coverage measurement

`bisect_ppx` for Zipperposition raised line coverage from **19.59 %**
(default test suite) to **27.57 %** under the targeted corpus, with
`Unif.ml` (the site of Bug 2) climbing by **30.4 percentage points**.

`gcc/lcov` for E prover showed baseline **26.9 %** versus **3.2 %** on the
Sledgehammer-driven path, with `ccl_clauses.c` (the site of Bug 3) at
**33.0 %** versus **0.4 %** — an 82.5× disparity that explains how the
Bug 3 crash survived in shipping releases.

Aggregated reports are in `coverage_results/`. Raw `bisect_ppx` data is in
`bisect327438452.coverage` and `bisect716426294.coverage`. Both were
generated from the **13 April 2026** runs; the build environment has since
been retired and re-running is not recommended.

---

## Citation

If you use this artifact, please cite both the paper and the Zenodo record:

```bibtex
@inproceedings{validating_the_verifier_2026,
  author    = {anon.},
  title     = {Validating the Verifier: Automated Testing for
               {Isabelle/HOL} Proof Assistant},
  year      = {2026},
}

@misc{xu_2026_zenodo,
  author       = {Xu, Jiangjing},
  title        = {{fyp-isabelle-fuzz}: Source-Informed Fuzzing of
                  {Sledgehammer}'s External {ATP} Interface},
  year         = {2026},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.XXXXXXX},
}
```

The Zenodo DOI will be issued automatically when the GitHub release is
published; replace `XXXXXXX` with the actual record ID.

---

## Acknowledgements

This work was supervised by Dr Mohammad Abdulaziz and Dr Karine Even-Mendoza
at King's College London. Prof. Stephan Schulz (DHBW Stuttgart) merged the
fix for Bug 3. Alexander Steen confirmed the TPTP keyword-handling
specification underlying Bug 1. The Zipperposition maintainer
(`nartannt` on GitHub) received the bug reports for Bugs 1 and 2.

---

## License

MIT — see `LICENSE`.
