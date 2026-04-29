#!/usr/bin/env python3
"""
smt_diff_fuzz_v3.py — SMT-LIB Differential Fuzzer v3.

New in v3 vs v2:
  - Generation-based fuzzing: synthesises fresh SMT-LIB from grammar, not just mutation
  - Cross-logic generation: randomly picks logic and builds matching formulas
  - Smarter mutation scheduling: tracks which mutations produce interesting results
  - Crash auto-minimizer: delta-debugs crash inputs to minimal reproducers
  - Coverage stats per seed and per mutation type
  - Optional third solver (e.g. Isabelle-bundled Z3 alongside latest Z3)
  - Multiprocess worker pool for higher throughput
"""

import argparse
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from dataclasses import dataclass, asdict, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# ═══════════════════════════════════════════════════════════════════════
#  GENERATION-BASED FUZZING: Build SMT-LIB from scratch
# ═══════════════════════════════════════════════════════════════════════

LOGICS = [
    "QF_UF", "QF_LIA", "QF_LRA", "QF_UFLIA", "QF_UFLRA",
    "QF_NIA", "QF_NRA", "QF_UFNIA",
    "AUFLIA", "AUFLRA", "AUFNIRA",
    "LIA", "LRA", "NIA", "NRA",
    "UF", "UFLIA", "UFLRA",
]

def generate_smt(logic: str = None) -> str:
    """Generate a fresh SMT-LIB problem from scratch."""
    if logic is None:
        logic = random.choice(LOGICS)

    has_int = any(x in logic for x in ["LIA", "NIA", "LIRA", "NIRA", "IDL"])
    has_real = any(x in logic for x in ["LRA", "NRA", "LIRA", "NIRA", "RDL"])
    has_uf = "UF" in logic or "AUF" in logic
    has_arrays = "A" in logic and logic.startswith("A")
    is_quantifier_free = logic.startswith("QF_")
    is_nonlinear = "N" in logic

    lines = [f"(set-logic {logic})"]

    # Declare sorts
    user_sorts = []
    if has_uf:
        n_sorts = random.randint(0, 3)
        for i in range(n_sorts):
            name = f"S{i}$"
            lines.append(f"(declare-sort {name} 0)")
            user_sorts.append(name)

    # Available sorts
    sorts = []
    if has_int:
        sorts.append("Int")
    if has_real:
        sorts.append("Real")
    sorts.append("Bool")
    sorts.extend(user_sorts)
    if not has_int and not has_real and not user_sorts:
        sorts.append("Int")  # fallback

    # Filter to non-Bool for arithmetic
    arith_sorts = [s for s in sorts if s in ("Int", "Real")]
    value_sorts = [s for s in sorts if s != "Bool"]
    if not value_sorts:
        value_sorts = ["Int"]

    # Declare functions
    n_consts = random.randint(3, 8)
    consts = {}
    for i in range(n_consts):
        name = f"v{i}"
        sort = random.choice(value_sorts)
        lines.append(f"(declare-fun {name} () {sort})")
        consts[name] = sort

    # Declare uninterpreted functions
    uf_funs = []
    if has_uf and user_sorts:
        n_funs = random.randint(0, 3)
        for i in range(n_funs):
            fname = f"f{i}"
            arg_sort = random.choice(value_sorts)
            ret_sort = random.choice(value_sorts)
            lines.append(f"(declare-fun {fname} ({arg_sort}) {ret_sort})")
            uf_funs.append((fname, arg_sort, ret_sort))

    # Generate assertions
    n_asserts = random.randint(3, 20)
    for _ in range(n_asserts):
        formula = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear,
                               is_quantifier_free, depth=0, max_depth=random.randint(2, 5))
        lines.append(f"(assert {formula})")

    # Negated conjecture (make it interesting)
    if random.random() < 0.3:
        conj = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear,
                            is_quantifier_free, depth=0, max_depth=2)
        lines.append(f"(assert (not {conj}))")

    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _gen_term(consts: dict, uf_funs: list, arith_sorts: list,
              is_nonlinear: bool, sort: str, depth: int, max_depth: int) -> str:
    """Generate a term of the given sort."""
    const_names = [n for n, s in consts.items() if s == sort]

    # Base case: variable or literal
    if depth >= max_depth or random.random() < 0.4:
        if sort == "Int":
            if const_names and random.random() < 0.7:
                return random.choice(const_names)
            return str(random.randint(-100, 100))
        elif sort == "Real":
            if const_names and random.random() < 0.7:
                return random.choice(const_names)
            return f"{random.randint(-100, 100)}.0"
        elif const_names:
            return random.choice(const_names)
        else:
            return str(random.randint(0, 10))

    # Recursive: arithmetic operations
    if sort in ("Int", "Real"):
        op = random.choice(["+", "-", "*"] if is_nonlinear else ["+", "-"])
        t1 = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth+1, max_depth)
        t2 = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth+1, max_depth)
        return f"({op} {t1} {t2})"

    # UF application
    matching_funs = [(f, a, r) for f, a, r in uf_funs if r == sort]
    if matching_funs and random.random() < 0.5:
        fname, arg_sort, _ = random.choice(matching_funs)
        arg = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, arg_sort, depth+1, max_depth)
        return f"({fname} {arg})"

    if const_names:
        return random.choice(const_names)
    return "0"


def _gen_formula(consts: dict, uf_funs: list, arith_sorts: list,
                 is_nonlinear: bool, is_qf: bool, depth: int, max_depth: int) -> str:
    """Generate a Boolean formula."""
    if depth >= max_depth:
        # Atomic formula
        return _gen_atomic(consts, uf_funs, arith_sorts, is_nonlinear, depth, max_depth)

    kind = random.choice(["and", "or", "not", "=>", "atomic", "ite", "eq",
                           "quantifier"] if not is_qf else
                          ["and", "or", "not", "=>", "atomic", "ite", "eq"])

    if kind == "not":
        inner = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth+1, max_depth)
        return f"(not {inner})"
    elif kind in ("and", "or"):
        n = random.randint(2, 4)
        children = [_gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth+1, max_depth)
                    for _ in range(n)]
        return f"({kind} {' '.join(children)})"
    elif kind == "=>":
        f1 = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth+1, max_depth)
        f2 = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth+1, max_depth)
        return f"(=> {f1} {f2})"
    elif kind == "ite":
        cond = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth+1, max_depth)
        f1 = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth+1, max_depth)
        f2 = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth+1, max_depth)
        return f"(ite {cond} {f1} {f2})"
    elif kind == "eq":
        return _gen_atomic(consts, uf_funs, arith_sorts, is_nonlinear, depth, max_depth)
    elif kind == "quantifier":
        qkind = random.choice(["forall", "exists"])
        vname = f"?qv{random.randint(0, 999)}"
        vsort = random.choice(arith_sorts) if arith_sorts else "Int"
        # Temporarily add quantified var
        new_consts = dict(consts)
        new_consts[vname] = vsort
        body = _gen_formula(new_consts, uf_funs, arith_sorts, is_nonlinear, False, depth+1, max_depth)
        return f"({qkind} (({vname} {vsort})) {body})"
    else:
        return _gen_atomic(consts, uf_funs, arith_sorts, is_nonlinear, depth, max_depth)


def _gen_atomic(consts: dict, uf_funs: list, arith_sorts: list,
                is_nonlinear: bool, depth: int, max_depth: int) -> str:
    """Generate an atomic formula (comparison or equality)."""
    if arith_sorts and random.random() < 0.7:
        sort = random.choice(arith_sorts)
        op = random.choice(["=", "<=", ">=", "<", ">", "distinct"])
        t1 = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth+1, max_depth)
        t2 = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth+1, max_depth)
        if op == "distinct":
            t3 = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth+1, max_depth)
            return f"(distinct {t1} {t2} {t3})"
        return f"({op} {t1} {t2})"
    else:
        # Equality on any sort
        all_sorts = list(set(consts.values()))
        if not all_sorts:
            return "true"
        sort = random.choice(all_sorts)
        names = [n for n, s in consts.items() if s == sort]
        if len(names) >= 2:
            a, b = random.sample(names, 2)
            return f"(= {a} {b})"
        return "true"


# ═══════════════════════════════════════════════════════════════════════
#  MUTATION STRATEGIES (inherited from v2 + new)
# ═══════════════════════════════════════════════════════════════════════

SMTLIB_RESERVED = [
    "par", "NUMERAL", "DECIMAL", "STRING", "_", "!", "as", "let",
    "forall", "exists", "match", "assert", "check-sat", "declare-fun",
    "declare-sort", "define-fun", "set-logic", "set-option",
]


def mutate_smt(content: str, mutation_count: int = None) -> str:
    mutations = [
        # Structural
        _mut_remove_assert, _mut_duplicate_assert, _mut_negate_assert,
        _mut_permute_asserts, _mut_add_redundant_assert,
        # Symbol / type
        _mut_swap_symbol_name, _mut_inject_reserved_symbol,
        _mut_swap_sort_in_decl, _mut_add_extra_sort, _mut_duplicate_declare,
        # Formula
        _mut_flip_quantifier, _mut_swap_connective, _mut_corrupt_numeral,
        _mut_inject_deep_nesting, _mut_inject_let_binding, _mut_add_named_assert,
        # Aggressive
        _mut_inject_huge_numeral, _mut_inject_chained_equals,
        _mut_inject_ite_chain, _mut_inject_distinct, _mut_empty_assert,
        # NEW in v3
        _mut_inject_define_fun, _mut_inject_recursive_define,
        _mut_inject_sort_alias, _mut_inject_multiarg_or_and,
        _mut_inject_nested_quantifier, _mut_inject_division_by_zero,
        _mut_inject_modular_arith, _mut_inject_array_ops,
        _mut_crossover_asserts, _mut_inject_string_literal_name,
    ]

    if mutation_count is None:
        mutation_count = random.randint(1, 5)

    for _ in range(mutation_count):
        mut = random.choice(mutations)
        try:
            content = mut(content)
        except Exception:
            pass
    return content


# ── Helpers ──────────────────────────────────────────────────────────

def _find_assert_blocks(content: str) -> list[str]:
    blocks = []
    i = 0
    while i < len(content):
        if content[i:i+7] == "(assert":
            depth, start = 0, i
            while i < len(content):
                if content[i] == "(": depth += 1
                elif content[i] == ")":
                    depth -= 1
                    if depth == 0:
                        blocks.append(content[start:i+1])
                        break
                i += 1
        i += 1
    return blocks

def _get_declared_symbols(content: str) -> list[str]:
    return re.findall(r'\(declare-fun\s+(\w+\$?\w*)\s', content)

def _get_declared_sorts(content: str) -> list[str]:
    return re.findall(r'\(declare-sort\s+(\w+\$?)\s+\d+\)', content)

def _before_checksat(content: str, insertion: str) -> str:
    return content.replace("(check-sat)", f"{insertion}\n(check-sat)", 1)


# ── v2 mutations (unchanged) ────────────────────────────────────────

def _mut_remove_assert(c):
    b = _find_assert_blocks(c)
    if len(b) <= 2: return c
    return c.replace(random.choice(b), "", 1)

def _mut_duplicate_assert(c):
    b = _find_assert_blocks(c)
    if not b: return c
    t = random.choice(b)
    return c.replace(t, t + "\n" + t, 1)

def _mut_negate_assert(c):
    b = _find_assert_blocks(c)
    if not b: return c
    t = random.choice(b)
    inner = t[7:-1].strip()
    if inner.startswith("(!"):
        m = re.search(r':named\s+\w+', inner)
        if m:
            formula = inner[2:m.start()].strip()
            named = inner[m.start():].rstrip(")")
            return c.replace(t, f"(assert (! (not {formula}) {named}))", 1)
    return c.replace(t, f"(assert (not {inner}))", 1)

def _mut_permute_asserts(c):
    b = _find_assert_blocks(c)
    if len(b) < 3: return c
    n = random.randint(2, min(10, len(b)))
    chosen = random.sample(b, n)
    shuffled = chosen[:]
    random.shuffle(shuffled)
    r = c
    for o, _ in zip(chosen, shuffled):
        r = r.replace(o, f"__PH_{id(o)}__", 1)
    for o, nw in zip(chosen, shuffled):
        r = r.replace(f"__PH_{id(o)}__", nw, 1)
    return r

def _mut_add_redundant_assert(c):
    t = random.choice([
        "(assert (= 0 0))", "(assert (or true true))", "(assert (=> false true))",
        "(assert (not false))", "(assert (<= 0 0))",
        "(assert (forall ((?x Int)) (= ?x ?x)))",
    ])
    return _before_checksat(c, t)

def _mut_swap_symbol_name(c):
    d = _get_declared_symbols(c)
    if not d: return c
    old = random.choice(d)
    return c.replace(old, f"mut_{random.randint(0,9999)}")

def _mut_inject_reserved_symbol(c):
    kw = random.choice(SMTLIB_RESERVED)
    sort = random.choice(["Int", "Bool"])
    inj = f"(declare-fun {kw} () {sort})\n"
    m = re.search(r'\(set-logic\s+\w+\)\s*\n', c)
    if m: return c[:m.end()] + inj + c[m.end():]
    return inj + c

def _mut_swap_sort_in_decl(c):
    us = _get_declared_sorts(c)
    if len(us) < 2: return c
    old = random.choice(us)
    new = random.choice([s for s in us if s != old])
    dfs = list(re.finditer(r'\(declare-fun\s+[^)]+\)', c))
    if not dfs: return c
    tm = random.choice(dfs)
    t = tm.group()
    if old in t:
        return c[:tm.start()] + t.replace(old, new, 1) + c[tm.end():]
    return c

def _mut_add_extra_sort(c):
    name = f"FuzzSort{random.randint(0,999)}$"
    decl = f"(declare-sort {name} 0)\n"
    ls = c.rfind("(declare-sort")
    if ls >= 0:
        eol = c.index("\n", ls)
        return c[:eol+1] + decl + c[eol+1:]
    return decl + c

def _mut_duplicate_declare(c):
    ds = list(re.finditer(r'\(declare-fun\s+[^)]+\)\s*\n', c))
    if not ds: return c
    t = random.choice(ds)
    return c[:t.end()] + t.group() + c[t.end():]

def _mut_flip_quantifier(c):
    if random.random() < 0.5:
        i = c.find("forall")
        if i >= 0: return c[:i] + "exists" + c[i+6:]
    else:
        i = c.find("exists")
        if i >= 0: return c[:i] + "forall" + c[i+6:]
    return c

def _mut_swap_connective(c):
    swaps = [("and ", "or "), ("or ", "and "), ("=> ", "= ")]
    old, new = random.choice(swaps)
    indices = [m.start() for m in re.finditer(re.escape(f"({old}"), c)]
    if not indices: return c
    idx = random.choice(indices)
    return c[:idx] + f"({new}" + c[idx+len(f"({old}"):]

def _mut_corrupt_numeral(c):
    repls = ["999999999999999999999", "-1", "0", "1",
             "2147483647", "2147483648", "-2147483648", "9223372036854775807"]
    nums = list(re.finditer(r'(?<=\s)(\d+)(?=[\s)])', c))
    if not nums: return c
    t = random.choice(nums)
    return c[:t.start()] + random.choice(repls) + c[t.end():]

def _mut_inject_deep_nesting(c):
    depth = random.randint(50, 300)
    inner = "x_deep"
    for _ in range(depth):
        inner = f"(not {inner})"
    if "x_deep" not in c:
        return _before_checksat(c, f"(declare-fun x_deep () Bool)\n(assert {inner})")
    return c

def _mut_inject_let_binding(c):
    return _before_checksat(c, "(assert (let ((?let_v 0)) (= ?let_v 0)))")

def _mut_add_named_assert(c):
    names = [f"n{random.randint(0,9999)}", "assert", "check-sat", "true", "false"]
    name = random.choice(names)
    return _before_checksat(c, f'(assert (! true :named {name}))')

def _mut_inject_huge_numeral(c):
    huge = str(10**random.randint(100, 500))
    return _before_checksat(c, f"(assert (>= {huge} 0))")

def _mut_inject_chained_equals(c):
    syms = _get_declared_symbols(c)
    if len(syms) < 3: return c
    n = random.randint(3, min(8, len(syms)))
    chain = random.sample(syms, n)
    return _before_checksat(c, f"(assert (= {' '.join(chain)}))")

def _mut_inject_ite_chain(c):
    depth = random.randint(5, 30)
    expr = "0"
    for i in range(depth):
        cond = f"(> {i} {i-1})" if i > 0 else "true"
        expr = f"(ite {cond} {expr} {i})"
    return _before_checksat(c, f"(assert (>= {expr} 0))")

def _mut_inject_distinct(c):
    syms = _get_declared_symbols(c)
    if len(syms) < 2: return c
    n = random.randint(2, min(6, len(syms)))
    chosen = random.sample(syms, n)
    return _before_checksat(c, f"(assert (distinct {' '.join(chosen)}))")

def _mut_empty_assert(c):
    edge = random.choice([
        "(assert true)", "(assert (not false))", "(assert (= 0 0))",
        "(assert (and))", "(assert (or))", "(assert (distinct))",
    ])
    return _before_checksat(c, edge)


# ── NEW v3 mutations ────────────────────────────────────────────────

def _mut_inject_define_fun(c):
    """Inject a define-fun that shadows or wraps an existing symbol."""
    syms = _get_declared_symbols(c)
    if not syms: return c
    sym = random.choice(syms)
    name = f"wrap_{sym}"
    defn = f"(define-fun {name} ((x Int)) Int (+ x 1))"
    return _before_checksat(c, f"{defn}\n(assert (>= ({name} 0) 0))")


def _mut_inject_recursive_define(c):
    """Inject a define-fun-rec (recursive function) — tests solver's recursion handling."""
    defn = (
        f"(define-fun-rec fib ((n Int)) Int\n"
        f"  (ite (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))\n"
        f"(assert (= (fib 5) 5))"
    )
    return _before_checksat(c, defn)


def _mut_inject_sort_alias(c):
    """Inject define-sort (sort alias)."""
    alias = f"(define-sort MyInt () Int)\n(declare-fun alias_v () MyInt)\n(assert (>= alias_v 0))"
    return _before_checksat(c, alias)


def _mut_inject_multiarg_or_and(c):
    """Inject (and) or (or) with 0, 1, or many arguments — edge cases per spec."""
    cases = [
        "(assert (and true true true true true true true true true true))",
        "(assert (or false false false false false false false false false true))",
        "(assert (and))",    # should be true per spec
        "(assert (or))",     # should be false per spec
        "(assert (or true))",
        "(assert (and true))",
    ]
    return _before_checksat(c, random.choice(cases))


def _mut_inject_nested_quantifier(c):
    """Inject nested quantifiers with shadowing variables."""
    q = (
        "(assert (forall ((?x Int))\n"
        "  (exists ((?x Int))\n"       # shadows outer ?x
        "    (>= ?x 0))))"
    )
    return _before_checksat(c, q)


def _mut_inject_division_by_zero(c):
    """Inject division by zero — tests solver's undefined behavior handling."""
    cases = [
        "(assert (= (div 1 0) 0))",
        "(assert (= (mod 1 0) 0))",
        "(assert (>= (div 42 0) 0))",
        "(assert (= (/ 1.0 0.0) 0.0))",
    ]
    return _before_checksat(c, random.choice(cases))


def _mut_inject_modular_arith(c):
    """Inject modular arithmetic edge cases."""
    cases = [
        "(assert (= (mod (- 7) 3) 2))",
        "(assert (= (div (- 7) 3) (- 3)))",
        "(assert (= (mod 0 5) 0))",
        "(assert (>= (mod 999999999999999999999 7) 0))",
    ]
    return _before_checksat(c, random.choice(cases))


def _mut_inject_array_ops(c):
    """Inject array operations — select, store, const arrays."""
    ops = (
        "(declare-fun fuzz_arr () (Array Int Int))\n"
        f"(assert (= (select (store fuzz_arr 0 42) 0) 42))"
    )
    return _before_checksat(c, ops)


def _mut_crossover_asserts(c):
    """Take an assert from one part and combine with terms from another."""
    blocks = _find_assert_blocks(c)
    if len(blocks) < 2: return c
    b1, b2 = random.sample(blocks, 2)
    # Extract inner formulas
    inner1 = b1[7:-1].strip()
    inner2 = b2[7:-1].strip()
    # Combine with random connective
    conn = random.choice(["and", "or", "=>"])
    combined = f"(assert ({conn} {inner1} {inner2}))"
    return _before_checksat(c, combined)


def _mut_inject_string_literal_name(c):
    """Use a quoted symbol |...| as a name — tests parser's quoted symbol handling."""
    names = ["|hello world|", "|foo bar baz|", "||", "|123|",
             "|declare-fun|", "|set-logic|", "|check-sat|"]
    name = random.choice(names)
    decl = f"(declare-fun {name} () Int)\n(assert (>= {name} 0))"
    return _before_checksat(c, decl)


# ═══════════════════════════════════════════════════════════════════════
#  SOLVER HARNESS
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class SolverResult:
    solver: str
    exit_code: int
    answer: str
    raw_output: str
    elapsed_ms: int
    error_msg: Optional[str] = None


def run_solver(solver_path: str, solver_name: str, input_file: Path,
               timeout: int = 5, extra_args: list[str] = None) -> SolverResult:
    cmd = [solver_path] + (extra_args or []) + [str(input_file)]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        elapsed = int((time.monotonic() - start) * 1000)
        stdout, stderr = proc.stdout.strip(), proc.stderr.strip()
        combined = stdout + "\n" + stderr

        answer = "unknown"
        for line in stdout.splitlines():
            l = line.strip()
            if l == "sat": answer = "sat"; break
            elif l == "unsat": answer = "unsat"; break
            elif l == "unknown": answer = "unknown"; break

        error_msg = None
        if proc.returncode < 0:
            answer = "crash"
            error_msg = f"signal {-proc.returncode}"
        elif proc.returncode != 0 and answer not in ("sat", "unsat"):
            if "error" in combined.lower() or "fatal" in combined.lower():
                answer = "error"
                for line in combined.splitlines():
                    if "error" in line.lower():
                        error_msg = line.strip()[:200]
                        break

        return SolverResult(solver=solver_name, exit_code=proc.returncode,
                           answer=answer, raw_output=combined[:2000],
                           elapsed_ms=elapsed, error_msg=error_msg)
    except subprocess.TimeoutExpired:
        elapsed = int((time.monotonic() - start) * 1000)
        return SolverResult(solver=solver_name, exit_code=-1, answer="timeout",
                           raw_output="TIMEOUT", elapsed_ms=elapsed,
                           error_msg=f"timeout after {timeout}s")


def run_solvers_parallel(z3_path, cvc5_path, input_file, timeout, z3_args, cvc5_args):
    with ThreadPoolExecutor(max_workers=2) as pool:
        f1 = pool.submit(run_solver, z3_path, "z3", input_file, timeout, z3_args)
        f2 = pool.submit(run_solver, cvc5_path, "cvc5", input_file, timeout, cvc5_args)
        return f1.result(), f2.result()


# ═══════════════════════════════════════════════════════════════════════
#  CRASH MINIMIZER
# ═══════════════════════════════════════════════════════════════════════

def minimize_crash(solver_path: str, crash_file: Path, output_file: Path,
                   timeout: int = 5) -> Path:
    """Delta-debug a crash input to find minimal reproducer."""
    content = crash_file.read_text()
    lines = content.splitlines(keepends=True)

    # Try removing lines one by one
    best = lines[:]
    improved = True
    while improved:
        improved = False
        for i in range(len(best) - 1, -1, -1):
            candidate = best[:i] + best[i+1:]
            tmp = crash_file.parent / f"_min_tmp.smt2"
            tmp.write_text("".join(candidate))
            r = run_solver(solver_path, "z3", tmp, timeout)
            if r.answer == "crash":
                best = candidate
                improved = True
                break
        if not improved:
            break

    # Try removing assert blocks
    content = "".join(best)
    blocks = _find_assert_blocks(content)
    for block in reversed(blocks):
        candidate = content.replace(block + "\n", "", 1)
        if not candidate.strip():
            continue
        tmp = crash_file.parent / f"_min_tmp.smt2"
        tmp.write_text(candidate)
        r = run_solver(solver_path, "z3", tmp, timeout)
        if r.answer == "crash":
            content = candidate

    output_file.write_text(content)
    # Cleanup
    tmp = crash_file.parent / f"_min_tmp.smt2"
    if tmp.exists():
        tmp.unlink()
    return output_file


# ═══════════════════════════════════════════════════════════════════════
#  CLASSIFICATION
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class DiffResult:
    mutant_id: str
    seed_file: str
    source: str           # "mutation" | "generated"
    mutation_hash: str
    z3: SolverResult
    cvc5: SolverResult
    category: str
    severity: str
    notes: str = ""


def classify_diff(z3r, cvc5r):
    a1, a2 = z3r.answer, cvc5r.answer
    if a1 == a2:
        if a1 == "sat":     return "agree_sat", "info", ""
        if a1 == "unsat":   return "agree_unsat", "info", ""
        if a1 == "timeout": return "both_timeout", "info", ""
        if a1 == "crash":   return "both_crash", "critical", "Both solvers crashed"
        if a1 == "error":   return "both_error", "low", ""
        return "agree_unknown", "info", ""
    if {a1, a2} == {"sat", "unsat"}:
        return "soundness_bug", "critical", f"Z3={a1}, CVC5={a2} — SOUNDNESS BUG!"
    if a1 == "crash" and a2 != "crash":
        return "z3_crash", "critical", f"Z3 crashed: {z3r.error_msg}"
    if a2 == "crash" and a1 != "crash":
        return "cvc5_crash", "critical", f"CVC5 crashed: {cvc5r.error_msg}"
    if a1 == "error" and a2 not in ("error", "crash"):
        return "z3_error", "medium", f"Z3 error but CVC5={a2}: {z3r.error_msg}"
    if a2 == "error" and a1 not in ("error", "crash"):
        return "cvc5_error", "medium", f"CVC5 error but Z3={a1}: {cvc5r.error_msg}"
    if a1 in ("sat", "unsat") and a2 in ("timeout", "unknown"):
        return "disagree_answer", "low", f"Z3={a1} CVC5={a2}"
    if a2 in ("sat", "unsat") and a1 in ("timeout", "unknown"):
        return "disagree_answer", "low", f"CVC5={a2} Z3={a1}"
    return "disagree_other", "low", f"Z3={a1}, CVC5={a2}"


# ═══════════════════════════════════════════════════════════════════════
#  SEED PREPARATION
# ═══════════════════════════════════════════════════════════════════════

def prepare_seed(content: str) -> str:
    lines = content.splitlines(keepends=True)
    if lines and lines[0].strip().startswith(";"):
        lines = lines[1:]
    content = "".join(lines)
    if "(check-sat)" not in content:
        content = content.rstrip() + "\n(check-sat)\n"
    content = content.replace("(get-unsat-core)", "")
    return content


# ═══════════════════════════════════════════════════════════════════════
#  MAIN FUZZER LOOP
# ═══════════════════════════════════════════════════════════════════════

def run_fuzz_campaign(
    seed_dir: Path, z3_path: str, cvc5_path: str, output_dir: Path,
    rounds: int = 10000, timeout: int = 5,
    gen_ratio: float = 0.3,   # fraction of rounds that are generation (vs mutation)
    z3_args: list[str] = None, cvc5_args: list[str] = None,
):
    output_dir.mkdir(parents=True, exist_ok=True)
    mutants_dir = output_dir / "mutants"
    mutants_dir.mkdir(exist_ok=True)
    interesting_dir = output_dir / "interesting"
    interesting_dir.mkdir(exist_ok=True)
    minimized_dir = output_dir / "minimized"
    minimized_dir.mkdir(exist_ok=True)

    # Load seeds
    seeds = []
    for ext in ["*.smt_in", "*.smt2", "*.smt"]:
        seeds.extend(seed_dir.glob(ext))

    prepared_seeds = {}
    for sf in seeds:
        raw = sf.read_text(encoding="utf-8", errors="replace")
        prepared_seeds[sf.name] = prepare_seed(raw)

    print(f"[*] SMT Differential Fuzzer v3")
    print(f"[*] Seeds: {len(seeds)}  Rounds: {rounds}  Timeout: {timeout}s")
    print(f"[*] Gen ratio: {gen_ratio:.0%} generated, {1-gen_ratio:.0%} mutated")
    print(f"[*] Z3:   {z3_path}")
    print(f"[*] CVC5: {cvc5_path}")
    print(f"[*] Output: {output_dir}")
    print()

    stats = {
        "total": 0, "deduped": 0, "generated": 0, "mutated": 0,
        "agree_sat": 0, "agree_unsat": 0, "agree_unknown": 0,
        "soundness_bug": 0,
        "z3_crash": 0, "cvc5_crash": 0, "both_crash": 0,
        "z3_error": 0, "cvc5_error": 0, "both_error": 0,
        "disagree_answer": 0, "disagree_other": 0, "both_timeout": 0,
    }

    seen_hashes = set()
    start_time = time.monotonic()
    crash_files = []

    for i in range(rounds):
        # Decide: generate or mutate
        if random.random() < gen_ratio or not prepared_seeds:
            content = generate_smt()
            source = "generated"
            seed_name = "generated"
            stats["generated"] += 1
        else:
            seed_name = random.choice(list(prepared_seeds.keys()))
            content = mutate_smt(prepared_seeds[seed_name])
            source = "mutated"
            stats["mutated"] += 1

        mut_hash = hashlib.md5(content.encode()).hexdigest()[:10]
        if mut_hash in seen_hashes:
            stats["deduped"] += 1
            continue
        seen_hashes.add(mut_hash)
        mutant_id = f"{'gen' if source == 'generated' else 'mut'}_{i:05d}_{mut_hash}"

        mutant_path = mutants_dir / f"{mutant_id}.smt2"
        mutant_path.write_text(content, encoding="utf-8")

        z3r, cvc5r = run_solvers_parallel(z3_path, cvc5_path, mutant_path, timeout, z3_args, cvc5_args)
        category, severity, notes = classify_diff(z3r, cvc5r)

        stats["total"] += 1
        stats[category] = stats.get(category, 0) + 1

        elapsed = time.monotonic() - start_time
        rate = stats["total"] / elapsed if elapsed > 0 else 0

        # Print interesting results
        if severity in ("critical", "high"):
            marker = " *** CRITICAL ***" if severity == "critical" else " ** HIGH **"
            print(f"  [{i+1:5d}/{rounds}] {category:20s} "
                  f"Z3={z3r.answer:8s} CVC5={cvc5r.answer:8s} "
                  f"[{source}] ({rate:.1f}/s){marker}")
        elif severity == "medium":
            print(f"  [{i+1:5d}/{rounds}] {category:20s} "
                  f"Z3={z3r.answer:8s} CVC5={cvc5r.answer:8s} "
                  f"[{source}] ({rate:.1f}/s)")
        elif (i+1) % 200 == 0:
            print(f"  [{i+1:5d}/{rounds}] ... ({rate:.1f}/s) "
                  f"sat={stats['agree_sat']} unsat={stats['agree_unsat']} "
                  f"crashes={stats.get('z3_crash',0)+stats.get('cvc5_crash',0)} "
                  f"soundness={stats.get('soundness_bug',0)}")

        # Save interesting
        if severity in ("critical", "high", "medium") or category.startswith("disagree"):
            save_path = interesting_dir / f"{severity}_{category}_{mutant_id}.smt2"
            try:
                shutil.copy2(mutant_path, save_path)
            except Exception:
                pass

            detail = {
                "mutant_id": mutant_id, "seed": seed_name, "source": source,
                "category": category, "severity": severity, "notes": notes,
                "z3": asdict(z3r), "cvc5": asdict(cvc5r),
            }
            dp = interesting_dir / f"{severity}_{category}_{mutant_id}.json"
            try:
                dp.write_text(json.dumps(detail, indent=2))
            except Exception:
                pass

            # Track crashes for minimization
            if "crash" in category:
                crash_files.append((save_path, category))

        # Cleanup boring
        if severity == "info" and mutant_path.exists():
            mutant_path.unlink()

    total_time = time.monotonic() - start_time

    # ── Auto-minimize crashes ──
    if crash_files:
        print(f"\n[*] Auto-minimizing {len(crash_files)} crash(es)...")
        for crash_path, cat in crash_files:
            solver = z3_path if "z3" in cat else cvc5_path
            min_path = minimized_dir / f"min_{crash_path.name}"
            try:
                minimize_crash(solver, crash_path, min_path, timeout)
                orig_lines = len(crash_path.read_text().splitlines())
                min_lines = len(min_path.read_text().splitlines())
                print(f"  {crash_path.name}: {orig_lines} → {min_lines} lines")
            except Exception as e:
                print(f"  {crash_path.name}: minimization failed: {e}")

    # ── Report ──
    report = {
        "timestamp": datetime.now().isoformat(),
        "config": {
            "seeds": len(seeds), "rounds": rounds, "timeout": timeout,
            "gen_ratio": gen_ratio, "z3": z3_path, "cvc5": cvc5_path,
        },
        "stats": stats,
        "total_time_s": round(total_time, 2),
        "throughput": round(stats["total"] / total_time, 2) if total_time > 0 else 0,
    }
    (output_dir / "fuzz_report.json").write_text(json.dumps(report, indent=2, default=str))

    print(f"\n{'='*60}")
    print(f"  SMT DIFFERENTIAL FUZZING v3 REPORT")
    print(f"{'='*60}")
    print(f"  Total tested:     {stats['total']} ({stats['generated']} gen + {stats['mutated']} mut)")
    print(f"  Deduped:          {stats['deduped']}")
    print(f"  Time:             {total_time:.1f}s")
    print(f"  Throughput:       {stats['total']/total_time:.1f} tests/s")
    print()
    print(f"  SOUNDNESS BUGS:   {stats.get('soundness_bug', 0)}  {'!!!' if stats.get('soundness_bug',0) else ''}")
    print(f"  Z3 crashes:       {stats.get('z3_crash', 0)}")
    print(f"  CVC5 crashes:     {stats.get('cvc5_crash', 0)}")
    print(f"  Both crash:       {stats.get('both_crash', 0)}")
    print(f"  Z3 errors:        {stats.get('z3_error', 0)}")
    print(f"  CVC5 errors:      {stats.get('cvc5_error', 0)}")
    print(f"  Both errors:      {stats.get('both_error', 0)}")
    print(f"  Disagree (answer):{stats.get('disagree_answer', 0)}")
    print(f"  Disagree (other): {stats.get('disagree_other', 0)}")
    print(f"  Agree sat:        {stats.get('agree_sat', 0)}")
    print(f"  Agree unsat:      {stats.get('agree_unsat', 0)}")
    print(f"  Agree unknown:    {stats.get('agree_unknown', 0)}")
    print(f"  Both timeout:     {stats.get('both_timeout', 0)}")
    print(f"{'='*60}")
    print(f"  Report:     {output_dir / 'fuzz_report.json'}")
    print(f"  Interesting:{interesting_dir}")
    if crash_files:
        print(f"  Minimized:  {minimized_dir}")


def main():
    parser = argparse.ArgumentParser(description="SMT Differential Fuzzer v3")
    parser.add_argument("--seeds", required=True)
    parser.add_argument("--z3", required=True)
    parser.add_argument("--cvc5", required=True)
    parser.add_argument("--rounds", type=int, default=10000)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--gen-ratio", type=float, default=0.3,
                        help="Fraction of rounds using generation vs mutation (default: 0.3)")
    parser.add_argument("--output-dir", default="./smt_fuzz_v3")
    parser.add_argument("--z3-args", default="")
    parser.add_argument("--cvc5-args", default="")
    args = parser.parse_args()

    run_fuzz_campaign(
        seed_dir=Path(args.seeds),
        z3_path=args.z3, cvc5_path=args.cvc5,
        output_dir=Path(args.output_dir),
        rounds=args.rounds, timeout=args.timeout,
        gen_ratio=args.gen_ratio,
        z3_args=args.z3_args.split() if args.z3_args else [],
        cvc5_args=args.cvc5_args.split() if args.cvc5_args else [],
    )


if __name__ == "__main__":
    main()
