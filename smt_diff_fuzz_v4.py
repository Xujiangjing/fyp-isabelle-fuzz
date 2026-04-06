#!/usr/bin/env python3
"""
smt_diff_fuzz_v4.py — SMT-LIB Differential Fuzzer v4.

New in v4 vs v3:
  - ERROR-AWARE CLASSIFICATION: A solver that exits non-zero or prints "(error ...)"
    has its sat/unsat answer treated as UNRELIABLE — no false soundness bugs.
  - LOGIC-AWARE MUTATIONS: Mutations respect the declared logic (no quantifiers in QF_*,
    no define-fun-rec in logics that don't support it, no arrays in non-array logics).
  - SOUNDNESS VALIDATION: Candidate soundness bugs are re-verified with a confirmation
    pass before being reported.
  - INPUT WELL-FORMEDNESS CHECK: Runs a quick syntax validation before classifying.
  - Better seed preparation: strips (get-proof), (get-model), (set-option :produce-proofs).
  - Cleaner output: severity buckets, summary of false-positive filtering.
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
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, asdict, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# ═══════════════════════════════════════════════════════════════════════
#  LOGIC METADATA
# ═══════════════════════════════════════════════════════════════════════

LOGICS = [
    "QF_UF", "QF_LIA", "QF_LRA", "QF_UFLIA", "QF_UFLRA",
    "QF_NIA", "QF_NRA", "QF_UFNIA",
    "AUFLIA", "AUFLRA", "AUFNIRA",
    "LIA", "LRA", "NIA", "NRA",
    "UF", "UFLIA", "UFLRA",
]


def parse_logic(content: str) -> dict:
    """Extract logic metadata from SMT-LIB content."""
    m = re.search(r'\(set-logic\s+(\S+)\s*\)', content)
    logic = m.group(1) if m else "ALL"
    return {
        "name": logic,
        "is_qf": logic.startswith("QF_"),
        "has_int": any(x in logic for x in ["LIA", "NIA", "LIRA", "NIRA", "IDL"]),
        "has_real": any(x in logic for x in ["LRA", "NRA", "LIRA", "NIRA", "RDL"]),
        "has_uf": "UF" in logic or "AUF" in logic,
        "has_arrays": logic.startswith("A") and "A" in logic,
        "is_nonlinear": "N" in logic and any(x in logic for x in ["NIA", "NRA", "NIRA"]),
        "supports_recfun": logic in ("ALL", "UFLIA", "AUFLRA", "AUFNIRA") or not logic.startswith("QF_"),
        "supports_strings": "S" in logic,
    }


# ═══════════════════════════════════════════════════════════════════════
#  GENERATION-BASED FUZZING: Build SMT-LIB from scratch
# ═══════════════════════════════════════════════════════════════════════

def generate_smt(logic: str = None) -> str:
    """Generate a fresh SMT-LIB problem from scratch."""
    if logic is None:
        logic = random.choice(LOGICS)

    lmeta = parse_logic(f"(set-logic {logic})")
    has_int = lmeta["has_int"]
    has_real = lmeta["has_real"]
    has_uf = lmeta["has_uf"]
    has_arrays = lmeta["has_arrays"]
    is_qf = lmeta["is_qf"]
    is_nonlinear = lmeta["is_nonlinear"]

    lines = [f"(set-logic {logic})"]

    # Declare sorts
    user_sorts = []
    if has_uf:
        # For pure UF logics (no Int/Real), guarantee at least 1 user sort
        min_sorts = 1 if (not has_int and not has_real) else 0
        n_sorts = random.randint(min_sorts, 3)
        for i in range(n_sorts):
            name = f"S{i}$"
            lines.append(f"(declare-sort {name} 0)")
            user_sorts.append(name)

    # Available sorts — only include types the logic actually supports
    sorts = []
    if has_int:
        sorts.append("Int")
    if has_real:
        sorts.append("Real")
    sorts.append("Bool")
    sorts.extend(user_sorts)
    # NO fallback to Int — if the logic doesn't have Int, don't inject it

    arith_sorts = [s for s in sorts if s in ("Int", "Real")]
    value_sorts = [s for s in sorts if s != "Bool"]
    if not value_sorts:
        # Pure Bool logic with no user sorts — just use Bool
        value_sorts = ["Bool"]

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
                               is_qf, depth=0, max_depth=random.randint(2, 5))
        lines.append(f"(assert {formula})")

    if random.random() < 0.3:
        conj = _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear,
                            is_qf, depth=0, max_depth=2)
        lines.append(f"(assert (not {conj}))")

    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth, max_depth):
    const_names = [n for n, s in consts.items() if s == sort]
    if depth >= max_depth or random.random() < 0.4:
        if sort == "Int":
            if const_names and random.random() < 0.7:
                return random.choice(const_names)
            return str(random.randint(-100, 100))
        elif sort == "Real":
            if const_names and random.random() < 0.7:
                return random.choice(const_names)
            return f"{random.randint(-100, 100)}.0"
        elif sort == "Bool":
            if const_names and random.random() < 0.7:
                return random.choice(const_names)
            return random.choice(["true", "false"])
        elif const_names:
            # User-defined sort — can only use declared constants of that sort
            return random.choice(const_names)
        else:
            # No constants of this sort available — try UF application
            matching_funs = [(f, a, r) for f, a, r in uf_funs if r == sort]
            if matching_funs:
                fname, arg_sort, _ = random.choice(matching_funs)
                arg = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear,
                                arg_sort, max_depth, max_depth)  # force base case
                return f"({fname} {arg})"
            # Last resort: declare won't help here, just use true as a safe fallback
            return "true"

    if sort in ("Int", "Real"):
        op = random.choice(["+", "-", "*"] if is_nonlinear else ["+", "-"])
        t1 = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth+1, max_depth)
        t2 = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, sort, depth+1, max_depth)
        return f"({op} {t1} {t2})"

    matching_funs = [(f, a, r) for f, a, r in uf_funs if r == sort]
    if matching_funs and random.random() < 0.5:
        fname, arg_sort, _ = random.choice(matching_funs)
        arg = _gen_term(consts, uf_funs, arith_sorts, is_nonlinear, arg_sort, depth+1, max_depth)
        return f"({fname} {arg})"

    if const_names:
        return random.choice(const_names)
    return "true"  # safe fallback for any sort


def _gen_formula(consts, uf_funs, arith_sorts, is_nonlinear, is_qf, depth, max_depth):
    if depth >= max_depth:
        return _gen_atomic(consts, uf_funs, arith_sorts, is_nonlinear, depth, max_depth)

    choices = ["and", "or", "not", "=>", "atomic", "ite", "eq"]
    if not is_qf:
        choices.append("quantifier")

    kind = random.choice(choices)

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
    elif kind == "quantifier":
        qkind = random.choice(["forall", "exists"])
        vname = f"?qv{random.randint(0, 999)}"
        vsort = random.choice(arith_sorts) if arith_sorts else "Int"
        new_consts = dict(consts)
        new_consts[vname] = vsort
        body = _gen_formula(new_consts, uf_funs, arith_sorts, is_nonlinear, False, depth+1, max_depth)
        return f"({qkind} (({vname} {vsort})) {body})"
    else:
        return _gen_atomic(consts, uf_funs, arith_sorts, is_nonlinear, depth, max_depth)


def _gen_atomic(consts, uf_funs, arith_sorts, is_nonlinear, depth, max_depth):
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
#  MUTATION STRATEGIES — now logic-aware
# ═══════════════════════════════════════════════════════════════════════

SMTLIB_RESERVED = [
    "par", "NUMERAL", "DECIMAL", "STRING", "_", "!", "as", "let",
    "forall", "exists", "match", "assert", "check-sat", "declare-fun",
    "declare-sort", "define-fun", "set-logic", "set-option",
]


def mutate_smt(content: str, mutation_count: int = None) -> str:
    """Apply logic-aware mutations to SMT-LIB content."""
    lmeta = parse_logic(content)

    # Build mutation pool based on logic capabilities
    mutations = [
        # Structural (always safe — no type assumptions)
        _mut_remove_assert, _mut_duplicate_assert, _mut_negate_assert,
        _mut_permute_asserts, _mut_add_redundant_assert_safe,
        # Symbol / type
        _mut_swap_symbol_name, _mut_swap_sort_in_decl, _mut_add_extra_sort,
        _mut_duplicate_declare,
        # Formula (type-agnostic)
        _mut_swap_connective,
        _mut_inject_deep_nesting, _mut_add_named_assert,
        _mut_inject_multiarg_or_and, _mut_crossover_asserts,
        _mut_empty_assert,
    ]

    # Mutations that inject Int-typed constructs — only if logic has Int
    if lmeta["has_int"] or lmeta["has_real"]:
        mutations.extend([
            _mut_corrupt_numeral,
            _mut_inject_huge_numeral,
            _mut_inject_chained_equals,
            _mut_inject_ite_chain,
            _mut_inject_distinct,
            _mut_inject_let_binding,
            _mut_inject_define_fun,
            _mut_inject_sort_alias,
            _mut_inject_string_literal_name,
        ])
    else:
        # For pure UF logics, only add type-safe versions
        mutations.extend([
            _mut_inject_distinct,  # fixed to be sort-safe
            _mut_inject_chained_equals,  # fixed to be sort-safe
        ])

    # Logic-conditional mutations
    if not lmeta["is_qf"]:
        mutations.extend([
            _mut_flip_quantifier,
            _mut_inject_nested_quantifier,
        ])

    if lmeta["has_int"]:
        mutations.extend([
            _mut_inject_division_by_zero_int,
            _mut_inject_modular_arith,
        ])

    if lmeta["has_real"]:
        mutations.append(_mut_inject_division_by_zero_real)

    if lmeta["has_arrays"]:
        mutations.append(_mut_inject_array_ops)

    if lmeta["supports_recfun"]:
        mutations.append(_mut_inject_recursive_define)

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

def _find_assert_blocks(content: str) -> list:
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

def _get_declared_symbols(content: str) -> list:
    return re.findall(r'\(declare-fun\s+(\w+\$?\w*)\s', content)

def _get_declared_sorts(content: str) -> list:
    return re.findall(r'\(declare-sort\s+(\w+\$?)\s+\d+\)', content)

def _before_checksat(content: str, insertion: str) -> str:
    return content.replace("(check-sat)", f"{insertion}\n(check-sat)", 1)


# ── Structural mutations ───────────────────────────────────────────

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

def _mut_add_redundant_assert_safe(c):
    """Only add redundant assertions that are valid in any logic (no quantifiers)."""
    t = random.choice([
        "(assert (= 0 0))", "(assert (or true true))", "(assert (=> false true))",
        "(assert (not false))", "(assert (<= 0 0))",
    ])
    return _before_checksat(c, t)

def _mut_swap_symbol_name(c):
    d = _get_declared_symbols(c)
    if not d: return c
    old = random.choice(d)
    return c.replace(old, f"mut_{random.randint(0,9999)}")

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
    # CVC5 strictly rejects duplicate declare-fun; instead rename the duplicate
    ds = list(re.finditer(r'\(declare-fun\s+(\w+\$?\w*)\s+([^)]*)\)\s*\n', c))
    if not ds: return c
    t = random.choice(ds)
    orig_name = t.group(1)
    new_name = f"{orig_name}_dup{random.randint(0, 99)}"
    new_decl = t.group().replace(orig_name, new_name, 1)
    return c[:t.end()] + new_decl + c[t.end():]

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
    # Only chain symbols of the same sort to avoid type errors
    decls = re.findall(r'\(declare-fun\s+(\w+\$?\w*)\s+\(\)\s+(\w+)', c)
    if len(decls) < 3: return c
    by_sort = {}
    for name, sort in decls:
        by_sort.setdefault(sort, []).append(name)
    candidates = {s: ns for s, ns in by_sort.items() if len(ns) >= 3}
    if not candidates: return c
    sort = random.choice(list(candidates.keys()))
    syms = candidates[sort]
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
    # Only use symbols of the same sort to avoid type errors
    decls = re.findall(r'\(declare-fun\s+(\w+\$?\w*)\s+\(\)\s+(\w+)', c)
    if len(decls) < 2: return c
    by_sort = {}
    for name, sort in decls:
        by_sort.setdefault(sort, []).append(name)
    candidates = {s: ns for s, ns in by_sort.items() if len(ns) >= 2}
    if not candidates: return c
    sort = random.choice(list(candidates.keys()))
    syms = candidates[sort]
    n = random.randint(2, min(6, len(syms)))
    chosen = random.sample(syms, n)
    return _before_checksat(c, f"(assert (distinct {' '.join(chosen)}))")

def _mut_empty_assert(c):
    # Avoid zero-arg (and)/(or)/(distinct) — CVC5 rejects these per stricter spec reading
    edge = random.choice([
        "(assert true)", "(assert (not false))", "(assert (= 0 0))",
        "(assert (and true true))", "(assert (or false true))",
    ])
    return _before_checksat(c, edge)


# ── Logic-conditional mutations ────────────────────────────────────

def _mut_inject_define_fun(c):
    syms = _get_declared_symbols(c)
    if not syms: return c
    sym = random.choice(syms)
    name = f"wrap_{sym}"
    defn = f"(define-fun {name} ((x Int)) Int (+ x 1))"
    return _before_checksat(c, f"{defn}\n(assert (>= ({name} 0) 0))")

def _mut_inject_recursive_define(c):
    """Only called when logic supports define-fun-rec."""
    defn = (
        f"(define-fun-rec fib ((n Int)) Int\n"
        f"  (ite (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))\n"
        f"(assert (= (fib 5) 5))"
    )
    return _before_checksat(c, defn)

def _mut_inject_sort_alias(c):
    alias = f"(define-sort MyInt () Int)\n(declare-fun alias_v () MyInt)\n(assert (>= alias_v 0))"
    return _before_checksat(c, alias)

def _mut_inject_multiarg_or_and(c):
    # Avoid zero-arg (and)/(or) — CVC5 rejects them
    cases = [
        "(assert (and true true true true true true true true true true))",
        "(assert (or false false false false false false false false false true))",
        "(assert (or true))",
        "(assert (and true))",
    ]
    return _before_checksat(c, random.choice(cases))

def _mut_inject_nested_quantifier(c):
    """Only called for non-QF logics."""
    q = (
        "(assert (forall ((?x Int))\n"
        "  (exists ((?x Int))\n"
        "    (>= ?x 0))))"
    )
    return _before_checksat(c, q)

def _mut_inject_division_by_zero_int(c):
    """Only called when logic has Int."""
    cases = [
        "(assert (= (div 1 0) 0))",
        "(assert (= (mod 1 0) 0))",
        "(assert (>= (div 42 0) 0))",
    ]
    return _before_checksat(c, random.choice(cases))

def _mut_inject_division_by_zero_real(c):
    """Only called when logic has Real."""
    return _before_checksat(c, "(assert (= (/ 1.0 0.0) 0.0))")

def _mut_inject_modular_arith(c):
    """Only called when logic has Int."""
    cases = [
        "(assert (= (mod (- 7) 3) 2))",
        "(assert (= (div (- 7) 3) (- 3)))",
        "(assert (= (mod 0 5) 0))",
        "(assert (>= (mod 999999999999999999999 7) 0))",
    ]
    return _before_checksat(c, random.choice(cases))

def _mut_inject_array_ops(c):
    """Only called when logic has arrays."""
    ops = (
        "(declare-fun fuzz_arr () (Array Int Int))\n"
        f"(assert (= (select (store fuzz_arr 0 42) 0) 42))"
    )
    return _before_checksat(c, ops)

def _mut_crossover_asserts(c):
    blocks = _find_assert_blocks(c)
    if len(blocks) < 2: return c
    b1, b2 = random.sample(blocks, 2)
    inner1 = b1[7:-1].strip()
    inner2 = b2[7:-1].strip()
    conn = random.choice(["and", "or", "=>"])
    combined = f"(assert ({conn} {inner1} {inner2}))"
    return _before_checksat(c, combined)

def _mut_inject_string_literal_name(c):
    # Avoid || (empty quoted symbol) — CVC5 rejects it
    names = ["|hello world|", "|foo bar baz|", "|123|",
             "|declare-fun|", "|set-logic|", "|check-sat|"]
    name = random.choice(names)
    decl = f"(declare-fun {name} () Int)\n(assert (>= {name} 0))"
    return _before_checksat(c, decl)


# ═══════════════════════════════════════════════════════════════════════
#  SOLVER HARNESS — error-aware answer extraction
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class SolverResult:
    solver: str
    exit_code: int
    answer: str           # "sat" | "unsat" | "unknown" | "crash" | "error" | "timeout"
    answer_reliable: bool # False if solver printed errors alongside sat/unsat
    raw_output: str
    elapsed_ms: int
    error_msg: Optional[str] = None
    has_errors: bool = False  # True if (error ...) appeared in output


def run_solver(solver_path: str, solver_name: str, input_file: Path,
               timeout: int = 5, extra_args: list = None) -> SolverResult:
    cmd = [solver_path] + (extra_args or []) + [str(input_file)]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        elapsed = int((time.monotonic() - start) * 1000)
        stdout, stderr = proc.stdout.strip(), proc.stderr.strip()
        combined = stdout + "\n" + stderr

        # Detect errors in output
        error_lines = []
        for line in combined.splitlines():
            l = line.strip()
            if l.startswith("(error") or "error" in l.lower() and ("line" in l or "column" in l):
                error_lines.append(l[:200])
        has_errors = len(error_lines) > 0

        # Extract answer
        answer = "unknown"
        for line in stdout.splitlines():
            l = line.strip()
            if l == "sat":
                answer = "sat"
                break
            elif l == "unsat":
                answer = "unsat"
                break
            elif l == "unknown":
                answer = "unknown"
                break

        error_msg = error_lines[0] if error_lines else None

        # Determine reliability:
        # An answer is UNRELIABLE if the solver printed errors or exited non-zero
        # This is the key v4 fix: don't trust sat/unsat from a solver that errored
        answer_reliable = True
        if proc.returncode < 0:
            answer = "crash"
            answer_reliable = False
            error_msg = f"signal {-proc.returncode}"
        elif has_errors:
            # Solver printed (error ...) — answer may be garbage
            answer_reliable = False
            if answer in ("sat", "unsat"):
                # Keep the answer string for logging, but mark unreliable
                pass
            else:
                answer = "error"
        elif proc.returncode != 0:
            # Non-zero exit without visible errors — still suspicious
            answer_reliable = False
            if answer not in ("sat", "unsat"):
                answer = "error"

        return SolverResult(
            solver=solver_name, exit_code=proc.returncode,
            answer=answer, answer_reliable=answer_reliable,
            raw_output=combined[:2000], elapsed_ms=elapsed,
            error_msg=error_msg, has_errors=has_errors,
        )
    except subprocess.TimeoutExpired:
        elapsed = int((time.monotonic() - start) * 1000)
        return SolverResult(
            solver=solver_name, exit_code=-1, answer="timeout",
            answer_reliable=False, raw_output="TIMEOUT", elapsed_ms=elapsed,
            error_msg=f"timeout after {timeout}s", has_errors=False,
        )


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
    content = crash_file.read_text()
    lines = content.splitlines(keepends=True)

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
    tmp = crash_file.parent / f"_min_tmp.smt2"
    if tmp.exists():
        tmp.unlink()
    return output_file


# ═══════════════════════════════════════════════════════════════════════
#  SOUNDNESS VALIDATION — confirm candidates aren't false positives
# ═══════════════════════════════════════════════════════════════════════

def validate_soundness_candidate(z3_path, cvc5_path, input_file: Path,
                                  timeout: int, z3_args, cvc5_args,
                                  z3r: SolverResult, cvc5r: SolverResult) -> tuple:
    """
    Re-check a soundness candidate. Returns (is_genuine, reason).

    Checks:
    1. Either solver had errors → false positive
    2. Either solver exited non-zero → false positive
    3. Re-run both solvers and check consistency
    4. Content contains logic-violating constructs → false positive
    """
    # Check 1: error output
    if z3r.has_errors:
        return False, f"Z3 printed errors: {z3r.error_msg}"
    if cvc5r.has_errors:
        return False, f"CVC5 printed errors: {cvc5r.error_msg}"

    # Check 2: non-zero exit
    if z3r.exit_code != 0:
        return False, f"Z3 exit code {z3r.exit_code}"
    if cvc5r.exit_code != 0:
        return False, f"CVC5 exit code {cvc5r.exit_code}"

    # Check 3: logic-content consistency
    content = input_file.read_text()
    lmeta = parse_logic(content)

    # Quantifiers in QF logic?
    if lmeta["is_qf"] and re.search(r'\b(forall|exists)\b', content):
        return False, f"Quantifiers in QF logic ({lmeta['name']})"

    # define-fun-rec in logic that might not support it?
    if "define-fun-rec" in content and lmeta["is_qf"]:
        return False, f"define-fun-rec in QF logic ({lmeta['name']})"

    # Arrays in non-array logic?
    if "(Array " in content and not lmeta["has_arrays"]:
        return False, f"Array ops in non-array logic ({lmeta['name']})"

    # Check 4: re-run for consistency (3 times each)
    z3_answers = []
    cvc5_answers = []
    for _ in range(3):
        rz = run_solver(z3_path, "z3", input_file, timeout, z3_args)
        rc = run_solver(cvc5_path, "cvc5", input_file, timeout, cvc5_args)
        if rz.has_errors or rc.has_errors:
            return False, "Errors on re-run"
        if rz.exit_code != 0 or rc.exit_code != 0:
            return False, "Non-zero exit on re-run"
        z3_answers.append(rz.answer)
        cvc5_answers.append(rc.answer)

    # All Z3 runs must agree, all CVC5 runs must agree
    if len(set(z3_answers)) > 1:
        return False, f"Z3 non-deterministic: {z3_answers}"
    if len(set(cvc5_answers)) > 1:
        return False, f"CVC5 non-deterministic: {cvc5_answers}"

    # Must still disagree
    if z3_answers[0] == cvc5_answers[0]:
        return False, f"Resolves on re-run: both say {z3_answers[0]}"

    if {z3_answers[0], cvc5_answers[0]} == {"sat", "unsat"}:
        return True, f"CONFIRMED: Z3={z3_answers[0]}, CVC5={cvc5_answers[0]} across 3 runs"

    return False, f"Disagreement is {z3_answers[0]} vs {cvc5_answers[0]}, not sat/unsat"


# ═══════════════════════════════════════════════════════════════════════
#  CLASSIFICATION — error-aware
# ═══════════════════════════════════════════════════════════════════════

def classify_diff(z3r: SolverResult, cvc5r: SolverResult):
    """
    Classify the differential result. KEY CHANGE from v3:
    If either solver's answer is unreliable (errors, non-zero exit),
    we do NOT report sat-vs-unsat as a soundness bug.
    """
    a1, a2 = z3r.answer, cvc5r.answer
    r1, r2 = z3r.answer_reliable, cvc5r.answer_reliable

    # ── Both agree ──
    if a1 == a2:
        if a1 == "sat":     return "agree_sat", "info", ""
        if a1 == "unsat":   return "agree_unsat", "info", ""
        if a1 == "timeout": return "both_timeout", "info", ""
        if a1 == "crash":   return "both_crash", "high", "Both solvers crashed"
        if a1 == "error":   return "both_error", "low", ""
        return "agree_unknown", "info", ""

    # ── Crashes ──
    if a1 == "crash" and a2 != "crash":
        return "z3_crash", "critical", f"Z3 crashed: {z3r.error_msg}"
    if a2 == "crash" and a1 != "crash":
        return "cvc5_crash", "critical", f"CVC5 crashed: {cvc5r.error_msg}"

    # ── sat vs unsat — THE CRITICAL PATH ──
    if {a1, a2} & {"sat", "unsat"} == {a1, a2} and a1 != a2:
        # Both said sat or unsat, but they disagree
        if not r1 and not r2:
            return "both_unreliable", "low", f"Z3={a1} (unreliable), CVC5={a2} (unreliable)"
        if not r1:
            return "z3_unreliable_disagree", "medium", \
                f"Z3={a1} (UNRELIABLE: {z3r.error_msg}), CVC5={a2}"
        if not r2:
            return "cvc5_unreliable_disagree", "medium", \
                f"CVC5={a2} (UNRELIABLE: {cvc5r.error_msg}), Z3={a1}"
        # Both reliable and they disagree on sat/unsat → candidate soundness bug
        return "soundness_candidate", "critical", \
            f"Z3={a1}, CVC5={a2} — POTENTIAL SOUNDNESS BUG (needs validation)"

    # ── One errored ──
    if a1 == "error" and a2 not in ("error", "crash"):
        return "z3_error", "info", f"Z3 error but CVC5={a2}: {z3r.error_msg}"
    if a2 == "error" and a1 not in ("error", "crash"):
        return "cvc5_error", "info", f"CVC5 error but Z3={a1}: {cvc5r.error_msg}"

    # ── One knows, one doesn't ──
    if a1 in ("sat", "unsat") and a2 in ("timeout", "unknown"):
        return "disagree_answer", "low", f"Z3={a1} CVC5={a2}"
    if a2 in ("sat", "unsat") and a1 in ("timeout", "unknown"):
        return "disagree_answer", "low", f"CVC5={a2} Z3={a1}"

    return "disagree_other", "low", f"Z3={a1}, CVC5={a2}"


# ═══════════════════════════════════════════════════════════════════════
#  SEED PREPARATION
# ═══════════════════════════════════════════════════════════════════════

def prepare_seed(content: str) -> str:
    """Clean up seed content for fuzzing."""
    lines = content.splitlines(keepends=True)
    # Strip leading comments
    while lines and lines[0].strip().startswith(";"):
        lines = lines[1:]
    content = "".join(lines)
    # Ensure check-sat
    if "(check-sat)" not in content:
        content = content.rstrip() + "\n(check-sat)\n"
    # Remove commands that cause false positives
    for cmd in ["(get-unsat-core)", "(get-proof)", "(get-model)",
                "(set-option :produce-proofs true)",
                "(set-option :produce-unsat-cores true)",
                "(set-option :produce-models true)"]:
        content = content.replace(cmd, "")
    return content.strip() + "\n"


# ═══════════════════════════════════════════════════════════════════════
#  MAIN FUZZER LOOP
# ═══════════════════════════════════════════════════════════════════════

def run_fuzz_campaign(
    seed_dir: Path, z3_path: str, cvc5_path: str, output_dir: Path,
    rounds: int = 10000, timeout: int = 5,
    gen_ratio: float = 0.3,
    z3_args: list = None, cvc5_args: list = None,
):
    output_dir.mkdir(parents=True, exist_ok=True)
    mutants_dir = output_dir / "mutants"
    mutants_dir.mkdir(exist_ok=True)
    interesting_dir = output_dir / "interesting"
    interesting_dir.mkdir(exist_ok=True)
    minimized_dir = output_dir / "minimized"
    minimized_dir.mkdir(exist_ok=True)
    confirmed_dir = output_dir / "confirmed_soundness"
    confirmed_dir.mkdir(exist_ok=True)

    # Load seeds
    seeds = []
    for ext in ["*.smt_in", "*.smt2", "*.smt"]:
        seeds.extend(seed_dir.glob(ext))

    prepared_seeds = {}
    for sf in seeds:
        raw = sf.read_text(encoding="utf-8", errors="replace")
        prepared_seeds[sf.name] = prepare_seed(raw)

    print(f"[*] SMT Differential Fuzzer v4 (error-aware)")
    print(f"[*] Seeds: {len(seeds)}  Rounds: {rounds}  Timeout: {timeout}s")
    print(f"[*] Gen ratio: {gen_ratio:.0%} generated, {1-gen_ratio:.0%} mutated")
    print(f"[*] Z3:   {z3_path}")
    print(f"[*] CVC5: {cvc5_path}")
    print(f"[*] Output: {output_dir}")
    print()

    stats = {
        "total": 0, "deduped": 0, "generated": 0, "mutated": 0,
        "agree_sat": 0, "agree_unsat": 0, "agree_unknown": 0,
        "soundness_candidate": 0, "soundness_confirmed": 0,
        "soundness_false_positive": 0,
        "z3_crash": 0, "cvc5_crash": 0, "both_crash": 0,
        "z3_error": 0, "cvc5_error": 0, "both_error": 0,
        "z3_unreliable_disagree": 0, "cvc5_unreliable_disagree": 0,
        "both_unreliable": 0,
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

        # ── Quick CVC5 pre-check: skip inputs CVC5 rejects immediately ──
        precheck = run_solver(cvc5_path, "cvc5", mutant_path, timeout=1, extra_args=cvc5_args or [])
        if precheck.has_errors and precheck.elapsed_ms < 500:
            stats["precheck_rejected"] = stats.get("precheck_rejected", 0) + 1
            if mutant_path.exists():
                mutant_path.unlink()
            continue

        z3r, cvc5r = run_solvers_parallel(z3_path, cvc5_path, mutant_path, timeout,
                                           z3_args or [], cvc5_args or [])
        category, severity, notes = classify_diff(z3r, cvc5r)

        stats["total"] += 1
        stats[category] = stats.get(category, 0) + 1

        elapsed = time.monotonic() - start_time
        rate = stats["total"] / elapsed if elapsed > 0 else 0

        # ── Handle soundness candidates: validate before reporting ──
        if category == "soundness_candidate":
            print(f"  [{i+1:5d}/{rounds}] *** SOUNDNESS CANDIDATE *** "
                  f"Z3={z3r.answer} CVC5={cvc5r.answer} [{source}] — validating...")
            genuine, reason = validate_soundness_candidate(
                z3_path, cvc5_path, mutant_path, timeout,
                z3_args or [], cvc5_args or [], z3r, cvc5r)
            if genuine:
                stats["soundness_confirmed"] += 1
                severity = "critical"
                notes = f"CONFIRMED SOUNDNESS BUG: {reason}"
                print(f"           ✓ CONFIRMED! {reason}")
                # Save to confirmed dir
                shutil.copy2(mutant_path, confirmed_dir / f"CONFIRMED_{mutant_id}.smt2")
            else:
                stats["soundness_false_positive"] += 1
                severity = "low"
                category = "soundness_false_positive"
                notes = f"False positive: {reason}"
                print(f"           ✗ False positive: {reason}")

        # Print other interesting results
        elif severity in ("critical", "high"):
            marker = " *** CRITICAL ***" if severity == "critical" else " ** HIGH **"
            print(f"  [{i+1:5d}/{rounds}] {category:20s} "
                  f"Z3={z3r.answer:8s} CVC5={cvc5r.answer:8s} "
                  f"[{source}] ({rate:.1f}/s){marker}")
        elif severity == "medium":
            print(f"  [{i+1:5d}/{rounds}] {category:25s} "
                  f"Z3={z3r.answer:8s} CVC5={cvc5r.answer:8s} "
                  f"[{source}] ({rate:.1f}/s)")
        elif (i+1) % 200 == 0:
            print(f"  [{i+1:5d}/{rounds}] ... ({rate:.1f}/s) "
                  f"sat={stats['agree_sat']} unsat={stats['agree_unsat']} "
                  f"crashes={stats.get('z3_crash',0)+stats.get('cvc5_crash',0)} "
                  f"confirmed={stats.get('soundness_confirmed',0)} "
                  f"fp={stats.get('soundness_false_positive',0)}")

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
                print(f"  {crash_path.name}: {orig_lines} -> {min_lines} lines")
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
    print(f"  SMT DIFFERENTIAL FUZZING v4 REPORT")
    print(f"{'='*60}")
    print(f"  Total tested:     {stats['total']} ({stats['generated']} gen + {stats['mutated']} mut)")
    print(f"  Deduped:          {stats['deduped']}")
    print(f"  Precheck reject:  {stats.get('precheck_rejected', 0)}")
    print(f"  Time:             {total_time:.1f}s")
    print(f"  Throughput:       {stats['total']/total_time:.1f} tests/s" if total_time > 0 else "")
    print()
    print(f"  SOUNDNESS (sat vs unsat):")
    print(f"    Candidates:     {stats.get('soundness_candidate', 0)}")
    print(f"    CONFIRMED:      {stats.get('soundness_confirmed', 0)}  "
          f"{'!!! GENUINE BUG !!!' if stats.get('soundness_confirmed', 0) else '(none)'}")
    print(f"    False positives:{stats.get('soundness_false_positive', 0)}")
    print()
    print(f"  CRASHES:")
    print(f"    Z3 crashes:     {stats.get('z3_crash', 0)}")
    print(f"    CVC5 crashes:   {stats.get('cvc5_crash', 0)}")
    print(f"    Both crash:     {stats.get('both_crash', 0)}")
    print()
    print(f"  ERRORS & DISAGREEMENTS:")
    print(f"    Z3 error:       {stats.get('z3_error', 0)}")
    print(f"    CVC5 error:     {stats.get('cvc5_error', 0)}")
    print(f"    Both error:     {stats.get('both_error', 0)}")
    print(f"    Z3 unreliable:  {stats.get('z3_unreliable_disagree', 0)}")
    print(f"    CVC5 unreliable:{stats.get('cvc5_unreliable_disagree', 0)}")
    print(f"    Disagree (ans): {stats.get('disagree_answer', 0)}")
    print(f"    Disagree (oth): {stats.get('disagree_other', 0)}")
    print()
    print(f"  AGREEMENTS:")
    print(f"    Agree sat:      {stats.get('agree_sat', 0)}")
    print(f"    Agree unsat:    {stats.get('agree_unsat', 0)}")
    print(f"    Agree unknown:  {stats.get('agree_unknown', 0)}")
    print(f"    Both timeout:   {stats.get('both_timeout', 0)}")
    print(f"{'='*60}")
    print(f"  Report:      {output_dir / 'fuzz_report.json'}")
    print(f"  Interesting: {interesting_dir}")
    if stats.get('soundness_confirmed', 0):
        print(f"  CONFIRMED:   {confirmed_dir}")
    if crash_files:
        print(f"  Minimized:   {minimized_dir}")


def main():
    parser = argparse.ArgumentParser(description="SMT Differential Fuzzer v4 (error-aware)")
    parser.add_argument("--seeds", required=True)
    parser.add_argument("--z3", required=True)
    parser.add_argument("--cvc5", required=True)
    parser.add_argument("--rounds", type=int, default=10000)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--gen-ratio", type=float, default=0.3,
                        help="Fraction of rounds using generation vs mutation (default: 0.3)")
    parser.add_argument("--output-dir", default="./smt_fuzz_v4")
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