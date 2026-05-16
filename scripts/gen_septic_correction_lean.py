#!/usr/bin/env python3
"""
Generate Lean code for `symmetric_bch_septic_correction_poly` based on the
discovery output of `discover_septic_alt_form.py`.

Produces:
1. Lean noncomputable def with 117 explicit smul terms.
2. CSV file with (numerator, word) pairs for downstream norm-bound generation.

Usage:
    python3 gen_septic_correction_lean.py > septic_correction_def.lean
    # also writes septic_correction_terms.txt
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple
import sys

NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero() -> NCPoly:
    return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c) -> NCPoly:
    r = ncpoly_zero()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_a() -> NCPoly:
    r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r


def ncpoly_b() -> NCPoly:
    r = ncpoly_zero(); r[(1,)] = sp.Integer(1); return r


def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items(): r[w] = r[w] + c
    for w, c in q.items(): r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0: return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0), {w: c * v for w, v in p.items()})


def ncpoly_sub(p, q): return ncpoly_add(p, ncpoly_scale(q, -1))


def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p, max_degree):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x, max_degree):
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x, max_degree):
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in p.items() if len(w) == k})


def bch_series(x, y, max_degree):
    ex = ncpoly_exp(x, max_degree); ey = ncpoly_exp(y, max_degree)
    prod = ncpoly_truncate(ncpoly_mul(ex, ey), max_degree)
    minus_one = defaultdict(lambda: sp.Integer(0), {w: c for w, c in prod.items() if w != ()})
    return ncpoly_log_one_plus(minus_one, max_degree)


def compute_correction() -> NCPoly:
    MAX = 7
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    half_a_plus_b = ncpoly_add(half_a, b)
    z = bch_series(half_a, b, MAX)
    bch_z_halfa = bch_series(z, half_a, MAX)
    a_plus_b = ncpoly_add(a, b)
    sym_bch_cubic_full = ncpoly_sub(bch_z_halfa, a_plus_b)
    sym_E7 = extract_degree(sym_bch_cubic_full, 7)
    bst_inner = extract_degree(z, 7)
    bch_outer_static = bch_series(half_a_plus_b, half_a, MAX)
    bst_outer = extract_degree(bch_outer_static, 7)
    residual = ncpoly_sub(sym_E7, bst_inner)
    residual = ncpoly_sub(residual, bst_outer)
    return residual


def word_to_lean(w: Tuple[int, ...]) -> str:
    return ' * '.join('a' if x == 0 else 'b' for x in w)


def main():
    correction = compute_correction()
    LCM = 276480
    items = sorted([(w, c) for w, c in correction.items() if c != 0],
                   key=lambda x: x[0])

    # Print Lean def.
    print("/-- **Septic correction polynomial** — the 117-term degree-7 polynomial in")
    print("`{a, b}` that captures `sym_E₇(a, b) − bch_septic_term(½a, b) −")
    print("bch_septic_term(½a+b, ½a)`. CAS-derived; common denominator `276480`.")
    print("Σ|numerators|/276480 = 15688/276480 ≈ 0.0567.")
    print("Deg-9 analog of `symmetric_bch_quintic_correction_poly` at one degree higher. -/")
    print("noncomputable def symmetric_bch_septic_correction_poly (𝕂 : Type*) [RCLike 𝕂]")
    print("    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=")
    for i, (w, c) in enumerate(items):
        num = sp.nsimplify(c * LCM)
        assert num == int(num), f"non-integer numerator {num} for word {w}"
        n = int(num)
        word_str = word_to_lean(w)
        prefix = "    " if i == 0 else "  + "
        print(f"{prefix}({n} / {LCM} : 𝕂) • ({word_str})")

    # Also write CSV for downstream norm-bound generation.
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for w, c in items)
    sys.stderr.write(f"# {len(items)} terms, LCM {LCM}, Σ|num| = {sum_abs}\n")
    with open('/tmp/septic_correction_terms.txt', 'w') as f:
        f.write(f"# {len(items)} terms, LCM={LCM}, sum_abs_numerators={sum_abs}\n")
        for w, c in items:
            n = int(sp.nsimplify(c * LCM))
            f.write(f"{n}\t{''.join('a' if x == 0 else 'b' for x in w)}\n")


if __name__ == "__main__":
    main()
