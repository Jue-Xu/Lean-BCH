#!/usr/bin/env python3
"""
Generate the explicit polynomial form of the combined V_3-only perturbation
at deg 7:
  (bch(x + V_3, ½a) − bch(x, ½a))_deg7  where x = ½a + b
                                              V_3 = bch_cubic_term(½a, b)

V_3 has degree 3 in {a, b}; at deg 7 the contributions come from:
  • Linear-in-V_3 from C_5 (deg 5 + (3-1) = 7).
  • Quadratic-in-V_3 from C_3 (deg 3 + 2·(3-1) = 7).
(Cubic-in-V_3 needs C_1 which has only 1 letter — impossible.)

This is the deg-7 analog of `gen_delta_C6_lin_V2.py` but using V_3 instead
of V_2. One ingredient of the future operator-form Phase B-septic identity
decomposing `septic_d7_perturbation_poly`.

Outputs the explicit polynomial form (rational coefficients with common
denominator) for use in a Lean lemma `delta_lin_V3_d7_eq` or similar.
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple

NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero():
    return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c):
    r = ncpoly_zero()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_a():
    r = ncpoly_zero()
    r[(0,)] = sp.Integer(1)
    return r


def ncpoly_b():
    r = ncpoly_zero()
    r[(1,)] = sp.Integer(1)
    return r


def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_sub(p, q):
    return ncpoly_add(p, ncpoly_scale(q, -1))


def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p, max_degree):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x, max_degree):
    r = ncpoly_from_scalar(1)
    xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        r = ncpoly_add(r, ncpoly_scale(xp, sp.Rational(1, sp.factorial(k))))
    return r


def ncpoly_log_one_plus(x, max_degree):
    r = ncpoly_zero()
    xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign / sp.Integer(k)))
    return r


def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx)
    ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0),
                     {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)
    # V_3 = bch_cubic_term(½a, b) = deg-3 part of bch(½a, b).
    bch_half_a_b = bch_series(half_a, b, 3)
    V3 = extract_degree(bch_half_a_b, 3)

    # Sanity: print V_3 to confirm.
    LCM_V3 = 1
    for c in V3.values():
        if c != 0:
            LCM_V3 = sp.lcm(LCM_V3, sp.denom(sp.nsimplify(c)))
    LCM_V3 = int(LCM_V3)
    sum_abs_V3 = sum(abs(int(sp.nsimplify(c * LCM_V3))) for c in V3.values() if c != 0)
    print(f"-- V_3 = bch_cubic_term(½a, b): {sum(1 for c in V3.values() if c != 0)} terms, "
          f"LCM = {LCM_V3}, Σ|num| = {sum_abs_V3}")

    # Compute (bch(x + V_3, ½a) - bch(x, ½a))_d7.
    # MAX = 7 is enough since V_3 is deg 3 and quadratic-in-V_3 from C_3 is deg 7 (the
    # highest order in V_3 that fits at deg 7); cubic-in-V_3 would be deg 9+.
    MAX = 7
    bch_x_V3 = bch_series(ncpoly_add(x, V3), half_a, MAX)
    bch_x = bch_series(x, half_a, MAX)
    diff = ncpoly_sub(bch_x_V3, bch_x)
    diff_d7 = extract_degree(diff, 7)

    # Sanity: all words deg 7.
    for w, c in diff_d7.items():
        assert len(w) == 7, f"unexpected degree {len(w)} for word {w}"

    LCM = 1
    for c in diff_d7.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)

    items = sorted([(w, c) for w, c in diff_d7.items() if c != 0],
                   key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)

    print(f"-- {len(items)} terms, LCM = {LCM}, Σ|num| = {sum_abs}")
    print(f"-- Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")
    print()
    print("/-- **Combined V_3-only perturbation at deg 7** (Phase B-septic foundation).")
    print()
    print("`(bch(x + V_3, ½a) − bch(x, ½a))_deg7`  where x = ½a + b, V_3 = bch_cubic_term(½a, b).")
    print()
    print("V_3 has deg 3 in {a, b}. At deg 7 the contributions come from:")
    print("  • Linear-in-V_3 from C_5 (deg 5 + (3-1) = 7).")
    print("  • Quadratic-in-V_3 from C_3 (deg 3 + 2·(3-1) = 7).")
    print("(Cubic-in-V_3 from C_1 impossible — only 1 letter in C_1.)")
    print()
    print(f"CAS-derived; denominator {LCM}, {len(items)} terms, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}.")
    print()
    print("Deg-7 analog of `gen_delta_C6_lin_V2.py` but using V_3 instead of V_2.")
    print("One ingredient of the operator-form Phase B-septic identity that")
    print("decomposes `septic_d7_perturbation_poly`. -/")
    print()
    print("-- LHS placeholder (operator form pending; explicit poly form below):")
    print("-- (bch(x + V_3, ½a) - bch(x, ½a))_deg7 where x = ½a + b, V_3 = bch_cubic_term(½a, b)")
    print()
    print("-- The explicit polynomial form:")
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        print(f"--   ({n} / {LCM} : 𝕂) • ({word_str})")


if __name__ == "__main__":
    main()
