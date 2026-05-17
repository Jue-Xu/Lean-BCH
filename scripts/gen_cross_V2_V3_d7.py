#!/usr/bin/env python3
"""
Generate the explicit polynomial form of the V_2·V_3 cross perturbation at deg 7:
  Cross(V_2, V_3) := (bch(x + V_2 + V_3, ½a) − bch(x + V_2, ½a)
                     − bch(x + V_3, ½a) + bch(x, ½a))_deg7

where x = ½a + b, V_2 = ½·[½a, b], V_3 = bch_cubic_term(½a, b).

This is the MIXED-V_2-and-V_3 part of the perturbation at deg 7: terms where
both V_2 and V_3 appear (at least once each). At deg 7, these come from:
  • Bilinear V_2·V_3 from C_4 (deg 4 + 1 + 2 = 7).
  • Trilinear V_2²·V_3 from C_3 (deg 3 + 1 + 1 + 2 = 7).

Used as one of the 6 pieces in the operator-form Phase B-septic identity
decomposing `septic_d7_perturbation_poly` (see verify_d7_operator_decomp.py).
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple

NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero(): return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c):
    r = ncpoly_zero(); c = sp.sympify(c)
    if c != 0: r[()] = c
    return r


def ncpoly_a():
    r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r


def ncpoly_b():
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
    r = ncpoly_from_scalar(1); xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        r = ncpoly_add(r, ncpoly_scale(xp, sp.Rational(1, sp.factorial(k))))
    return r


def ncpoly_log_one_plus(x, max_degree):
    r = ncpoly_zero(); xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign / sp.Integer(k)))
    return r


def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)
    bch_inner = bch_series(half_a, b, 7)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)

    # Cross(V_2, V_3) at deg 7
    bch_23 = bch_series(ncpoly_add(ncpoly_add(x, V2), V3), half_a, 7)
    bch_2 = bch_series(ncpoly_add(x, V2), half_a, 7)
    bch_3 = bch_series(ncpoly_add(x, V3), half_a, 7)
    bch_0 = bch_series(x, half_a, 7)
    cross = ncpoly_sub(ncpoly_sub(bch_23, bch_2), ncpoly_sub(bch_3, bch_0))
    cross_d7 = extract_degree(cross, 7)

    for w, c in cross_d7.items():
        assert len(w) == 7, f"unexpected degree {len(w)} for word {w}"

    LCM = 1
    for c in cross_d7.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)

    items = sorted([(w, c) for w, c in cross_d7.items() if c != 0],
                   key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)

    print(f"-- {len(items)} terms, LCM = {LCM}, Σ|num| = {sum_abs}")
    print(f"-- Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")
    print()
    print("/-- **Cross V_2·V_3 perturbation at deg 7** (Phase B-septic foundation).")
    print()
    print("`Cross(V_2, V_3) := (bch(x + V_2 + V_3, ½a) − bch(x + V_2, ½a)")
    print("                    − bch(x + V_3, ½a) + bch(x, ½a))_deg7`")
    print()
    print("where x = ½a + b, V_2 = ½·[½a, b], V_3 = bch_cubic_term(½a, b).")
    print()
    print("This is the MIXED-V_2-and-V_3 part of the perturbation at deg 7:")
    print("  • Bilinear V_2·V_3 from C_4 (deg 4 + 1 + 2 = 7).")
    print("  • Trilinear V_2²·V_3 from C_3 (deg 3 + 1 + 1 + 2 = 7).")
    print()
    print(f"CAS-derived; denominator {LCM}, {len(items)} terms, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}.")
    print()
    print("One of 6 pieces in the operator-form Phase B-septic identity decomposing")
    print("`septic_d7_perturbation_poly` (see verify_d7_operator_decomp.py). -/")
    print()
    print("-- LHS placeholder (mixed-difference form; explicit poly form below):")
    print("-- Cross(V_2, V_3) = bch(x+V_2+V_3, ½a) - bch(x+V_2, ½a) - bch(x+V_3, ½a) + bch(x, ½a)")
    print("--                                                                       restricted to deg 7")
    print()
    print("-- The explicit polynomial form:")
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        print(f"--   ({n} / {LCM} : 𝕂) • ({word_str})")


if __name__ == "__main__":
    main()
