#!/usr/bin/env python3
"""
CAS verification: enumerate cross-V_j*V_k contributions at deg 7 individually.

Following `verify_d7_cross_terms.py`, the residual after subtracting all
single-V_j perturbations is a 48-term polynomial (LCM 18432). This script
decomposes that residual into individual cross pieces:

  Cross(V_j, V_k) := (bch(x + V_j + V_k, ½a) − bch(x + V_j, ½a)
                     − bch(x + V_k, ½a) + bch(x, ½a))_d7

This captures the MIXED contributions involving both V_j and V_k (bilinear
+ any higher-order in the mixed terms).

At deg 7, the possible cross multisets are:
  • {V_2, V_3}: V_2·V_3 from C_4 (bilinear) + V_2²·V_3 from C_3 (trilinear).
  • {V_2, V_4}: V_2·V_4 from C_3 (bilinear).
(No {V_2, V_5}, {V_3, V_4}, {V_3, V_5}, {V_4, V_5} cross terms at deg 7
since C_2 doesn't admit bilinear substitution and higher C_p needs lower
total V degree.)

The script computes Cross(V_2, V_3) and Cross(V_2, V_4) at deg 7 and
verifies they sum to the residual.
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


def ncpoly_diff(p, q):
    r = ncpoly_zero()
    keys = set(p.keys()) | set(q.keys())
    for w in keys:
        d = sp.nsimplify(p.get(w, 0) - q.get(w, 0))
        if d != 0:
            r[w] = d
    return r


def summarize(p, label):
    n = sum(1 for c in p.values() if c != 0)
    if n == 0:
        print(f"  {label}: 0 non-zero terms (identically zero)")
        return
    LCM = 1
    for c in p.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for c in p.values() if c != 0)
    print(f"  {label}: {n} terms, LCM = {LCM}, Σ|num| = {sum_abs}, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")


def cross(x, Vj, Vk, halfa, mx, target_deg):
    """Compute Cross(V_j, V_k) at target_deg:
    bch(x + V_j + V_k, halfa) - bch(x + V_j, halfa) - bch(x + V_k, halfa)
       + bch(x, halfa), restricted to target_deg."""
    bch_jk = bch_series(ncpoly_add(ncpoly_add(x, Vj), Vk), halfa, mx)
    bch_j = bch_series(ncpoly_add(x, Vj), halfa, mx)
    bch_k = bch_series(ncpoly_add(x, Vk), halfa, mx)
    bch_0 = bch_series(x, halfa, mx)
    result = ncpoly_sub(ncpoly_sub(bch_jk, bch_j), ncpoly_sub(bch_k, bch_0))
    return extract_degree(result, target_deg)


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    bch_inner = bch_series(half_a, b, 7)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)

    # Cross pieces
    cross_23 = cross(x, V2, V3, half_a, 7, 7)
    cross_24 = cross(x, V2, V4, half_a, 7, 7)
    cross_25 = cross(x, V2, V5, half_a, 7, 7)
    cross_34 = cross(x, V3, V4, half_a, 7, 7)
    cross_35 = cross(x, V3, V5, half_a, 7, 7)
    cross_45 = cross(x, V4, V5, half_a, 7, 7)

    print("== Cross pieces at deg 7 ==")
    summarize(cross_23, "Cross(V_2, V_3)")
    summarize(cross_24, "Cross(V_2, V_4)")
    summarize(cross_25, "Cross(V_2, V_5)")
    summarize(cross_34, "Cross(V_3, V_4)")
    summarize(cross_35, "Cross(V_3, V_5)")
    summarize(cross_45, "Cross(V_4, V_5)")

    # Sum
    cross_sum = ncpoly_zero()
    for c in [cross_23, cross_24, cross_25, cross_34, cross_35, cross_45]:
        cross_sum = ncpoly_add(cross_sum, c)
    print()
    summarize(cross_sum, "Sum of all cross pieces")

    # Compare with residual from previous script
    bch_z = bch_series(bch_inner, half_a, 7)
    bch_static = bch_series(x, half_a, 7)
    pert_d7 = extract_degree(ncpoly_sub(bch_z, bch_static), 7)

    V6 = extract_degree(bch_inner, 6)
    V7 = extract_degree(bch_inner, 7)
    P2 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V2), half_a, 7), bch_static), 7)
    P3 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, 7), bch_static), 7)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, 7), bch_static), 7)
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, 7), bch_static), 7)
    P6 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V6), half_a, 7), bch_static), 7)
    P7 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V7), half_a, 7), bch_static), 7)
    P_sum_all = ncpoly_add(ncpoly_add(ncpoly_add(P2, P3), ncpoly_add(P4, P5)), ncpoly_add(P6, P7))
    residual = ncpoly_diff(pert_d7, P_sum_all)
    print()
    summarize(residual, "residual = pert_d7 - (P_2 + ... + P_7)")
    print()
    diff = ncpoly_diff(cross_sum, residual)
    nz = sum(1 for c in diff.values() if c != 0)
    if nz == 0:
        print("✓ VERIFIED: cross_sum = residual")
        print("  Cross pieces ACCOUNT for the entire cross-V_j*V_k contribution at deg 7.")
    else:
        print(f"✗ MISMATCH: cross_sum vs residual differ by {nz} non-zero terms")
        # Could be that we're missing 3-way crosses like Cross(V_2, V_2, V_3) or similar.
        print("  Possibly missing 3-way crosses (V_2·V_2·V_3 etc.) — see below.")

    # Triple cross: V_2 · V_2 · V_3 from C_3 (trilinear)
    # This shows up in cross_23 as the V_2² · V_3 part, captured via bilinear difference?
    # No: cross(V_2, V_3) only catches MIXED V_2·V_3 (one of each). The V_2² · V_3
    # piece, where V_2 appears TWICE in one C_3 word, would actually be captured by
    # cross(V_2, V_3)! Let's see.
    #
    # Actually: bch(x + V_2 + V_3, ½a) − bch(x + V_2, ½a) − bch(x + V_3, ½a) + bch(x, ½a)
    # captures the MIXED-in-V_2-and-V_3 part: those words where at least 1 V_2 AND
    # at least 1 V_3 appear. So V_2² · V_3 IS captured here.
    #
    # So the residual SHOULD equal cross_23 + cross_24 (no other crosses at deg 7).


if __name__ == "__main__":
    main()
