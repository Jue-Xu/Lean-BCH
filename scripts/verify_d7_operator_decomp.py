#!/usr/bin/env python3
"""
CAS verification: confirm the operator-form decomposition of
`septic_d7_perturbation_poly`.

Following `verify_d7_cross_decomposition.py`, we established:
  pert_d7 = (bch(z, ½a) - bch(½a+b, ½a))_d7
          = P_2 + P_3 + P_4 + P_5 + P_6 + P_7
            + Cross(V_2, V_3) + Cross(V_2, V_4)

where P_j = (bch(x + V_j, ½a) - bch(x, ½a))_d7 (single-V_j piece) and
Cross(V_j, V_k) is the mixed-difference cross piece.

We also know (from `verify_d7_pert_operator_form.py`):
  pert_d7 = C_7_inner + correction
  septic_d7_perturbation_poly + ½·[C_6(½a, b), ½a] = correction

Since:
  P_7 = V_7 = C_7_inner
  P_6 = ½·[C_6(½a, b), ½a]   (only contribution at deg 7 from V_6 perturbation)

We have:
  septic_d7_perturbation_poly
    = correction - ½·[C_6(½a, b), ½a]
    = (pert_d7 - C_7_inner) - P_6
    = (P_2 + P_3 + P_4 + P_5 + P_6 + Cross(V_2,V_3) + Cross(V_2,V_4)) - P_6
    = P_2 + P_3 + P_4 + P_5 + Cross(V_2, V_3) + Cross(V_2, V_4)

This is the **operator-form Phase B-septic identity (deg 7)**: 6 pieces
sum to septic_d7_perturbation_poly. The 6 pieces are:
  • P_2: V_2-only perturbation (96 terms, LCM 92160)
  • P_3: V_3-only perturbation (108 terms, LCM 276480)
  • P_4: V_4-only perturbation (35 terms, LCM 18432)
  • P_5: V_5-only perturbation (100 terms, LCM 276480)
  • Cross(V_2, V_3) (41 terms, LCM 18432)
  • Cross(V_2, V_4) (30 terms, LCM 9216)

This script verifies the identity holds in CAS.
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
    V6 = extract_degree(bch_inner, 6)

    bch_static = bch_series(x, half_a, 7)
    P2 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V2), half_a, 7), bch_static), 7)
    P3 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, 7), bch_static), 7)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, 7), bch_static), 7)
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, 7), bch_static), 7)
    cross_23 = cross(x, V2, V3, half_a, 7, 7)
    cross_24 = cross(x, V2, V4, half_a, 7, 7)

    # The operator-form decomposition:
    operator_form = ncpoly_zero()
    for piece in [P2, P3, P4, P5, cross_23, cross_24]:
        operator_form = ncpoly_add(operator_form, piece)
    print("== Operator-form decomposition ==")
    print("  septic_d7_perturbation_poly =? P_2 + P_3 + P_4 + P_5 + Cross(V_2,V_3) + Cross(V_2,V_4)")
    print()
    summarize(operator_form, "  Σ (operator-form pieces)")

    # Compare with septic_d7_perturbation_poly = correction - ½·[C_6, ½a]
    # correction = sym_E_7 - C_7_inner - C_7_static
    # ½·[C_6(½a,b), ½a] = P_6 (CAS)
    bch_z = bch_series(bch_inner, half_a, 7)
    sym_E_7 = extract_degree(bch_z, 7)
    C7_inner = extract_degree(bch_inner, 7)
    C7_static = extract_degree(bch_static, 7)
    correction = ncpoly_diff(sym_E_7, ncpoly_add(C7_inner, C7_static))
    P6 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V6), half_a, 7), bch_static), 7)
    d7_pert = ncpoly_diff(correction, P6)
    summarize(d7_pert, "  septic_d7_perturbation_poly = correction - ½·[C_6, ½a]")

    # Check: operator_form == d7_pert
    diff = ncpoly_diff(operator_form, d7_pert)
    nz = sum(1 for c in diff.values() if c != 0)
    print()
    if nz == 0:
        print("✓ VERIFIED: septic_d7_perturbation_poly = P_2 + P_3 + P_4 + P_5")
        print("                                       + Cross(V_2, V_3) + Cross(V_2, V_4)")
        print()
        print("This is the **operator-form Phase B-septic identity (deg 7)**.")
        print("Each piece is CAS-derivable as an explicit polynomial in {a, b}, so the")
        print("identity translates to 6 Lean lemmas (each proved by match_scalars + ring)")
        print("plus a combined identity (summing 6 polynomial forms).")
    else:
        print(f"✗ MISMATCH: differ by {nz} terms")
        for w, c in list(diff.items())[:5]:
            if c != 0:
                word = ''.join('a' if x == 0 else 'b' for x in w)
                print(f"   {sp.nsimplify(c)} · {word}")

    print()
    print("== Summary of pieces (for Lean) ==")
    summarize(P2, "P_2 (V_2-only)")
    summarize(P3, "P_3 (V_3-only)")
    summarize(P4, "P_4 (V_4-only)")
    summarize(P5, "P_5 (V_5-only)")
    summarize(cross_23, "Cross(V_2, V_3)")
    summarize(cross_24, "Cross(V_2, V_4)")


if __name__ == "__main__":
    main()
