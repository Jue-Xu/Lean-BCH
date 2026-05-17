#!/usr/bin/env python3
"""
CAS verification: structural decomposition of septic_d8_perturbation_poly
into operator-form pieces (analog of verify_d7_operator_decomp.py for d8).

We aim to show:

  septic_d8_perturbation_poly = P_2_d8 + P_3_d8 + P_4_d8 + P_5_d8 + P_6_d8
                              + Cross(V_2, V_3)_d8 + Cross(V_2, V_4)_d8
                              + Cross(V_2, V_5)_d8 + Cross(V_3, V_4)_d8

where:
  • P_j_d8 := (bch(x + V_j, ½a) − bch(x, ½a))_deg8  (single-V_j perturbation).
  • Cross(V_j, V_k)_d8 := mixed second-difference at deg 8.

Plus a possible trilinear V_2·V_2·V_2 from C_5 component (captured within
P_2_d8 if we treat it as "V_2-only trilinear").

At deg 8 the contributions are more numerous than at deg 7:
  • V_2-only: linear from C_7, quadratic from C_6, cubic V_2³ from C_5.
  • V_3-only: linear from C_6, quadratic from C_4.
  • V_4-only: linear from C_5.
  • V_5-only: linear from C_4.
  • V_6-only: linear from C_3.
  • Cross V_2·V_3 from C_5 (bilinear).
  • Cross V_2·V_4 from C_4 (bilinear).
  • Cross V_2·V_5 from C_3 (bilinear).
  • Cross V_3·V_4 from C_3 (bilinear).

This script verifies these 9 pieces sum to septic_d8_perturbation_poly.

Setup parallels verify_d7_operator_decomp.py.
"""

import sympy as sp
from collections import defaultdict


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
        print(f"  {label}: 0 non-zero terms")
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

    # MAX=8 for deg-8 extraction
    MX = 8

    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)
    V6 = extract_degree(bch_inner, 6)
    V7 = extract_degree(bch_inner, 7)
    V8 = extract_degree(bch_inner, 8)

    # Static and full bch
    bch_static = bch_series(x, half_a, MX)
    bch_full = bch_series(bch_inner, half_a, MX)
    pert_d8 = extract_degree(ncpoly_sub(bch_full, bch_static), 8)

    print("== Full perturbation pert_d8 = (bch(z, ½a) - bch(½a+b, ½a))_d8 ==")
    summarize(pert_d8, "pert_d8")

    # Single-V_j perturbations P_j_d8
    P2 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V2), half_a, MX), bch_static), 8)
    P3 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, MX), bch_static), 8)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, MX), bch_static), 8)
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, MX), bch_static), 8)
    P6 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V6), half_a, MX), bch_static), 8)
    P7 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V7), half_a, MX), bch_static), 8)
    P8 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V8), half_a, MX), bch_static), 8)

    print()
    print("== Single-V_j perturbations at deg 8 ==")
    summarize(P2, "P_2 (V_2-only)")
    summarize(P3, "P_3 (V_3-only)")
    summarize(P4, "P_4 (V_4-only)")
    summarize(P5, "P_5 (V_5-only)")
    summarize(P6, "P_6 (V_6-only)")
    summarize(P7, "P_7 (V_7-only = ½·[V_7, ½a])")
    summarize(P8, "P_8 (V_8-only = V_8 = C_8_inner)")

    # Cross pieces
    cross_23 = cross(x, V2, V3, half_a, MX, 8)
    cross_24 = cross(x, V2, V4, half_a, MX, 8)
    cross_25 = cross(x, V2, V5, half_a, MX, 8)
    cross_26 = cross(x, V2, V6, half_a, MX, 8)
    cross_34 = cross(x, V3, V4, half_a, MX, 8)
    cross_35 = cross(x, V3, V5, half_a, MX, 8)
    cross_45 = cross(x, V4, V5, half_a, MX, 8)

    print()
    print("== Cross pieces at deg 8 ==")
    summarize(cross_23, "Cross(V_2, V_3)")
    summarize(cross_24, "Cross(V_2, V_4)")
    summarize(cross_25, "Cross(V_2, V_5)")
    summarize(cross_26, "Cross(V_2, V_6)")
    summarize(cross_34, "Cross(V_3, V_4)")
    summarize(cross_35, "Cross(V_3, V_5)")
    summarize(cross_45, "Cross(V_4, V_5)")

    # Sum all single + cross
    total = ncpoly_zero()
    for p in [P2, P3, P4, P5, P6, P7, P8,
              cross_23, cross_24, cross_25, cross_26, cross_34, cross_35, cross_45]:
        total = ncpoly_add(total, p)

    print()
    summarize(total, "Sum of all single-V_j + cross pieces")

    # Residual = pert_d8 - total
    residual = ncpoly_diff(pert_d8, total)
    print()
    summarize(residual, "Residual = pert_d8 - sum")

    nz = sum(1 for c in residual.values() if c != 0)
    if nz == 0:
        print()
        print("✓ VERIFIED: pert_d8 = ΣP_j + ΣCross (no triple cross needed)")
    else:
        print()
        print(f"✗ MISMATCH: residual has {nz} non-zero terms")
        print("  This is the triple-cross residual (V_2·V_2·V_3 etc.).")
        summarize(residual, "  residual details")

    # Now compute septic_d8_perturbation_poly = correction_d8 - "P_8 + P_7 + something"
    # Actually d8_pert is defined as related to symmetric_bch deg-8 cancellation.
    # The Lean theorem septic_d8_cancellation_poly_form says:
    #   d8_pert + C_8(½a, b) + ½·[C_7(½a, b), ½a] + C_8(½a+b, ½a) = 0
    # So d8_pert = -(C_8(½a, b) + ½·[C_7(½a, b), ½a] + C_8(½a+b, ½a))
    # = -(V_8 + P_7 + C_8(a'+b, a'))
    # Hmm let me think about this carefully.

    # Compute C_8_inner = bch_octic_term(½a, b) = deg-8 of bch(½a, b)
    C8_inner = V8
    # Compute C_8_static = bch_octic_term(a'+b, a') = deg-8 of bch(a'+b, a')
    C8_static = extract_degree(bch_static, 8)
    # Compute ½·[V_7, ½a] = P_7 (CAS confirms)
    # septic_d8_perturbation_poly should be -(C_8_inner + P_7 + C_8_static) ?

    # Actually from the cancellation identity:
    #   d8_pert + C_8(½a, b) + ½·[C_7(½a, b), ½a] + C_8(½a+b, ½a) = 0
    # So d8_pert = - C_8(½a, b) - ½·[C_7(½a, b), ½a] - C_8(½a+b, ½a)
    # = -V_8 - ½·[V_7, ½a] - C_8(½a+b, ½a)
    # = -P_8 - P_7 - C_8(½a+b, ½a)
    # Hmm but septic_d8_perturbation_poly should be positive.

    # Let me try another interpretation:
    # pert_d8 = (bch(z, ½a) - bch(½a+b, ½a))_d8 = C_8_inner + (deg-8 of (bch(z,½a) - C_8(z,½a) - bch(½a+b,½a) + C_8(a'+b,a')))
    # Actually the symmetric BCH deg-8 vanishes (palindromic), so all this should sum to 0.

    print()
    print("== Sanity check: sym_E_8 should vanish (palindromic) ==")
    summarize(extract_degree(bch_full, 8), "sym_E_8 (= deg-8 of bch(z, ½a))")

    # The proper structure for d8 from CLAUDE.md / session 42 notes:
    # septic_d8_perturbation_poly is defined so that:
    #   d8_pert + ½·[C_7(½a, b), ½a] + C_8(½a, b) + C_8(½a+b, ½a) = 0
    # i.e., d8_pert = -(P_7 + V_8 + C_8(a'+b, a'))
    # Equivalently: d8_pert = - (pert_d8 + C_8(a'+b, a')) since pert_d8 = (P_2 + ... + P_8 + crosses)
    # Hmm wait that doesn't help. Let me think.

    # Actually pert_d8 = (bch(z, ½a) - bch(½a+b, ½a))_d8.
    # sym_E_8 = (bch(z, ½a))_d8 (since z = bch(½a, b), bch(z, ½a) is sym BCH).
    # sym_E_8 = 0 (palindromic for symmetric BCH).
    # So (bch(z, ½a))_d8 = 0, meaning pert_d8 = -(bch(½a+b, ½a))_d8 = -C_8(a'+b, a').
    # i.e., pert_d8 = -C_8_static.

    print()
    print("== Check: pert_d8 = -C_8(a'+b, a')? ==")
    summarize(extract_degree(bch_static, 8), "C_8_static")
    check = ncpoly_add(pert_d8, C8_static)
    nz_check = sum(1 for c in check.values() if c != 0)
    if nz_check == 0:
        print("✓ CONFIRMED: pert_d8 = -C_8(a'+b, a')")
    else:
        summarize(check, "pert_d8 + C_8_static")
        print(f"  Non-zero: {nz_check}")

    # Derive septic_d8_perturbation_poly's decomposition:
    # From septic_d8_cancellation_poly_form:
    #   d8_pert = -V_8 - ½·[V_7, ½a] - C_8_static = -P_8 - P_7 - C_8_static
    # And pert_d8 = ΣP_j(j=2..8) + Σcrosses = -C_8_static (verified above)
    # So C_8_static = -(ΣP_j + Σcrosses), and:
    # d8_pert = -P_8 - P_7 + (ΣP_j(j=2..8) + Σcrosses)
    #         = P_2 + P_3 + P_4 + P_5 + P_6 + crosses  (since -P_7-P_8 cancels P_7+P_8 in the sum)

    print()
    print("== septic_d8_perturbation_poly = P_2 + P_3 + P_4 + P_5 + P_6 + 4 crosses ==")
    d8_pert_computed = ncpoly_zero()
    for p in [P2, P3, P4, P5, P6, cross_23, cross_24, cross_25, cross_34]:
        d8_pert_computed = ncpoly_add(d8_pert_computed, p)
    summarize(d8_pert_computed, "d8_pert (computed as 5 single + 4 cross)")

    # Verify: d8_pert = -P_8 - P_7 - C_8_static (matches Lean septic_d8_cancellation_poly_form)
    d8_pert_via_cancellation = ncpoly_sub(ncpoly_sub(ncpoly_zero(),
                                                      ncpoly_add(P8, P7)),
                                          C8_static)
    summarize(d8_pert_via_cancellation, "d8_pert (computed as -P_8 - P_7 - C_8_static)")

    check2 = ncpoly_diff(d8_pert_computed, d8_pert_via_cancellation)
    nz2 = sum(1 for c in check2.values() if c != 0)
    if nz2 == 0:
        print()
        print("✓ VERIFIED: septic_d8_perturbation_poly = P_2 + P_3 + P_4 + P_5 + P_6")
        print("                                       + Cross(V_2,V_3) + Cross(V_2,V_4)")
        print("                                       + Cross(V_2,V_5) + Cross(V_3,V_4)")
        print()
        print("This is the d8-analog of the d7 6-piece decomposition. d8 has 9 pieces")
        print("(5 single-V_j + 4 cross), parallel to d7's 6 pieces (4 single + 2 cross).")
    else:
        print(f"✗ MISMATCH: differ by {nz2} terms")


if __name__ == "__main__":
    main()
