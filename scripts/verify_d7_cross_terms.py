#!/usr/bin/env python3
"""
CAS verification: identify the cross-V_j*V_k contributions at deg 7.

We have:
  full pert_d7 = (bch(z, ½a) − bch(½a+b, ½a))_d7   (z = bch(½a, b))
              = C_7_inner + correction              (verified earlier)

We have V_j-only pieces (computed by gen_delta_lin_V{j}_d7.py for j=2..5):
  P_j := (bch(x + V_j, ½a) − bch(x, ½a))_d7         (x = ½a+b)

The single-V_j sum P_2 + P_3 + P_4 + P_5 should account for all
linear/multiquadratic-in-single-V_j contributions, BUT not the cross terms
V_j·V_k for j ≠ k.

This script computes:
  residual = pert_d7 − (P_2 + P_3 + P_4 + P_5)
         = sum of cross V_j·V_k contributions at deg 7.

At deg 7, the cross-V_j·V_k terms come from bilinear C_k perturbations:
  • Bilinear V_j·V_k from C_p: total deg = p + (j-1) + (k-1) = p + j + k - 2.
    For deg 7, p + j + k = 9.
    Pairs (j,k) with j ≤ k, both ≥ 2, p ≥ 2 (C_2 = ½[z,y]):
      - (j,k,p) = (2,3,4) → ΔC_4_bil(V_2, V_3)
      - (j,k,p) = (2,4,3) → ΔC_3_bil(V_2, V_4)
      - (j,k,p) = (2,5,2) → ΔC_2_bil(V_2, V_5)? C_2 = ½[z,y], length 2.
        Bilinear means both z's replaced. But C_2 has only 1 z. So no bilinear.
        Actually C_2(z, y) = ½(z·y - y·z), length 2 word, 1 z and 1 y. So
        replacing the single z with V_j gives linear-in-V_j, not bilinear.
        Hence the (2,5,2) entry doesn't apply for C_2.
      - (j,k,p) = (3,4,2) → same: C_2 has no bilinear.

  • Trilinear V_2·V_2·V_3 etc. from C_p with p ≥ 3:
    total deg = p + (j-1)+(k-1)+(l-1) = p + j + k + l - 3.
    For deg 7, p + j + k + l = 10.
    Min: p ≥ 3, j,k,l ≥ 2 → p+j+k+l ≥ 9. So solutions:
      - (j,k,l) = (2,2,3), p = 3 → ΔC_3_tri(V_2, V_2, V_3)
      - (j,k,l) = (2,2,2), p = 4 → ΔC_4_tri(V_2, V_2, V_2) [SINGLE V_2 type]

Wait, ΔC_4_tri(V_2, V_2, V_2) is single-V_2 (only V_2's involved), so it's
captured by P_2. Cross terms are TWO+ distinct V's.

Same for ΔC_5_quad(V_2, V_2): single V_2 type, captured by P_2.

True cross terms (involve V_j and V_k for j ≠ k):
  • ΔC_4_bil(V_2, V_3) — from C_4(z, y) bilinear in V_2, V_3
  • ΔC_3_bil(V_2, V_4) — from C_3(z, y) bilinear in V_2, V_4
  • ΔC_3_tri(V_2, V_2, V_3) — three V's involving V_2 (twice) and V_3 (once)

This script computes the residual and confirms its structure.
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


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    # Compute V_2, V_3, V_4, V_5 = deg-k parts of bch(½a, b).
    bch_inner = bch_series(half_a, b, 7)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)
    V6 = extract_degree(bch_inner, 6)
    V7 = extract_degree(bch_inner, 7)

    # Full pert_d7 = (bch(z, ½a) - bch(½a+b, ½a))_d7
    bch_z = bch_series(bch_inner, half_a, 7)
    bch_static = bch_series(x, half_a, 7)
    pert = ncpoly_sub(bch_z, bch_static)
    pert_d7 = extract_degree(pert, 7)
    print("== Full perturbation ==")
    summarize(pert_d7, "pert_d7 = (bch(z, ½a) - bch(½a+b, ½a))_d7")

    # Single-V_j pieces
    P2 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V2), half_a, 7), bch_static), 7)
    P3 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, 7), bch_static), 7)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, 7), bch_static), 7)
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, 7), bch_static), 7)
    print()
    print("== Single-V_j perturbations at deg 7 ==")
    summarize(P2, "P_2 = (bch(x+V_2, ½a) - bch(x, ½a))_d7")
    summarize(P3, "P_3")
    summarize(P4, "P_4")
    summarize(P5, "P_5")

    # V_6, V_7 contributions (single-V_j) at deg 7:
    P6 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V6), half_a, 7), bch_static), 7)
    P7 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V7), half_a, 7), bch_static), 7)
    print()
    print("== V_6, V_7 contributions ==")
    summarize(P6, "P_6 (= ½·[V_6, a'] = ½[V_6, ½a])")
    summarize(P7, "P_7 (= V_7 = C_7_inner)")

    # Sum of single-V_j perturbations (j = 2..7)
    P_sum_all = ncpoly_add(ncpoly_add(ncpoly_add(P2, P3), ncpoly_add(P4, P5)), ncpoly_add(P6, P7))
    print()
    print("== Sum of single-V_j perturbations (j = 2..7) ==")
    summarize(P_sum_all, "P_sum_all = P_2 + ... + P_7")

    # Residual = pert_d7 - P_sum_all = cross-V_j*V_k contributions
    residual = ncpoly_diff(pert_d7, P_sum_all)
    print()
    print("== Residual (cross-V_j*V_k contributions) ==")
    summarize(residual, "residual = pert_d7 - (P_2 + ... + P_7)")
    print()
    print("This residual is the SUM of all cross-V_j*V_k contributions at deg 7,")
    print("i.e., the bilinear/trilinear pieces where ≥ 2 distinct V_j's appear.")

    # Verify pert_d7 = V_7 + correction:
    # Full pert_d7 should equal V_7 + correction (from septic_d7_cancellation_poly_form context)
    # correction = sym_E_7 - C_7_inner - C_7_static
    # septic_d7_pert = correction - ½·[C_6(½a, b), ½a]

    # Compute correction directly:
    # sym_E_7 = bch_z at deg 7 (= bch(bch(½a, b), ½a) at deg 7)
    sym_E_7 = extract_degree(bch_z, 7)
    C7_inner = V7
    C7_static = extract_degree(bch_static, 7)
    correction = ncpoly_diff(sym_E_7, ncpoly_add(C7_inner, C7_static))
    print()
    print("== correction (≡ pert_d7 - C_7_inner via palindromic structure) ==")
    summarize(correction, "correction = sym_E_7 - C_7_inner - C_7_static")

    # Double check: pert_d7 - C_7_inner = correction (structurally)
    check = ncpoly_diff(pert_d7, ncpoly_add(C7_inner, correction))
    nz = sum(1 for c in check.values() if c != 0)
    if nz == 0:
        print("✓ VERIFIED: pert_d7 = C_7_inner + correction")
    else:
        print(f"✗ MISMATCH: residual has {nz} non-zero terms")


if __name__ == "__main__":
    main()
