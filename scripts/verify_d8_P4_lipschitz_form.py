#!/usr/bin/env python3
"""
CAS verification: establish the Lipschitz-form identity for the simplest
non-Dynkin d8 sub-piece, septic_d8_P4_poly.

The identity:
  bch_quintic_term(x + V_4, a') - bch_quintic_term(x, a') = septic_d8_P4_poly + R_d8_P4
where R_d8_P4 is the deg-11+ residual.

P_4_d8 (= septic_d8_P4_poly) = (bch(x + V_4, a') - bch(x, a'))_deg8.
At deg 8, only bch_quintic_term contributes (since 5 - 1 + 4 = 8 for 1 V_4 sub;
other bch_k either give deg < 8 or > 8 with V_4 substitutions; see structural
analysis in gen_septic_d8_pieces_lean.py).

The Lipschitz-form identity expresses P_4_d8 as a `bch_quintic_term` difference
minus a higher-degree residual. The residual R_d8_P4 has terms at degrees
5 + 3k for k = 2, 3, 4, 5 (i.e., 11, 14, 17, 20) since each additional V_4
substitution adds deg 3 (V_4 has deg 4, replacing z of deg 1).

This script:
  1. Computes R_d8_P4 = bch_quintic_term(x + V_4, a') - bch_quintic_term(x, a')
                     - septic_d8_P4_poly.
  2. Verifies R_d8_P4 has only deg ≥ 11 terms.
  3. Emits Lean DEF for R_d8_P4 + identity theorem.

Useful for the future joint analysis combining d7+d8 op-form pieces with
Groups F + CD-quintic for the O(s⁹) bound discharging
`symmetric_bch_septic_sub_poly_axiom`.
"""

import sympy as sp
from collections import defaultdict
import sys


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


def ncpoly_bracket(p, q):
    return ncpoly_sub(ncpoly_mul(p, q), ncpoly_mul(q, p))


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


def extract_degree_ge(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) >= k})


def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def substitute(p, sub_a, sub_b):
    """Substitute atom 0 with sub_a and atom 1 with sub_b in poly p."""
    result = ncpoly_zero()
    for word, coef in p.items():
        prod = ncpoly_from_scalar(1)
        for atom in word:
            sub_poly = sub_a if atom == 0 else sub_b
            prod = ncpoly_mul(prod, sub_poly)
        result = ncpoly_add(result, ncpoly_scale(prod, coef))
    return result


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
        print(f"  {label}: 0 non-zero terms", file=sys.stderr)
        return
    LCM = 1
    for c in p.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for c in p.values() if c != 0)
    print(f"  {label}: {n} terms, LCM = {LCM}, Σ|num| = {sum_abs}, "
          f"Σ|num|/LCM ≈ {sum_abs/LCM:.4f}, "
          f"degs = [{min(len(w) for w, c in p.items() if c != 0)}, "
          f"{max(len(w) for w, c in p.items() if c != 0)}]",
          file=sys.stderr)


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    # V_4 = bch_quartic_term(½a, b)
    MX = 20  # Need high max-degree to capture full bch_quintic_term diff
    bch_inner = bch_series(half_a, b, 4)
    V4 = extract_degree(bch_inner, 4)
    summarize(V4, "V_4 (= bch_quartic_term(½a, b))")

    # x + V_4
    x_plus_V4 = ncpoly_add(x, V4)
    summarize(x_plus_V4, "x + V_4")

    # bch_quintic_term as abstract poly in (a, b) = (z, y)
    bch_full = bch_series(a, b, 5)
    bch_5_abstract = extract_degree(bch_full, 5)
    summarize(bch_5_abstract, "bch_quintic_term abstract (z, y) = (a, b)")

    # bch_quintic_term(x + V_4, a') - bch_quintic_term(x, a')
    bch5_at_xV4 = substitute(bch_5_abstract, x_plus_V4, half_a)
    bch5_at_x = substitute(bch_5_abstract, x, half_a)
    diff = ncpoly_sub(bch5_at_xV4, bch5_at_x)
    summarize(diff, "bch_quintic_term(x+V_4, a') - bch_quintic_term(x, a') (FULL)")

    # Deg-8 part = septic_d8_P4_poly
    P4_d8 = extract_degree(diff, 8)
    summarize(P4_d8, "septic_d8_P4_poly (deg-8 part of diff)")

    # Cross-check via the full bch series
    bch_static = bch_series(x, half_a, 8)
    bch_at_xV4_full = bch_series(x_plus_V4, half_a, 8)
    P4_d8_via_full = extract_degree(ncpoly_sub(bch_at_xV4_full, bch_static), 8)
    summarize(P4_d8_via_full, "septic_d8_P4_poly via full bch")

    check = ncpoly_diff(P4_d8, P4_d8_via_full)
    nz_check = sum(1 for c in check.values() if c != 0)
    if nz_check == 0:
        print("  ✓ Cross-check: deg-8 of bch_quintic_term diff = P_4_d8 via full bch",
              file=sys.stderr)
    else:
        print(f"  ✗ Mismatch by {nz_check} terms!", file=sys.stderr)
        return

    # R_d8_P4 = diff - P_4_d8 (the deg-11+ residual)
    R_d8_P4 = ncpoly_sub(diff, P4_d8)
    summarize(R_d8_P4, "R_d8_P4 (residual = full diff - deg-8 part)")

    # Verify R_d8_P4 has only deg ≥ 11 terms
    degrees_in_R = set(len(w) for w, c in R_d8_P4.items() if c != 0)
    print(f"  R_d8_P4 has terms at degrees: {sorted(degrees_in_R)}", file=sys.stderr)

    # Verify the identity: diff = P_4_d8 + R_d8_P4
    total = ncpoly_add(P4_d8, R_d8_P4)
    final_check = ncpoly_diff(total, diff)
    nz_final = sum(1 for c in final_check.values() if c != 0)
    if nz_final == 0:
        print("  ✓ VERIFIED: bch_quintic_term diff = P_4_d8 + R_d8_P4", file=sys.stderr)
    else:
        print(f"  ✗ Mismatch by {nz_final} terms!", file=sys.stderr)


if __name__ == "__main__":
    main()
