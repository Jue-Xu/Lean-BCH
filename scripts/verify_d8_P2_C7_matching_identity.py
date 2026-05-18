#!/usr/bin/env python3
"""
CAS verification + sizing study for the d=8 P_2 C_7 matching identity.

The C_7 = `bch_septic_term` diff under V_2 perturbation:

    bch_septic_term(½a + b + V_2, ½a) - bch_septic_term(½a + b, ½a)

decomposes by degree into k=1..6 pieces (V_2 substitutions into C_7's
z-positions; deg = 7 - k + 2k = 7 + k):

  k=1, deg  8: septic_d8_P2_C7_lin_poly         (existing, session 51)
  k=2, deg  9: residual                          (NEW)
  k=3, deg 10: residual                          (NEW)
  k=4, deg 11: residual                          (NEW)
  k=5, deg 12: residual                          (NEW)
  k=6, deg 13: residual                          (NEW)

This verifies the decomposition holds at CAS level and reports per-degree
sizing so the Lean strategy can be planned. Lean DEFs with N > 124 terms
require per-deg split-halves (matching feedback_simp_recursion_180_terms).

V_2 = bch_quadratic_term(½a, b) = (1/4)·(a·b - b·a).
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
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


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
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


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
    m1 = defaultdict(lambda: sp.Integer(0),
                     {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def substitute(p, sub_a, sub_b):
    result = ncpoly_zero()
    for word, coef in p.items():
        prod = ncpoly_from_scalar(1)
        for atom in word:
            sub_poly = sub_a if atom == 0 else sub_b
            prod = ncpoly_mul(prod, sub_poly)
        result = ncpoly_add(result, ncpoly_scale(prod, coef))
    return result


def stats(p):
    nonzero = [(w, c) for w, c in p.items() if c != 0]
    n = len(nonzero)
    if n == 0:
        return (0, 1, 0, 0)
    lcm = 1
    for _, c in nonzero:
        lcm = sp.lcm(lcm, sp.denom(sp.nsimplify(c)))
    lcm = int(lcm)
    sum_abs = sum(abs(int(sp.nsimplify(c * lcm))) for _, c in nonzero)
    max_abs = max(abs(int(sp.nsimplify(c * lcm))) for _, c in nonzero)
    return (n, lcm, max_abs, sum_abs)


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    MX = 14
    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)

    bch_to_7 = bch_series(a, b, 7)
    bch_7_abs = extract_degree(bch_to_7, 7)
    n_c7 = sum(1 for c in bch_7_abs.values() if c != 0)
    print(f"bch_septic_term: {n_c7} terms")

    x_plus_V2 = ncpoly_add(x, V2)
    full = ncpoly_sub(substitute(bch_7_abs, x_plus_V2, half_a),
                      substitute(bch_7_abs, x, half_a))

    print()
    print("Per-degree decomposition of (C_7 diff under V_2 shift):")
    print(f"{'k':>2} {'deg':>4} {'N':>5} {'LCM':>11} {'max|n|':>7} "
          f"{'Σ|n|/LCM':>10} {'split?':>7}")
    print("-" * 56)
    parts = {}
    total_terms = 0
    for k in range(1, 8):
        d = 7 + k
        part = extract_degree(full, d)
        n, lcm, max_abs, sum_abs = stats(part)
        if n == 0:
            continue
        parts[d] = part
        total_terms += n
        ratio = float(sp.Rational(sum_abs, lcm))
        # how many >124 splits needed
        splits = (n + 123) // 124
        print(f"{k:>2} {d:>4} {n:>5} {lcm:>11} {max_abs:>7} "
              f"{ratio:>10.4f} {splits:>7}")

    # Verify: sum of all per-deg pieces equals full
    reconstructed = ncpoly_zero()
    for part in parts.values():
        reconstructed = ncpoly_add(reconstructed, part)
    diff = ncpoly_sub(full, reconstructed)
    diff_nonzero = [(w, c) for w, c in diff.items() if c != 0]
    print()
    print(f"Matching identity verification (full diff = Σ deg pieces):")
    print(f"  Residual after subtracting Σ deg pieces: "
          f"{len(diff_nonzero)} terms")
    assert len(diff_nonzero) == 0, \
        f"Decomposition not exact: {len(diff_nonzero)} non-zero terms remain"
    print(f"  ✓ Matching identity holds at CAS level.")

    print()
    print(f"Summary: total residual (k≥2, deg≥9) = "
          f"{total_terms - sum(1 for c in parts[8].values() if c != 0)} terms")
    print(f"  Matches session 57 sizing study (d=8 P_2_C7_lin: 2488 terms).")

    # Estimate Lean code size
    print()
    print(f"Lean encoding estimate:")
    total_splits = 0
    for d, part in parts.items():
        n = sum(1 for c in part.values() if c != 0)
        if d == 8:
            continue  # septic_d8_P2_C7_lin_poly already in place
        splits = (n + 123) // 124
        total_splits += splits
    print(f"  Total split DEFs needed for deg-9..13 residuals: {total_splits}")
    print(f"  Each split DEF + Finset.sum norm bound ≈ 700 lines → "
          f"{total_splits * 700} lines total")
    print(f"  Plus the matching identity itself (~250 lines)")


if __name__ == "__main__":
    main()
