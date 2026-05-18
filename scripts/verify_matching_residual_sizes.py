#!/usr/bin/env python3
"""
CAS sizing study: for each (C_p, sub-piece) matching, compute the deg-(q+1)+
residual size so we can plan the Lean formalization strategy.

For each sub-piece, we have the identity (CAS-verified):

    (C_p(z + V, a') - C_p(z, a')) at deg q  =  sub-piece poly

The Lipschitz residual we need to bound for joint cancellation is:

    R := C_p(z + V, a') - C_p(z, a') - sub-piece poly

R contains only deg-(q+1)+ terms. We want to know |R| (number of terms),
max|num|, LCM, Σ|num|/LCM (which gives ‖R‖ ≤ Σ|num|/LCM · s^(q+1) for s ≤ 1).

This decides whether to:
  (A) Encode each R explicitly as a Lean polynomial DEF + identity (feasible
      if R ≤ ~300 terms).
  (B) Use a Lipschitz-style bound via norm_bch_kth_term_diff_le composed
      with ‖V‖^k bounds (loses the tight constant but doesn't need explicit
      polynomial form).

Sub-pieces considered:
  d=7 single-V substitutions: P_3_C5_lin (V_3), P_2_C6_lin (V_2), P_2_C5_quad (V_2 twice)
  d=8 single-V substitutions: P_3_C6_lin (V_3), P_2_C7_lin (V_2), P_4_C5_lin (V_4),
                              P_2_C6_quad (V_2 twice), P_2_C5_cubic (V_2 thrice),
                              Cross-V₂V₃-C₅-bil
"""

import sympy as sp
from collections import defaultdict
import sys


def ncpoly_zero(): return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c):
    r = ncpoly_zero(); c = sp.sympify(c)
    if c != 0: r[()] = c
    return r


def ncpoly_a(): r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r


def ncpoly_b(): r = ncpoly_zero(); r[(1,)] = sp.Integer(1); return r


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


def extract_ge_degree(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) >= k})


def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
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


def report(p, label, target_deg):
    nonzero = [(w, c) for w, c in p.items() if c != 0]
    n = len(nonzero)
    if n == 0:
        print(f"{label}: EMPTY (residual zero)", file=sys.stderr)
        return
    LCM = 1
    for w, c in nonzero:
        LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for w, c in nonzero)
    max_abs = max(abs(int(sp.nsimplify(c * LCM))) for w, c in nonzero)
    by_deg = defaultdict(int)
    for w, c in nonzero:
        by_deg[len(w)] += 1
    deg_str = ", ".join(f"d{k}:{by_deg[k]}" for k in sorted(by_deg))
    bound = sp.Rational(sum_abs, LCM)
    print(f"{label}: {n} terms ({deg_str}), LCM = {LCM}, "
          f"Σ|num|/LCM ≈ {float(bound):.5f}, ≤ {float(bound):.4f}·s^{target_deg}",
          file=sys.stderr)


def compute_residual(bch_p_abs, x, half_a, V_subs_list, target_deg):
    """Compute C_p(x + Σ V_i, a') - C_p(x, a') - poly(target_deg part), as residual."""
    x_perturbed = x
    for V in V_subs_list:
        x_perturbed = ncpoly_add(x_perturbed, V)
    full = ncpoly_sub(substitute(bch_p_abs, x_perturbed, half_a),
                      substitute(bch_p_abs, x, half_a))
    deg_q = extract_degree(full, target_deg)
    residual = extract_ge_degree(full, target_deg + 1)
    return full, deg_q, residual


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    # Compute V_j for j=2..6
    MX_inner = 6
    bch_inner = bch_series(half_a, b, MX_inner)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)
    V6 = extract_degree(bch_inner, 6)

    # Compute bch_kth_term abstract polynomials (in {a, b}) for k=3..7
    print("=== Absolute bch_kth_term ===", file=sys.stderr)
    bch_to_8 = bch_series(a, b, 8)
    bch_3_abs = extract_degree(bch_to_8, 3)
    bch_4_abs = extract_degree(bch_to_8, 4)
    bch_5_abs = extract_degree(bch_to_8, 5)
    bch_6_abs = extract_degree(bch_to_8, 6)
    bch_7_abs = extract_degree(bch_to_8, 7)
    report(bch_3_abs, "bch_3 (cubic_term)", 3)
    report(bch_4_abs, "bch_4 (quartic_term)", 4)
    report(bch_5_abs, "bch_5 (quintic_term)", 5)
    report(bch_6_abs, "bch_6 (sextic_term)", 6)
    report(bch_7_abs, "bch_7 (septic_term)", 7)

    # ===== d=7 sub-pieces =====
    print("\n=== d=7 single/multi-V matching residuals ===", file=sys.stderr)

    # P_2_C6_lin: C_6 with k=1 V_2 substitution → deg 7
    _, deg7, R = compute_residual(bch_6_abs, x, half_a, [V2], 7)
    report(deg7, "P_2_C6_lin (deg-7 part of C_6 diff with V_2)", 7)
    report(R, "  residual (deg-8+)", 8)

    # P_3_C5_lin: C_5 with k=1 V_3 substitution → deg 7
    # Wait — C_5 has up to 5 z-positions. k=1 V_3 substitution: deg = 5 - 1 + 3 = 7 ✓.
    _, deg7, R = compute_residual(bch_5_abs, x, half_a, [V3], 7)
    report(deg7, "P_3_C5_lin (deg-7 part of C_5 diff with V_3)", 7)
    report(R, "  residual (deg-8+)", 8)

    # P_2_C5_quad: C_5 with k=2 V_2 substitutions → deg 7
    # This is a 2-arg matching: (bch_5(x + V_2, a') + bch_5(x - V_2, a') - 2·bch_5(x, a'))/2 ??
    # Or just: bch_5(x + V_2, a') - bch_5(x, a') with deg-7 contribution from k=2.
    full = ncpoly_sub(substitute(bch_5_abs, ncpoly_add(x, V2), half_a),
                      substitute(bch_5_abs, x, half_a))
    deg7 = extract_degree(full, 7)
    R = extract_ge_degree(full, 8)
    # But this captures both k=1 (deg 5+1=6, but C_5 with V_2: 5-1+2=6, so deg 6,
    # which is not deg 7) and k=2 (deg 5-2+4=7). So only k=2 contributes at deg 7.
    report(deg7, "P_2_C5_quad (deg-7 part of C_5 diff with V_2, k=2)", 7)
    report(R, "  residual (deg-8+)", 8)
    # Note: the deg-6 part is also in `full` but not relevant for d=7.
    deg6 = extract_degree(full, 6)
    report(deg6, "  (deg-6 part — k=1 V_2 in C_5, lower order)", 6)

    # ===== d=8 sub-pieces =====
    print("\n=== d=8 single/multi-V matching residuals ===", file=sys.stderr)

    # P_2_C7_lin: C_7 with k=1 V_2 substitution → deg 8
    _, deg8, R = compute_residual(bch_7_abs, x, half_a, [V2], 8)
    report(deg8, "P_2_C7_lin (deg-8 part of C_7 diff with V_2)", 8)
    report(R, "  residual (deg-9+)", 9)

    # P_3_C6_lin: C_6 with k=1 V_3 substitution → deg 8
    _, deg8, R = compute_residual(bch_6_abs, x, half_a, [V3], 8)
    report(deg8, "P_3_C6_lin (deg-8 part of C_6 diff with V_3)", 8)
    report(R, "  residual (deg-9+)", 9)

    # P_4_C5_lin: C_5 with k=1 V_4 substitution → deg 8
    _, deg8, R = compute_residual(bch_5_abs, x, half_a, [V4], 8)
    report(deg8, "P_4_C5_lin (deg-8 part of C_5 diff with V_4)", 8)
    report(R, "  residual (deg-9+)", 9)

    # P_2_C6_quad: C_6 with k=2 V_2 substitutions → deg 8
    full = ncpoly_sub(substitute(bch_6_abs, ncpoly_add(x, V2), half_a),
                      substitute(bch_6_abs, x, half_a))
    deg8 = extract_degree(full, 8)
    R = extract_ge_degree(full, 9)
    report(deg8, "P_2_C6_quad (deg-8 part of C_6 diff with V_2, k=2)", 8)
    report(R, "  residual (deg-9+)", 9)

    # P_2_C5_cubic: C_5 with k=3 V_2 substitutions → deg 8
    full = ncpoly_sub(substitute(bch_5_abs, ncpoly_add(x, V2), half_a),
                      substitute(bch_5_abs, x, half_a))
    deg8 = extract_degree(full, 8)
    R = extract_ge_degree(full, 9)
    report(deg8, "P_2_C5_cubic (deg-8 part of C_5 diff with V_2, k=3)", 8)
    report(R, "  residual (deg-9+)", 9)

    # Cross_V2_V3_C5_bil: C_5 with k_2=1 V_2 + k_3=1 V_3 → deg 8
    full = ncpoly_sub(
        ncpoly_sub(
            ncpoly_sub(substitute(bch_5_abs, ncpoly_add(ncpoly_add(x, V2), V3), half_a),
                       substitute(bch_5_abs, ncpoly_add(x, V2), half_a)),
            substitute(bch_5_abs, ncpoly_add(x, V3), half_a)),
        ncpoly_scale(substitute(bch_5_abs, x, half_a), -1))
    deg8 = extract_degree(full, 8)
    R = extract_ge_degree(full, 9)
    report(deg8, "Cross_V2_V3_C5 (deg-8 part)", 8)
    report(R, "  residual (deg-9+)", 9)

    # ===== Summary =====
    print("\n=== Lean formalization strategy ===", file=sys.stderr)
    print("Each (C_p diff)_dq has a deg-q matching part (the existing sub-piece poly)", file=sys.stderr)
    print("plus a deg-(q+1)+ residual. The residual sizes determine Lean feasibility:", file=sys.stderr)
    print("  R ≤ ~150 terms: direct polynomial-form Lean DEF + identity + Finset.sum norm bound", file=sys.stderr)
    print("  R 150-400 terms: split into per-deg sub-residuals (each ≤ 124 to fit simp pattern)", file=sys.stderr)
    print("  R > 400 terms: use norm_bch_kth_term_diff_le composed with V-norm bounds (loses constant)", file=sys.stderr)


if __name__ == "__main__":
    main()
