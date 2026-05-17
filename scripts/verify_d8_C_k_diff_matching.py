#!/usr/bin/env python3
"""
CAS verification: structural grouping of the 9 d8_pert sub-pieces by their
C_p origin (the bch_kth_term that contains them).

This documents the joint analysis cancellation structure: in the eventual
discharge of `symmetric_bch_septic_sub_poly_axiom`, each (C_p diff) at deg 8
that appears in Groups F / CD-quintic cancels against a specific subset of
d8_pert sub-pieces.

The grouping by C_p origin (derived from degree counting: for k_j V_j subs in
C_p, total deg = p + Σ k_j·(j-1); for deg 8 with each k_j and p chosen):

  Group_C3 = P_6 + Cross(V_2,V_5) + Cross(V_3,V_4)  (C_3 has 2 z-positions)
    * P_6 = ΔC_3_lin(V_6, x, a')  [k_6=1, k_others=0; Σ k·(j-1) = 5]
    * Cross(V_2,V_5) = ΔC_3_bil(V_2, V_5)  [k_2=1, k_5=1; Σ = 1+4 = 5]
    * Cross(V_3,V_4) = ΔC_3_bil(V_3, V_4)  [k_3=1, k_4=1; Σ = 2+3 = 5]

  Group_C4 = P_5 + Cross(V_2,V_4) + P_3_C4_quad  (C_4 has 2 z-positions)
    * P_5 = ΔC_4_lin(V_5, x, a')  [k_5=1; Σ = 4]
    * Cross(V_2,V_4) = ΔC_4_bil(V_2, V_4)  [k_2=1, k_4=1; Σ = 1+3 = 4]
    * P_3_C4_quad = ΔC_4_quad(V_3, V_3)  [k_3=2; Σ = 2·2 = 4]

  Group_C5 = P_4 + Cross(V_2,V_3) + P_2_C5_cubic  (C_5 has up to 5 z-positions)
    * P_4 = ΔC_5_lin(V_4)  [k_4=1; Σ = 3]
    * Cross(V_2,V_3) = ΔC_5_bil(V_2, V_3)  [k_2=1, k_3=1; Σ = 1+2 = 3]
    * P_2_C5_cubic = ΔC_5_cubic(V_2, V_2, V_2)  [k_2=3; Σ = 3·1 = 3]

  Group_C6 = P_3_C6_lin + P_2_C6_quad  (C_6 has up to 6 z-positions)
    * P_3_C6_lin = ΔC_6_lin(V_3)  [k_3=1; Σ = 2]
    * P_2_C6_quad = ΔC_6_quad(V_2, V_2)  [k_2=2; Σ = 2·1 = 2]

  Group_C7 = P_2_C7_lin  (C_7 has up to 7 z-positions)
    * P_2_C7_lin = ΔC_7_lin(V_2)  [k_2=1; Σ = 1]

Sum of all groups: 3 + 3 + 3 + 2 + 1 = 12 sub-pieces (matching the 9-piece
decomposition expanded into sub-pieces: 9 + 2 (P_3 split into 2) + 3-1 (P_2
split into 3, minus original counts as 1) ... actually 9 - 1 + 2 - 1 + 3 = 12).

This script verifies: Σ Group_Ci = septic_d8_perturbation_poly at the CAS level,
using the previously-extracted sub-piece polynomials (no full bch substitution).
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
        print(f"  {label}: 0 non-zero terms", file=sys.stderr)
        return
    LCM = 1
    for c in p.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for c in p.values() if c != 0)
    print(f"  {label}: {n} terms, LCM = {LCM}, Σ|num| = {sum_abs}, "
          f"Σ|num|/LCM ≈ {sum_abs/LCM:.4f}", file=sys.stderr)


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

    MX = 8
    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)
    V6 = extract_degree(bch_inner, 6)
    V7 = extract_degree(bch_inner, 7)
    V8 = extract_degree(bch_inner, 8)

    print("=== Individual d8_pert sub-pieces ===", file=sys.stderr)

    # 5 Pure Dynkin pieces from session 49
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, MX),
                                    bch_series(x, half_a, MX)), 8)
    P6 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V6), half_a, MX),
                                    bch_series(x, half_a, MX)), 8)
    Cross_V2_V4 = cross(x, V2, V4, half_a, MX, 8)
    Cross_V2_V5 = cross(x, V2, V5, half_a, MX, 8)
    Cross_V3_V4 = cross(x, V3, V4, half_a, MX, 8)
    summarize(P5, "P_5 (ΔC_4_lin(V_5))")
    summarize(P6, "P_6 (ΔC_3_lin(V_6))")
    summarize(Cross_V2_V4, "Cross(V_2,V_4) (ΔC_4_bil)")
    summarize(Cross_V2_V5, "Cross(V_2,V_5) (ΔC_3_bil)")
    summarize(Cross_V3_V4, "Cross(V_3,V_4) (ΔC_3_bil)")

    # P_3 sub-pieces from session 50
    # P_3 = P_3_C4_quad + P_3_C6_lin
    P3_full = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, MX),
                                          bch_series(x, half_a, MX)), 8)
    # P_3_C4_quad = -(1/24)·[a', [V_3, [V_3, a']]] (Dynkin)
    minus_one_24 = sp.Rational(-1, 24)
    bracket_V3_a = ncpoly_bracket(V3, half_a)
    P3_C4_quad = ncpoly_scale(
        ncpoly_bracket(half_a, ncpoly_bracket(V3, bracket_V3_a)),
        minus_one_24
    )
    P3_C6_lin = ncpoly_sub(P3_full, P3_C4_quad)
    summarize(P3_C4_quad, "P_3_C4_quad")
    summarize(P3_C6_lin, "P_3_C6_lin")

    # P_4 piece from session 47 (only 1 sub-piece, non-Dynkin)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, MX),
                                    bch_series(x, half_a, MX)), 8)
    summarize(P4, "P_4 (= septic_d8_P4_poly, ΔC_5_lin(V_4))")

    # Cross(V_2, V_3) piece (non-Dynkin)
    Cross_V2_V3 = cross(x, V2, V3, half_a, MX, 8)
    summarize(Cross_V2_V3, "Cross(V_2,V_3) (ΔC_5_bil)")

    # P_2 sub-pieces from session 51 — extracted via bch_kth_term diffs at deg 8.
    # Compute bch_kth_term abstract via substitution.
    def substitute(p, sub_a, sub_b):
        result = ncpoly_zero()
        for word, coef in p.items():
            prod = ncpoly_from_scalar(1)
            for atom in word:
                sub_poly = sub_a if atom == 0 else sub_b
                prod = ncpoly_mul(prod, sub_poly)
            result = ncpoly_add(result, ncpoly_scale(prod, coef))
        return result

    bch_full_to_7 = bch_series(a, b, 7)
    bch_5_abs = extract_degree(bch_full_to_7, 5)
    bch_6_abs = extract_degree(bch_full_to_7, 6)
    bch_7_abs = extract_degree(bch_full_to_7, 7)

    x_plus_V2 = ncpoly_add(x, V2)
    P2_C5_cubic = extract_degree(ncpoly_sub(
        substitute(bch_5_abs, x_plus_V2, half_a),
        substitute(bch_5_abs, x, half_a)), 8)
    P2_C6_quad = extract_degree(ncpoly_sub(
        substitute(bch_6_abs, x_plus_V2, half_a),
        substitute(bch_6_abs, x, half_a)), 8)
    P2_C7_lin = extract_degree(ncpoly_sub(
        substitute(bch_7_abs, x_plus_V2, half_a),
        substitute(bch_7_abs, x, half_a)), 8)
    summarize(P2_C5_cubic, "P_2_C5_cubic")
    summarize(P2_C6_quad, "P_2_C6_quad")
    summarize(P2_C7_lin, "P_2_C7_lin")

    # === Group by C_p origin ===
    print("\n=== Groups by C_p origin ===", file=sys.stderr)
    Group_C3 = ncpoly_add(ncpoly_add(P6, Cross_V2_V5), Cross_V3_V4)
    Group_C4 = ncpoly_add(ncpoly_add(P5, Cross_V2_V4), P3_C4_quad)
    Group_C5 = ncpoly_add(ncpoly_add(P4, Cross_V2_V3), P2_C5_cubic)
    Group_C6 = ncpoly_add(P3_C6_lin, P2_C6_quad)
    Group_C7 = P2_C7_lin
    summarize(Group_C3, "Group_C3 (P_6 + Cross(V_2,V_5) + Cross(V_3,V_4))")
    summarize(Group_C4, "Group_C4 (P_5 + Cross(V_2,V_4) + P_3_C4_quad)")
    summarize(Group_C5, "Group_C5 (P_4 + Cross(V_2,V_3) + P_2_C5_cubic)")
    summarize(Group_C6, "Group_C6 (P_3_C6_lin + P_2_C6_quad)")
    summarize(Group_C7, "Group_C7 (P_2_C7_lin)")

    # === Verify total matches septic_d8_perturbation_poly ===
    print("\n=== Total verification ===", file=sys.stderr)
    total = ncpoly_add(ncpoly_add(ncpoly_add(ncpoly_add(Group_C3, Group_C4),
                                              Group_C5), Group_C6), Group_C7)
    summarize(total, "Sum of all 5 groups")

    bch_static = bch_series(x, half_a, MX)
    bch_full = bch_series(bch_inner, half_a, MX)
    pert_d8 = extract_degree(ncpoly_sub(bch_full, bch_static), 8)
    summarize(pert_d8, "pert_d8 (= bch(z, a') - bch(a'+b, a'))_d8")

    # pert_d8 = -C_8(a'+b, a') by palindromic vanishing (session 47)
    # septic_d8_perturbation_poly = -P_8 - P_7 - C_8_static = pert_d8 - P_8 - P_7
    # And pert_d8 = (full bch diff at d8) = sum of all (C_p diff)_d8 for p ≥ 3
    # The 5 groups above capture the contributions from p = 3, 4, 5, 6, 7.
    # Plus also need P_7 and P_8 contributions (which CANCEL in d8_pert def).

    # septic_d8_perturbation_poly definition:
    #   = pert_d8 + V_8 + ½·[V_7, a']  (from session 47 derivation)
    # where V_8 = bch_octic_term(½a, b) = C_8_inner, ½·[V_7, a'] = P_7
    # So septic_d8_perturbation_poly = pert_d8 - (-P_8 - P_7) = pert_d8 + P_8 + P_7
    # But also pert_d8 = -C_8_static (palindromic), and septic_d8_pert = -P_8 - P_7 - C_8_static
    # = -P_8 - P_7 + pert_d8

    P7 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V7), half_a, MX),
                                    bch_series(x, half_a, MX)), 8)
    P8 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V8), half_a, MX),
                                    bch_series(x, half_a, MX)), 8)
    summarize(P7, "P_7 (in pert_d8 but excluded from d8_pert)")
    summarize(P8, "P_8 (in pert_d8 but excluded from d8_pert)")

    septic_d8_pert = ncpoly_sub(ncpoly_sub(pert_d8, P7), P8)
    summarize(septic_d8_pert, "septic_d8_perturbation_poly (= pert_d8 - P_7 - P_8)")

    diff = ncpoly_diff(total, septic_d8_pert)
    nz = sum(1 for c in diff.values() if c != 0)
    if nz == 0:
        print("\n✓ VERIFIED: Group_C3 + Group_C4 + Group_C5 + Group_C6 + Group_C7", file=sys.stderr)
        print("            = septic_d8_perturbation_poly", file=sys.stderr)
    else:
        print(f"\n✗ MISMATCH: differ by {nz} terms", file=sys.stderr)

    # === Joint analysis cancellation interpretation ===
    print("\n=== Joint analysis cancellation structure (CONCEPTUAL) ===", file=sys.stderr)
    print("In the eventual O(s⁹) joint analysis discharging", file=sys.stderr)
    print("symmetric_bch_septic_sub_poly_axiom:", file=sys.stderr)
    print("", file=sys.stderr)
    print("Each (C_p(z, a') − C_p(a'+b, a')) at deg 8 cancels with the corresponding", file=sys.stderr)
    print("Group_Cp from septic_d8_perturbation_poly:", file=sys.stderr)
    print("", file=sys.stderr)
    print("  (C_3 diff)_d8 ↔ Group_C3 = P_6 + Cross(V_2,V_5) + Cross(V_3,V_4)", file=sys.stderr)
    print("  (C_4 diff)_d8 ↔ Group_C4 = P_5 + Cross(V_2,V_4) + P_3_C4_quad", file=sys.stderr)
    print("  (C_5 diff)_d8 ↔ Group_C5 = P_4 + Cross(V_2,V_3) + P_2_C5_cubic", file=sys.stderr)
    print("  (C_6 diff)_d8 ↔ Group_C6 = P_3_C6_lin + P_2_C6_quad", file=sys.stderr)
    print("  (C_7 diff)_d8 ↔ Group_C7 = P_2_C7_lin", file=sys.stderr)
    print("", file=sys.stderr)
    print("Each (C_p diff)_d8 is bounded by `norm_bch_kth_term_diff_le` for", file=sys.stderr)
    print("the appropriate k = p (sessions 27-28 provide these for k=5,6,7,8).", file=sys.stderr)
    print("After cancellation, the residual is the deg-(8+1)+ contributions = O(s⁹).", file=sys.stderr)


if __name__ == "__main__":
    main()
