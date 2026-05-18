#!/usr/bin/env python3
"""
CAS verification: structural grouping of the 8 d7_pert sub-pieces by their
C_p origin (the bch_kth_term that contains them).

d7 analog of `verify_d8_C_k_diff_matching.py` (session 52). Documents the
joint analysis cancellation structure for the deg-7 part of the perturbation
polynomial.

The grouping by C_p origin (derived from degree counting: for k_j V_j subs in
C_p, total deg = p + Σ k_j·(j-1); for deg 7 with each k_j and p chosen):

  Group_C3_d7 = P_5 + Cross(V_2,V_4) + P_3_C3_quad   (C_3 has 2 z-positions)
    * P_5 = ΔC_3_lin(V_5, x, a')           [k_5=1; Σ k·(j-1) = 4]
    * Cross(V_2,V_4) = ΔC_3_bil(V_2, V_4)  [k_2=1, k_4=1; Σ = 1+3 = 4]
    * P_3_C3_quad = ΔC_3_quad(V_3, V_3)    [k_3=2; Σ = 2·2 = 4]

  Group_C4_d7 = P_4 + Cross(V_2,V_3)                  (C_4 has 2 z-positions)
    * P_4 = ΔC_4_lin(V_4)                  [k_4=1; Σ = 3]
    * Cross(V_2,V_3) = ΔC_4_bil(V_2, V_3)  [k_2=1, k_3=1; Σ = 1+2 = 3]

  Group_C5_d7 = P_3_C5_lin + P_2_C5_quad             (C_5 has up to 5 z-positions)
    * P_3_C5_lin = ΔC_5_lin(V_3)            [k_3=1; Σ = 2]
    * P_2_C5_quad = ΔC_5_quad(V_2, V_2)     [k_2=2; Σ = 2·1 = 2]

  Group_C6_d7 = P_2_C6_lin                            (C_6 has up to 6 z-positions)
    * P_2_C6_lin = ΔC_6_lin(V_2)            [k_2=1; Σ = 1]

Total: 3 + 2 + 2 + 1 = 8 sub-pieces (matching the 6-piece d7 decomposition
of session 44 expanded into sub-pieces: P_2 → 2 sub-pieces, P_3 → 2 sub-pieces,
4 other pieces stay as is → 6 + 2 = 8).

Note: this corrects a typo in session 52's docstring which placed P_3_C3_quad
in Group_C4 instead of Group_C3. The degree counting confirms p=3 origin
(C_3 quadratic in V_3 with k_3=2 gives p + Σ = 3 + 4 = 7).

This script verifies: Σ Group_Ci = septic_d7_perturbation_poly at the CAS level.
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

    MX = 7
    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)
    V6 = extract_degree(bch_inner, 6)
    V7 = extract_degree(bch_inner, 7)

    print("=== Individual d7_pert sub-pieces ===", file=sys.stderr)

    # 4 Pure Dynkin pieces from session 45 (P_4, P_5, Cross_V2_V3, Cross_V2_V4)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, MX),
                                    bch_series(x, half_a, MX)), 7)
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, MX),
                                    bch_series(x, half_a, MX)), 7)
    Cross_V2_V3 = cross(x, V2, V3, half_a, MX, 7)
    Cross_V2_V4 = cross(x, V2, V4, half_a, MX, 7)
    summarize(P4, "P_4 (ΔC_4_lin(V_4))")
    summarize(P5, "P_5 (ΔC_3_lin(V_5))")
    summarize(Cross_V2_V3, "Cross(V_2,V_3) (ΔC_4_bil)")
    summarize(Cross_V2_V4, "Cross(V_2,V_4) (ΔC_3_bil)")

    # P_3 sub-pieces from session 46
    # P_3 = P_3_C3_quad + P_3_C5_lin
    P3_full = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, MX),
                                          bch_series(x, half_a, MX)), 7)
    # P_3_C3_quad = (1/12)·[V_3, [V_3, a']] (Dynkin from C_3)
    one_12 = sp.Rational(1, 12)
    bracket_V3_a = ncpoly_bracket(V3, half_a)
    P3_C3_quad = ncpoly_scale(
        ncpoly_bracket(V3, bracket_V3_a),
        one_12
    )
    P3_C5_lin = ncpoly_sub(P3_full, P3_C3_quad)
    summarize(P3_C3_quad, "P_3_C3_quad (= (1/12)·[V_3,[V_3,a']])")
    summarize(P3_C5_lin, "P_3_C5_lin")

    # P_2 sub-pieces from session 46
    # P_2 = P_2_C5_quad + P_2_C6_lin
    # Extract directly via bch_kth_term diffs at deg 7
    def substitute(p, sub_a, sub_b):
        result = ncpoly_zero()
        for word, coef in p.items():
            prod = ncpoly_from_scalar(1)
            for atom in word:
                sub_poly = sub_a if atom == 0 else sub_b
                prod = ncpoly_mul(prod, sub_poly)
            result = ncpoly_add(result, ncpoly_scale(prod, coef))
        return result

    bch_full_to_6 = bch_series(a, b, 6)
    bch_5_abs = extract_degree(bch_full_to_6, 5)
    bch_6_abs = extract_degree(bch_full_to_6, 6)

    x_plus_V2 = ncpoly_add(x, V2)
    # Sanity-check definitions: the C_5 quadratic-in-V_2 piece comes from
    # the half-sum (even part), the C_6 linear-in-V_2 from the half-diff
    # (odd part), per session 46's CAS trick. But for the matching grouping
    # we can just extract at deg 7 from bch_5 and bch_6 substitutions:
    P2_C5_quad = extract_degree(ncpoly_sub(
        substitute(bch_5_abs, x_plus_V2, half_a),
        substitute(bch_5_abs, x, half_a)), 7)
    P2_C6_lin = extract_degree(ncpoly_sub(
        substitute(bch_6_abs, x_plus_V2, half_a),
        substitute(bch_6_abs, x, half_a)), 7)
    summarize(P2_C5_quad, "P_2_C5_quad")
    summarize(P2_C6_lin, "P_2_C6_lin")

    # === Group by C_p origin ===
    print("\n=== Groups by C_p origin ===", file=sys.stderr)
    Group_C3 = ncpoly_add(ncpoly_add(P5, Cross_V2_V4), P3_C3_quad)
    Group_C4 = ncpoly_add(P4, Cross_V2_V3)
    Group_C5 = ncpoly_add(P3_C5_lin, P2_C5_quad)
    Group_C6 = P2_C6_lin
    summarize(Group_C3, "Group_C3 (P_5 + Cross(V_2,V_4) + P_3_C3_quad)")
    summarize(Group_C4, "Group_C4 (P_4 + Cross(V_2,V_3))")
    summarize(Group_C5, "Group_C5 (P_3_C5_lin + P_2_C5_quad)")
    summarize(Group_C6, "Group_C6 (P_2_C6_lin)")

    # === Verify total matches septic_d7_perturbation_poly ===
    print("\n=== Total verification ===", file=sys.stderr)
    total = ncpoly_add(ncpoly_add(ncpoly_add(Group_C3, Group_C4), Group_C5), Group_C6)
    summarize(total, "Sum of all 4 groups")

    # septic_d7_perturbation_poly = pert_d7 - P_6 (subtracting V_6/C_6_inner contribution)
    # where pert_d7 = bch(z, a') - bch(a'+b, a') at deg 7
    # and P_6 = (bch(x + V_6, a') - bch(x, a'))_d7 = ½·[V_6, ½a]
    bch_static = bch_series(x, half_a, MX)
    bch_full = bch_series(bch_inner, half_a, MX)
    pert_d7 = extract_degree(ncpoly_sub(bch_full, bch_static), 7)
    summarize(pert_d7, "pert_d7 (= bch(z, a') - bch(a'+b, a'))_d7")

    P6 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V6), half_a, MX),
                                    bch_series(x, half_a, MX)), 7)
    summarize(P6, "P_6 (excluded from d7_pert; = ½·[V_6, a'])")
    summarize(V7, "V_7 (= bch_septic_term(½a, b))")

    # septic_d7_perturbation_poly = pert_d7 - V_7 - P_6:
    #   pert_d7 = V_7 + P_6 + Group_C3 + Group_C4 + Group_C5 + Group_C6
    #   (V_7 from the linear z-(a'+b) part, P_6 = ½[V_6, a'] from the
    #    bracket term, no C_7-diff contribution since C_7 diff at deg 7
    #    requires no V_j substitution but C_7(a'+b, a') - C_7(a'+b, a') = 0.)
    septic_d7_pert = ncpoly_sub(ncpoly_sub(pert_d7, P6), V7)
    summarize(septic_d7_pert, "septic_d7_perturbation_poly (= pert_d7 - V_7 - P_6)")

    diff = ncpoly_diff(total, septic_d7_pert)
    nz = sum(1 for c in diff.values() if c != 0)
    if nz == 0:
        print("\n✓ VERIFIED: Group_C3 + Group_C4 + Group_C5 + Group_C6", file=sys.stderr)
        print("            = septic_d7_perturbation_poly", file=sys.stderr)
    else:
        print(f"\n✗ MISMATCH: differ by {nz} terms", file=sys.stderr)
        # Show a few terms of the diff for debugging
        for i, (w, c) in enumerate(diff.items()):
            if i >= 5: break
            print(f"   {w}: {c}", file=sys.stderr)

    # === Joint analysis cancellation interpretation ===
    print("\n=== Joint analysis cancellation structure (CONCEPTUAL) ===", file=sys.stderr)
    print("In the eventual O(s⁹) joint analysis discharging", file=sys.stderr)
    print("symmetric_bch_septic_sub_poly_axiom:", file=sys.stderr)
    print("", file=sys.stderr)
    print("Each (C_p(z, a') − C_p(a'+b, a')) at deg 7 cancels with the corresponding", file=sys.stderr)
    print("Group_Cp from septic_d7_perturbation_poly:", file=sys.stderr)
    print("", file=sys.stderr)
    print("  (C_3 diff)_d7 ↔ Group_C3 = P_5 + Cross(V_2,V_4) + P_3_C3_quad", file=sys.stderr)
    print("  (C_4 diff)_d7 ↔ Group_C4 = P_4 + Cross(V_2,V_3)", file=sys.stderr)
    print("  (C_5 diff)_d7 ↔ Group_C5 = P_3_C5_lin + P_2_C5_quad", file=sys.stderr)
    print("  (C_6 diff)_d7 ↔ Group_C6 = P_2_C6_lin", file=sys.stderr)
    print("", file=sys.stderr)
    print("Each (C_p diff)_d7 is bounded by `norm_bch_kth_term_diff_le` for", file=sys.stderr)
    print("k = p (sessions 27-28 provide these for k=5,6,7).", file=sys.stderr)
    print("After cancellation, the residual is the deg-(7+1)+ contributions = O(s⁸),", file=sys.stderr)
    print("combined with d8's O(s⁹) residual gives the joint O(s⁹) bound", file=sys.stderr)
    print("(via fold s⁸ → s⁷ then group with d7's O(s⁷) joint bound).", file=sys.stderr)


if __name__ == "__main__":
    main()
