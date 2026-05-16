#!/usr/bin/env python3
"""
Generate the explicit polynomial form of `ΔC₇_lin(V₂, ½a+b, ½a)`
= linear-in-V₂ part of C₇(z, ½a) at z = ½a + b + V₂, where V₂ = ½·[½a, b].

This is the deg-8 analog of `ΔC₅_lin(V₂, x, ½a)` (the 36-monomial polynomial
appearing in `symmetric_bch_quintic_deg6_cancellation_pure_identity`).

Approach: compute (C₇(z, ½a) − C₇(½a+b, ½a))_{deg 8 in {a, b}} where
z = (½a+b) + V₂. At deg 8 with V₂ deg 2, only the linear-in-V₂
contribution survives (quadratic-in-V₂ gives deg 9+).
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
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    half_a_plus_b = ncpoly_add(half_a, b)
    # V_2 = ½·(½a·b - b·½a) = ¼·(ab - ba)
    V2 = ncpoly_scale(
        ncpoly_sub(ncpoly_mul(half_a, b), ncpoly_mul(b, half_a)), half)

    # z_with_V2 = (½a+b) + V_2
    z_with_V2 = ncpoly_add(half_a_plus_b, V2)

    # C_7(z_with_V2, ½a) at deg 8 in {a, b}.
    # C_7(x, y) = degree-7 of bch(x, y). With x = (½a+b) + V_2 (deg 1+2) and y = ½a (deg 1):
    # The bch_series at level 7 has many degrees; we need deg-7-as-Lie-polynomial
    # in (x, y), then degree-8 in {a, b}.
    # OPERATIONAL: substitute x = (½a+b) + V_2 (a multi-degree polynomial), y = ½a,
    # into the FORMAL bch series at large enough max_degree, then extract deg-7-weight Lie content.
    # Easiest: just compute bch(z_with_V2, ½a) at deg 8 in {a, b} and subtract
    # the constant part (which corresponds to V_2 → 0).
    # Note: "linear-in-V_2 at deg 8" is exactly the contribution at deg 8 that vanishes when V_2 = 0.

    # MAX must be high enough to capture the deg-8 contributions but not so high
    # that they're polluted by V_2² (which gives deg 4 + 5 = 9 ≥ 9, so safe at deg 8).
    MAX = 8

    bch_z_V2 = bch_series(z_with_V2, half_a, MAX)
    bch_static = bch_series(half_a_plus_b, half_a, MAX)
    # The deg-8 contribution at deg 8 in {a, b} (since linear-in-V_2 of bch's C_k is
    # contained in this difference at deg 8).
    diff = ncpoly_sub(bch_z_V2, bch_static)
    diff_d8 = extract_degree(diff, 8)

    print(f"-- diff at deg 8: {sum(1 for c in diff_d8.values() if c != 0)} non-zero words")
    # NOTE: this includes ALL deg-8 contributions from C_k(z_with_V2, ½a) - C_k(½a+b, ½a)
    # where V_2 has been substituted in z. It's NOT just ΔC_7_lin — it's the combined
    # linear-in-V_2 perturbations across ALL k = 3..7.

    LCM = 1
    for c in diff_d8.values():
        if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)

    items = sorted([(w, c) for w, c in diff_d8.items() if c != 0], key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    print(f"-- LCM = {LCM}, Σ|num| = {sum_abs}, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")
    print()
    print("/-- **Combined linear-in-V₂ perturbation at deg 8** (Phase C-septic, structural piece).")
    print()
    print("`(C₃(z, ½a) + C₄(z, ½a) + C₅(z, ½a) + C₆(z, ½a) + C₇(z, ½a))` at z = (½a+b) + V₂")
    print("minus the same expression at z = ½a+b, restricted to deg 8 in {a, b}. Equivalently:")
    print("the COMBINED `ΔC_k_lin(V₂, ½a+b, ½a)` for k = 3..7 at degree 8.")
    print()
    print("V₂ = ½·(½a·b − b·½a) = ¼·(a·b − b·a). At deg 8, only the linear-in-V₂")
    print("perturbations of C_k contribute (quadratic-in-V₂ gives deg ≥ 9).")
    print()
    print(f"CAS-derived; denominator {LCM}, {len(items)} terms, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}. -/")
    print("private theorem combined_delta_Ck_lin_V2_d8_eq")
    print("    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]")
    print("    (a b : 𝔸) :")
    print("    -- LHS placeholder: the polynomial form of (bch(z_V2, ½a) − bch(½a+b, ½a))_d8")
    print("    -- where z_V2 = (½a+b) + ¼(ab − ba). Equivalently the linear-in-V_2 perturbation")
    print("    -- of bch's C_k slices at deg 8.")
    print("    (True : Prop) := trivial  -- placeholder; structural form pending")
    print()
    print("-- The explicit polynomial form:")
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        print(f"--   {n}/{LCM} · {word_str}")


if __name__ == "__main__":
    main()
