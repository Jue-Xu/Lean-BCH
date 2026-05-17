#!/usr/bin/env python3
"""
Generate the explicit polynomial form of ΔC₆_lin(V₂, x, ½a)
= deg-7 linear-in-V₂ part of C₆(x + V₂, ½a) − C₆(x, ½a),
where x = ½a + b and V₂ = ¼·(ab − ba).

This is the deg-7 analog of the quintic Phase B sub-lemmas
(`deltaC3_lin_V3_eq`, `deltaC4_lin_V2_eq`) at one degree higher;
it is the simplest "single ΔC_k operator with single V_i" piece
needed for the future Phase B-septic operator-form identity.

C_6(z, y) is the deg-6 Lie polynomial in {z, y}; substituting
z → x + V₂ and expanding to first order in V₂ gives a deg-7
polynomial in {a, b} (linear-in-V₂ at deg 7; quadratic-in-V₂
would give deg ≥ 8).

Outputs Lean code for:

    set_option maxHeartbeats 16000000 in
    private theorem delta_C6_lin_V2_eq (a b : 𝔸) :
        (<explicit ΔC_6_lin operator form in V₂, x, a'>) =
          <explicit polynomial in {a, b}, deg 7>
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple

NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero():
    return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c):
    r = ncpoly_zero()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_a():
    r = ncpoly_zero()
    r[(0,)] = sp.Integer(1)
    return r


def ncpoly_b():
    r = ncpoly_zero()
    r[(1,)] = sp.Integer(1)
    return r


def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_sub(p, q):
    return ncpoly_add(p, ncpoly_scale(q, -1))


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
    r = ncpoly_from_scalar(1)
    xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        r = ncpoly_add(r, ncpoly_scale(xp, sp.Rational(1, sp.factorial(k))))
    return r


def ncpoly_log_one_plus(x, max_degree):
    r = ncpoly_zero()
    xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign / sp.Integer(k)))
    return r


def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx)
    ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0),
                     {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)
    # V_2 = ½·(½a·b - b·½a) = ¼·(ab - ba)
    V2 = ncpoly_scale(
        ncpoly_sub(ncpoly_mul(half_a, b), ncpoly_mul(b, half_a)), half)

    # Compute C_6(x + V_2, ½a) at deg 7 in {a, b}.
    # C_6(z, y) = extract_degree(bch(z, y), 6). We substitute z = x + V_2.
    # Since V_2 is deg-2, the linear-in-V_2 part at deg 7 in {a, b} is exactly
    # what we want; quadratic-in-V_2 contributes deg ≥ 8.
    # Approach: compute bch(x+V_2, ½a) at MAX = 7, extract deg-7 — this includes
    # contributions from ALL C_k for k = 3..7 (linear-in-V_2 ones at deg 7).
    # To isolate ONLY C_6's contribution, compute the static C_6(x, ½a),
    # substitute z → x + V_2 in C_6 (as a polynomial) directly, and extract deg 7.

    # Step 1: compute the FORMAL C_6 = extract_degree(bch(z, y), 6) — but
    # we want it as a sym polynomial in (z, y), not (a, b).
    # Easiest: compute bch(x, ½a) at MAX = 6 with no V_2 perturbation, then
    # compute bch(x + V_2, ½a) at MAX = 7 — the deg-7 contributions purely from
    # C_6 linearization are NOT cleanly separable from C_5 linearization without
    # symbolic tagging.
    #
    # WORKAROUND: use a tagged 3rd letter c for V_2 (so V_2 has its own
    # alphabet position). Compute bch(x + c·V_2, ½a) where c is a formal scalar.
    # Then the COEFFICIENT of c (at any deg) is the linear-in-V_2 part.

    # Actually V_2 is already a noncommutative POLYNOMIAL in {a, b}, so we can't
    # easily tag it. Let me try a different approach: extract the deg-7 part of
    # the FULL bch(x + V_2, ½a) − bch(x, ½a) — this gives the COMBINED linear
    # contribution from C_k for k = 3..7 at deg 7.
    #
    # This is the deg-7 analog of `gen_delta_C7_lin.py` (which extracts deg-8).

    bch_xV2 = bch_series(ncpoly_add(x, V2), half_a, 7)
    bch_x = bch_series(x, half_a, 7)
    diff = ncpoly_sub(bch_xV2, bch_x)
    diff_d7 = extract_degree(diff, 7)

    # Sanity: all words deg 7.
    for w, c in diff_d7.items():
        assert len(w) == 7, f"unexpected degree {len(w)} for word {w}"

    LCM = 1
    for c in diff_d7.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)

    items = sorted([(w, c) for w, c in diff_d7.items() if c != 0],
                   key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)

    print(f"-- {len(items)} terms, LCM = {LCM}, Σ|num| = {sum_abs}")
    print(f"-- Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")
    print()
    print("/-- **Combined linear-in-V₂ perturbation at deg 7** (Phase B-septic foundation).")
    print()
    print("`(C₃(z, ½a) + C₄(z, ½a) + C₅(z, ½a) + C₆(z, ½a))` at z = (½a+b) + V₂")
    print("minus the same expression at z = ½a+b, restricted to deg 7 in {a, b}.")
    print()
    print("Equivalently: the COMBINED `ΔC_k_lin(V₂, ½a+b, ½a)` for k = 3..6 at degree 7.")
    print()
    print("V₂ = ½·(½a·b − b·½a) = ¼·(a·b − b·a). At deg 7, only the linear-in-V₂")
    print("perturbations of C_k contribute (quadratic-in-V₂ gives deg ≥ 8).")
    print()
    print(f"CAS-derived; denominator {LCM}, {len(items)} terms, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}.")
    print()
    print("Deg-7 analog of the deg-8 `combined_delta_Ck_lin_V2_d8` form")
    print("(`scripts/gen_delta_C7_lin.py`). Foundation for the Phase B-septic")
    print("operator-form identity. -/")
    print()
    print("-- LHS placeholder (operator form pending; explicit poly form below):")
    print("-- (bch(z + V₂, ½a) - bch(z, ½a))_deg7 where z = ½a + b, V₂ = ¼(ab - ba)")
    print()
    print("-- The explicit polynomial form:")
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        print(f"--   ({n} / {LCM} : 𝕂) • ({word_str})")


if __name__ == "__main__":
    main()
