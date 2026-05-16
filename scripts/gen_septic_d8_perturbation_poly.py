#!/usr/bin/env python3
"""
Compute the FULL deg-8 perturbation polynomial:

    septic_d8_perturbation := (bch(z, ½a) − (½a+b+½a) − ½·[z, ½a]
                                − C_3(z,½a) − ... − C_8(z,½a))_{d8}

Actually equivalently:
    septic_d8_perturbation := bch(z, ½a)_d8 − C_8(½a, b) − ½·[C_7(½a, b), ½a]
                              − C_8(½a+b, ½a)
                              = 0 − (C_8 + half_C7_bracket + C_8_static)
                              = −(C_8 + half_C7_bracket + C_8_static).

So septic_d8_perturbation + C_8(½a, b) + ½·[C_7(½a, b), ½a] + C_8(½a+b, ½a) = 0.

This identity will be useful for the future Phase C-septic deg-8 cancellation.
The polynomial form of septic_d8_perturbation can be computed directly as
the negative of the three known polynomial forms.

Output: explicit polynomial for septic_d8_perturbation.
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
    MAX = 8
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    half_a_plus_b = ncpoly_add(half_a, b)

    # z = bch(½a, b) up to deg 8.
    z = bch_series(half_a, b, MAX)
    bch_z_halfa = bch_series(z, half_a, MAX)

    # Sanity: bch(z, ½a) at deg 8 should equal (a+b) at deg 8 + deg-8 of sym_bch_cubic.
    # By palindromic vanishing, deg 8 = 0 for sym_bch_cubic, and (a+b) has no deg-8.
    # So bch(z, ½a)_d8 should be exactly 0.
    bch_d8 = extract_degree(bch_z_halfa, 8)
    nz_bch = sum(1 for c in bch_d8.values() if c != 0)
    print(f"-- Sanity: bch(z, ½a) at deg 8 has {nz_bch} non-zero words (expect 0 by palindromic vanishing)")
    assert nz_bch == 0, "Palindromic vanishing failed at deg 8!"

    # Now compute septic_d8_perturbation = bch(z, ½a)_d8 - C_8(½a, b) - ½·[C_7(½a, b), ½a] - C_8(½a+b, ½a).
    C8_inner = extract_degree(z, 8)
    C7_inner = extract_degree(z, 7)
    bracket = ncpoly_sub(ncpoly_mul(C7_inner, half_a), ncpoly_mul(half_a, C7_inner))
    half_bracket_C7 = ncpoly_scale(bracket, half)
    C8_static = extract_degree(bch_series(half_a_plus_b, half_a, MAX), 8)

    # septic_d8_perturbation = 0 - C8_inner - half_bracket_C7 - C8_static
    sum_pieces = ncpoly_add(C8_inner, half_bracket_C7)
    sum_pieces = ncpoly_add(sum_pieces, C8_static)
    perturbation = ncpoly_scale(sum_pieces, -1)  # negate

    nz_pert = sum(1 for c in perturbation.values() if c != 0)
    print(f"-- septic_d8_perturbation: {nz_pert} non-zero deg-8 words")

    LCM = 1
    for c in perturbation.values():
        if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    items = sorted([(w, c) for w, c in perturbation.items() if c != 0], key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    print(f"-- LCM = {LCM}, Σ|num| = {sum_abs}, Σ|num|/LCM ≈ {sum_abs/LCM:.6f}")

    # ALSO: print the sanity polynomial identity to verify the formula.
    print()
    print("/-! ### Phase C-septic: combined deg-8 perturbation polynomial")
    print()
    print("CAS-derived: bch(z, ½a)_d8 = 0 (palindromic vanishing), so the deg-8")
    print("contributions cancel as a polynomial identity in {a, b}:")
    print()
    print("    C_8(½a, b) + ½·[C_7(½a, b), ½a] + (deg-8 perturbation poly) + C_8(½a+b, ½a) = 0.")
    print()
    print(f"The 'deg-8 perturbation poly' has {nz_pert} non-zero words")
    print(f"(LCM {LCM}, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}). It captures the COMBINED")
    print("perturbation of C_k(z, ½a) for k = 3..7 at deg 8 in {a, b} (linear-in-V_k for")
    print("various k, quadratic-in-V₂, cubic-in-V₂, etc.) -/")
    print()
    print("noncomputable def septic_d8_perturbation_poly (𝕂 : Type*) [RCLike 𝕂]")
    print("    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=")
    first = True
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        prefix = "    " if first else "  + "
        print(f"{prefix}({n} / {LCM} : 𝕂) • ({word_str})")
        first = False


if __name__ == "__main__":
    main()
