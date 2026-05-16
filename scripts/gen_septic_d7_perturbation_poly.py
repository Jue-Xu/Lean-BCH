#!/usr/bin/env python3
"""
Compute the deg-7 perturbation polynomial for the Phase B-septic identity:

  septic_d7_perturbation := correction(a, b) − ½·[C_6(½a, b), ½a]

Equivalently: the combined deg-7 perturbation of C_k(z, ½a) − C_k(½a+b, ½a)
for k = 3..6, where z = bch(½a, b).

From the alt-form:
  sym_E_7 = bst_inner + bst_outer + correction
And by the expansion of bch(z, ½a) at deg 7:
  sym_E_7 = bst_inner + bst_outer + ½·[C_6(½a, b), ½a] + (deg-7 perturbation)
So: correction = ½·[C_6(½a, b), ½a] + septic_d7_perturbation.
Equivalently: septic_d7_perturbation = correction − ½·[C_6(½a, b), ½a].

This is the deg-7 analog of `septic_d8_perturbation_poly`.
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
    MAX = 7
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    half_a_plus_b = ncpoly_add(half_a, b)

    # correction = sym_E_7 − bst_inner − bst_outer (from alt-form).
    z = bch_series(half_a, b, MAX)
    bz = bch_series(z, half_a, MAX)
    sym_E7 = extract_degree(ncpoly_sub(bz, ncpoly_add(a, b)), 7)
    bst_inner = extract_degree(z, 7)
    bst_outer = extract_degree(bch_series(half_a_plus_b, half_a, MAX), 7)
    correction = ncpoly_sub(sym_E7, bst_inner)
    correction = ncpoly_sub(correction, bst_outer)

    # half_C6_bracket = ½·[C_6(½a, b), ½a].
    C6_inner = extract_degree(z, 6)
    bracket = ncpoly_sub(ncpoly_mul(C6_inner, half_a), ncpoly_mul(half_a, C6_inner))
    half_C6_bracket = ncpoly_scale(bracket, half)

    # septic_d7_perturbation = correction − half_C6_bracket.
    perturbation = ncpoly_sub(correction, half_C6_bracket)
    nz_pert = sum(1 for c in perturbation.values() if c != 0)
    print(f"-- septic_d7_perturbation: {nz_pert} non-zero deg-7 words")

    LCM = 1
    for c in perturbation.values():
        if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    items = sorted([(w, c) for w, c in perturbation.items() if c != 0], key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    print(f"-- LCM = {LCM}, Σ|num| = {sum_abs}, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")
    print()
    print("/-! ### Phase B-septic: combined deg-7 perturbation polynomial")
    print()
    print("CAS-derived: from the alt-form `sym_E_7 = bst_inner + bst_outer + correction`")
    print("and the expansion `bch(z, ½a)_d7 = bst_inner + bst_outer + ½·[C_6(½a, b), ½a]")
    print("+ (deg-7 perturbation)`, we get:")
    print()
    print("    correction = ½·[C_6(½a, b), ½a] + septic_d7_perturbation_poly.")
    print()
    print(f"The perturbation poly has {nz_pert} non-zero deg-7 words")
    print(f"(LCM {LCM}, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}). Captures the COMBINED")
    print("perturbation of C_k(z, ½a) − C_k(½a+b, ½a) at deg 7 for k = 3..6")
    print("(linear-in-V_k for various k, plus quadratic-in-V₂, cubic-in-V₂ at lower k). -/")
    print()
    print("noncomputable def septic_d7_perturbation_poly (𝕂 : Type*) [RCLike 𝕂]")
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
