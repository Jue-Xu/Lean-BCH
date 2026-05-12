#!/usr/bin/env python3
"""
Compute `bch_octic_term` — the τ⁸ Taylor coefficient of bch(a, b) =
log(exp(a) · exp(b)) — as an explicit polynomial in 8-letter {a, b} words.

This is the deg-8 analog of `bch_septic_term` (session 27, 126 monomials).
For deg-8: 124 non-zero monomials, LCM 120960, Σ|coef|/LCM = 199/4032 ≈ 0.049.

Building block for stepping-stone 1 (`symmetric_bch_septic_sub_poly_axiom`)
discharge, which mirrors the T2-F7e Phase A-E chain at one degree higher.
The discharge would use `bch_octic_term` in a `nonic_pure_identity`
(deg-8 cancellation) analogous to `septic_pure_identity` (deg-6 cancellation).

Output: Lean-ready `noncomputable def bch_octic_term` with rational
coefficients over LCM = 120960.

Usage:        python3 compute_bch_octic_term.py
Dependencies: sympy
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple
from math import gcd
from functools import reduce


NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero() -> NCPoly:
    return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c) -> NCPoly:
    r = ncpoly_zero()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_a() -> NCPoly:
    r = ncpoly_zero()
    r[(0,)] = sp.Integer(1)
    return r


def ncpoly_b() -> NCPoly:
    r = ncpoly_zero()
    r[(1,)] = sp.Integer(1)
    return r


def ncpoly_add(p, q) -> NCPoly:
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p, c) -> NCPoly:
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_mul(p, q) -> NCPoly:
    r = ncpoly_zero()
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            r[w] = r[w] + c1 * c2
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p, max_degree: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x, max_degree: int) -> NCPoly:
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x, max_degree: int) -> NCPoly:
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


def extract_degree(p: NCPoly, deg: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == deg})


def word_to_lean(w: Tuple[int, ...]) -> str:
    return ' * '.join('a' if x == 0 else 'b' for x in w)


def main():
    print("=" * 70)
    print("bch_octic_term (τ⁸ Taylor coefficient of bch(a, b))")
    print("=" * 70)

    a = ncpoly_a()
    b = ncpoly_b()
    exp_a = ncpoly_exp(a, 8)
    exp_b = ncpoly_exp(b, 8)
    prod = ncpoly_truncate(ncpoly_mul(exp_a, exp_b), 8)
    y = defaultdict(lambda: sp.Integer(0),
                    {w: c for w, c in prod.items() if w != ()})
    bch = ncpoly_log_one_plus(y, 8)
    bch_octic = extract_degree(bch, 8)

    print(f"\nbch_octic_term has {len(bch_octic)} non-zero 8-letter words.")

    denoms = []
    for w, c in bch_octic.items():
        c_simplified = sp.simplify(c)
        if c_simplified != 0:
            denoms.append(sp.fraction(c_simplified)[1])
    if denoms:
        lcm = reduce(lambda x, y: sp.lcm(x, y), denoms)
        print(f"\nLCM of denominators: {lcm}")
    else:
        lcm = 1

    sorted_terms = sorted(bch_octic.items(), key=lambda x: x[0])

    print("\n" + "=" * 70)
    print(f"Lean-ready snippet (with LCM = {lcm}):")
    print("=" * 70)

    print(f"\nnoncomputable def bch_octic_term (𝕂 : Type*) [RCLike 𝕂] {{𝔸 : Type*}}")
    print(f"    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=")

    first = True
    for w, c in sorted_terms:
        c_simplified = sp.simplify(c)
        if c_simplified == 0:
            continue
        num_over_lcm = sp.simplify(c_simplified * lcm)
        if num_over_lcm == int(num_over_lcm):
            num = int(num_over_lcm)
            word_lean = word_to_lean(w)
            prefix = "    " if first else "  + "
            print(f"{prefix}({num} / {lcm} : 𝕂) • ({word_lean})")
            first = False
        else:
            print(f"  WARNING: non-integer numerator for word {w}: {num_over_lcm}")

    total_abs = sum(sp.Abs(c) for c in bch_octic.values())
    print(f"\nSum of |coefs|: {total_abs}")
    print(f"Sum of |coefs| as decimal: {float(total_abs):.6f}")
    print(f"\n[Norm bound: ‖bch_octic_term(a,b)‖ ≤ {float(total_abs):.6f} · s^8 where s = ‖a‖+‖b‖.]")


if __name__ == "__main__":
    main()
