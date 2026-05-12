#!/usr/bin/env python3
"""
Compute `bch_septic_term` — the τ⁷ Taylor coefficient of bch(a, b) =
log(exp(a) · exp(b)) — as an explicit polynomial in 7-letter {a, b} words.

This is the deg-7 analog of `bch_sextic_term` in BCH/Basic.lean (28 monomials).
For deg-7, the polynomial has ~64 non-zero monomials (out of 128 = 2^7).

Building block for stepping-stone 1 (`symmetric_bch_septic_sub_poly_axiom`)
discharge, which mirrors the T2-F7e Phase A-E chain at one degree higher.

The discharge would use `bch_septic_term` in an `octic_pure_identity`
(deg-7 cancellation) analogous to `septic_pure_identity` (deg-6 cancellation).

Output: Lean-ready `noncomputable def bch_septic_term` with rational
coefficients (likely LCM 60480 = 1440 · 42, or similar).

Usage:        python3 compute_bch_septic_term.py
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


def ncpoly_add(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p: NCPoly, c) -> NCPoly:
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_neg(p: NCPoly) -> NCPoly:
    return ncpoly_scale(p, -1)


def ncpoly_sub(p: NCPoly, q: NCPoly) -> NCPoly:
    return ncpoly_add(p, ncpoly_neg(q))


def ncpoly_mul(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            r[w] = r[w] + c1 * c2
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p: NCPoly, max_degree: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x: NCPoly, max_degree: int) -> NCPoly:
    """exp(x) = 1 + x + x²/2 + x³/6 + ... up to max_degree."""
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x: NCPoly, max_degree: int) -> NCPoly:
    """log(1+x) = x - x²/2 + x³/3 - ... up to max_degree."""
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


def extract_degree(p: NCPoly, k: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def word_to_lean(w: Tuple[int, ...]) -> str:
    """Convert a word tuple to a Lean product like 'a * a * b * a * b * a * b'."""
    return ' * '.join('a' if x == 0 else 'b' for x in w)


def main():
    print("=" * 70)
    print("bch_septic_term (τ⁷ Taylor coefficient of bch(a, b))")
    print("=" * 70)

    a = ncpoly_a()
    b = ncpoly_b()

    # bch(a, b) = log(exp(a) · exp(b))
    exp_a = ncpoly_exp(a, 7)
    exp_b = ncpoly_exp(b, 7)
    prod = ncpoly_truncate(ncpoly_mul(exp_a, exp_b), 7)

    # Subtract the constant term (= 1) to get y = exp(a)·exp(b) - 1.
    y = defaultdict(lambda: sp.Integer(0),
                    {w: c for w, c in prod.items() if w != ()})

    # bch = log(1 + y)
    bch = ncpoly_log_one_plus(y, 7)

    # Extract deg-7 part.
    bch_septic = extract_degree(bch, 7)

    print(f"\nbch_septic_term has {len(bch_septic)} non-zero 7-letter words.")
    print(f"(Out of 128 = 2^7 possible 7-letter words.)")

    # Compute LCM of denominators.
    denoms = []
    for w, c in bch_septic.items():
        c_simplified = sp.simplify(c)
        if c_simplified != 0:
            denoms.append(sp.fraction(c_simplified)[1])
    if denoms:
        lcm = reduce(lambda x, y: sp.lcm(x, y), denoms)
        print(f"\nLCM of denominators: {lcm}")
    else:
        lcm = 1

    # Output sorted by word for stability.
    sorted_terms = sorted(bch_septic.items(), key=lambda x: x[0])

    print("\n" + "=" * 70)
    print(f"Lean-ready snippet (with LCM = {lcm}):")
    print("=" * 70)

    print(f"\nnoncomputable def bch_septic_term (𝕂 : Type*) [RCLike 𝕂] {{𝔸 : Type*}}")
    print(f"    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=")

    first = True
    for w, c in sorted_terms:
        c_simplified = sp.simplify(c)
        if c_simplified == 0:
            continue
        # Express c as num / lcm.
        num_over_lcm = sp.simplify(c_simplified * lcm)
        if num_over_lcm == int(num_over_lcm):
            num = int(num_over_lcm)
            word_lean = word_to_lean(w)
            prefix = "    " if first else "  + "
            print(f"{prefix}({num} / {lcm} : 𝕂) • ({word_lean})")
            first = False
        else:
            print(f"  WARNING: non-integer numerator for word {w}: {num_over_lcm}")

    # Sanity check: sum of absolute coefficients (for norm bound).
    total_abs = sum(sp.Abs(c) for c in bch_septic.values())
    print(f"\nSum of |coefs|: {total_abs}")
    print(f"Sum of |coefs| as decimal: {float(total_abs):.6f}")
    print(f"\n[Norm bound: ‖bch_septic_term(a,b)‖ ≤ {float(total_abs):.6f} · s^7 where s = ‖a‖+‖b‖.]")


if __name__ == "__main__":
    main()
