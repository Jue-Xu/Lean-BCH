#!/usr/bin/env python3
"""
Discover the algebraic decomposition for `symmetric_bch_septic_poly_alt_form`
in BCH/SymmetricQuintic.lean — the deg-7 analog of
`symmetric_bch_quintic_poly_alt_form` at one degree higher.

Goal
----
Express `symmetric_bch_septic_poly(a, b)` (the τ⁷ coefficient of
log(exp(a/2)·exp(b)·exp(a/2))) as:

    sym_E₇(a, b) = bch_septic_term(½a, b)
                 + bch_septic_term(½a + b, ½a)
                 + ½·[bch_sextic_term(½a, b), ½a]                (deg 6+1=7)
                 + (C_k(z, ½a) − C_k(½a+b, ½a))_d7   for k = 3..6
                 + correction polynomial in a, b

The quintic version had 5 components (k = 3, 4). For septic at deg 7, we
need all C_k for k = 3..6 because each contributes a deg-7 piece via
substituting z = (½a+b) + W where W contains the deg-2+ tail.

Strategy
--------
1. Build NC-polynomials over {a=0, b=1}, work up to degree MAX=7.
2. Compute z = bch(½a, b) and bch(z, ½a) up to deg 7.
3. sym_E₇ = degree-7 part of bch(z,½a) − (a+b).
4. bch_septic_term(½a, b) = degree-7 part of bch(½a, b).
5. bch_septic_term(½a+b, ½a) = degree-7 part of bch(½a+b, ½a).
6. ½·[bch_sextic_term(½a, b), ½a] (deg-6 term × ½a).
7. For k = 3..6: extract deg-7 of C_k(z, ½a) − C_k(½a+b, ½a).
   Where C_k(x, y) := degree-k part of the formal BCH series in (x, y).
8. Subtract all of these from sym_E₇ → residual = correction polynomial.

If residual is non-zero but polynomial in {a, b} only (no z), we have the
alt-form. Lean transcription follows the quintic pattern.

Dependencies: sympy
Usage:        python3 discover_septic_alt_form.py
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple

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
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p: NCPoly, max_degree: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x: NCPoly, max_degree: int) -> NCPoly:
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x: NCPoly, max_degree: int) -> NCPoly:
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


def commutator(p: NCPoly, q: NCPoly) -> NCPoly:
    return ncpoly_sub(ncpoly_mul(p, q), ncpoly_mul(q, p))


def extract_degree(p: NCPoly, k: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})


def bch_series(x: NCPoly, y: NCPoly, max_degree: int) -> NCPoly:
    """bch(x, y) = log(exp(x)·exp(y)) truncated to max_degree."""
    ex = ncpoly_exp(x, max_degree)
    ey = ncpoly_exp(y, max_degree)
    prod = ncpoly_truncate(ncpoly_mul(ex, ey), max_degree)
    minus_one = defaultdict(lambda: sp.Integer(0),
                            {w: c for w, c in prod.items() if w != ()})
    return ncpoly_log_one_plus(minus_one, max_degree)


def display_ncpoly(p: NCPoly, label: str = ""):
    items = sorted([(w, c) for w, c in p.items() if c != 0],
                   key=lambda x: (len(x[0]), x[0]))
    if label:
        print(f"\n--- {label} ({len(items)} terms) ---")
    if not items:
        print("  (zero)")
        return
    for w, c in items:
        word_str = ''.join('a' if l == 0 else 'b' for l in w)
        c_str = sp.nsimplify(c)
        print(f"  {c_str} · {word_str}")


def main():
    MAX = 7
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)               # ½a
    half_a_plus_b = ncpoly_add(half_a, b)        # ½a + b

    print("=" * 70)
    print("Discovering symmetric_bch_septic_poly_alt_form decomposition")
    print("=" * 70)

    # Step 1-3: compute symmetric BCH up to deg 7
    print("\n[Step 1] z = bch(½a, b) up to degree 7")
    z = bch_series(half_a, b, MAX)
    print("[Step 2] bch(z, ½a) up to degree 7")
    bch_z_halfa = bch_series(z, half_a, MAX)
    print("[Step 3] sym_bch_cubic = bch(z, ½a) − (a+b)")
    a_plus_b = ncpoly_add(a, b)
    sym_bch_cubic_full = ncpoly_sub(bch_z_halfa, a_plus_b)

    # Step 4: extract degree-7 part = sym_E₇(a, b)
    sym_E7 = extract_degree(sym_bch_cubic_full, 7)
    print(f"[Step 4] sym_E₇(a, b) extracted: {len(sym_E7)} non-zero words")

    # Confirm deg-2, 4, 6 vanish (palindromic symmetry).
    for k in (2, 4, 6):
        layer = extract_degree(sym_bch_cubic_full, k)
        nz = sum(1 for c in layer.values() if c != 0)
        print(f"   sanity: sym_bch_cubic deg-{k} non-zero words = {nz} (expect 0)")

    # Step 5: bch_septic_term(½a, b)
    bst_inner = extract_degree(z, 7)
    print(f"\n[Step 5] bch_septic_term(½a, b): {len(bst_inner)} non-zero words")

    # Step 6: bch_septic_term(½a+b, ½a) — deg 7 of bch(½a+b, ½a)
    bch_outer_static = bch_series(half_a_plus_b, half_a, MAX)
    bst_outer = extract_degree(bch_outer_static, 7)
    print(f"[Step 6] bch_septic_term(½a+b, ½a): {len(bst_outer)} non-zero words")

    # Step 7: ½·[bch_sextic_term(½a, b), ½a]  (deg 6+1 = 7)
    bst6_inner = extract_degree(z, 6)
    bracket_C6_inner_halfa = commutator(bst6_inner, half_a)
    half_bracket_C6 = ncpoly_scale(bracket_C6_inner_halfa, half)
    print(f"[Step 7] ½·[C₆(½a, b), ½a] (deg 7): "
          f"{sum(1 for c in half_bracket_C6.values() if c != 0)} non-zero words")

    # Residual so far.  Match the QUINTIC alt-form pattern: subtract ONLY the
    # two bst pieces, absorb everything else (½·[C₆, ½a] + C_k-diffs) into
    # the correction polynomial.
    residual = ncpoly_sub(sym_E7, bst_inner)
    residual = ncpoly_sub(residual, bst_outer)
    nz_r0 = sum(1 for c in residual.values() if c != 0)
    print(f"   COMBINED correction = sym_E₇ − bst(½a,b) − bst(½a+b,½a): {nz_r0} terms")

    # No further subtraction: the correction polynomial = full residual.

    nz_final = sum(1 for c in residual.values() if c != 0)
    print()
    if nz_final == 0:
        print("=" * 70)
        print("✓ DECOMPOSITION COMPLETE: residual = 0")
        print("=" * 70)
        print("symmetric_bch_septic_poly(a, b) =")
        print("    bch_septic_term(½a, b)")
        print("  + bch_septic_term(½a+b, ½a)")
        print("  + ½·[bch_sextic_term(½a, b), ½a]")
        print("  + Σ_{k=3..6} (C_k(z, ½a) − C_k(½a+b, ½a))_d7   [z = bch(½a, b)]")
    else:
        print("=" * 70)
        print(f"✗ Non-zero residual ({nz_final} terms) — correction polynomial:")
        print("=" * 70)
        display_ncpoly(residual, "correction polynomial")

        # Compute LCM of denominators for clean rational form.
        lcm = 1
        for c in residual.values():
            if c != 0:
                lcm = sp.lcm(lcm, sp.denom(sp.nsimplify(c)))
        print(f"\nLCM of denominators: {lcm}")

        # Print as Lean-style smul terms.
        items = sorted([(w, c) for w, c in residual.items() if c != 0],
                       key=lambda x: x[0])
        sum_abs = 0
        print(f"\n--- Lean transcription form (denominator {lcm}) ---")
        for w, c in items:
            num = sp.nsimplify(c * lcm)
            assert num == int(num), f"non-integer numerator {num} for word {w}"
            sum_abs += abs(int(num))
            word_str = ' * '.join('a' if l == 0 else 'b' for l in w)
            print(f"  + ({num} / {lcm} : 𝕂) • ({word_str})")
        print(f"\n  sum of |numerators| / {lcm} = {sum_abs}/{lcm} ≈ {sum_abs/lcm:.4f}")
        print(f"  → ‖correction‖ ≤ {sum_abs}/{lcm} · s⁷ for s = ‖a‖+‖b‖")


if __name__ == "__main__":
    main()
