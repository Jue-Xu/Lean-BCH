#!/usr/bin/env python3
"""
CAS verification: confirm that septic_d7_P5_poly equals the ΔC_3_lin(V_5)
operator form.

By construction, P_5 = (bch(x + V_5, ½a) - bch(x, ½a))_deg7 where V_5 has
deg 5 in {a, b}. At deg 7, the only contribution comes from linear-in-V_5
in C_3 (since C_3 has deg 3 in (z, y) and V_5 substituted once gives
deg 3 - 1 + 5 = 7; higher-order V_5 contributions exceed deg 7).

Using C_3(z, y) = (1/12)·([z, [z, y]] + [y, [y, z]]) (Dynkin formula),
the linear-in-V_5 perturbation when z → x + V_5 is:

  ΔC_3_lin(V_5, x, a') = (1/12)·([V_5, [x, a']]
                                 + [x, [V_5, a']]
                                 + [a', [a', V_5]])

where a' = ½a. This script verifies the operator form equals P_5 at the
polynomial level (modulo coefficient matching).
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


def ncpoly_bracket(p, q):
    """Compute [p, q] = p·q − q·p."""
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
        print(f"  {label}: 0 non-zero terms (identically zero)")
        return
    LCM = 1
    for c in p.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for c in p.values() if c != 0)
    print(f"  {label}: {n} terms, LCM = {LCM}, Σ|num| = {sum_abs}, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    # V_5 = bch_quintic_term(½a, b) = deg-5 part of bch(½a, b).
    bch_inner = bch_series(half_a, b, 5)
    V5 = extract_degree(bch_inner, 5)

    # Operator form: ΔC_3_lin(V_5, x, ½a) = (1/12)·([V_5, [x, ½a]] + [x, [V_5, ½a]] + [½a, [½a, V_5]])
    one_twelfth = sp.Rational(1, 12)
    bracket_x_a = ncpoly_bracket(x, half_a)  # [x, ½a]
    bracket_V5_a = ncpoly_bracket(V5, half_a)  # [V_5, ½a]
    bracket_a_V5 = ncpoly_bracket(half_a, V5)  # [½a, V_5]

    triple1 = ncpoly_bracket(V5, bracket_x_a)  # [V_5, [x, ½a]]
    triple2 = ncpoly_bracket(x, bracket_V5_a)  # [x, [V_5, ½a]]
    triple3 = ncpoly_bracket(half_a, bracket_a_V5)  # [½a, [½a, V_5]]

    operator_form = ncpoly_scale(
        ncpoly_add(ncpoly_add(triple1, triple2), triple3),
        one_twelfth
    )
    print("== Operator form (1/12)·([V_5, [x, ½a]] + [x, [V_5, ½a]] + [½a, [½a, V_5]]) ==")
    summarize(operator_form, "operator_form")

    # Direct P_5 from bch series:
    bch_static = bch_series(x, half_a, 7)
    P5 = extract_degree(
        ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, 7), bch_static), 7
    )
    print()
    print("== Direct P_5 = (bch(x+V_5, ½a) - bch(x, ½a))_deg7 ==")
    summarize(P5, "P5_direct")

    # Compare
    diff = ncpoly_diff(operator_form, P5)
    nz = sum(1 for c in diff.values() if c != 0)
    print()
    if nz == 0:
        print("✓ VERIFIED: operator_form == P_5")
        print("  ΔC_3_lin(V_5) operator equals septic_d7_P5_poly exactly.")
        print("  Ready to write Lean lemma `septic_d7_P5_op_form`:")
        print()
        print("  septic_d7_P5_poly 𝕂 a b =")
        print("    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a")
        print("    let V_5 : 𝔸 := bch_quintic_term 𝕂 a' b")
        print("    let x : 𝔸 := a' + b")
        print("    (12 : 𝕂)⁻¹ • (V_5 * (x * a' - a' * x) - (x * a' - a' * x) * V_5)")
        print("  + (12 : 𝕂)⁻¹ • (x * (V_5 * a' - a' * V_5) - (V_5 * a' - a' * V_5) * x)")
        print("  + (12 : 𝕂)⁻¹ • (a' * (a' * V_5 - V_5 * a') - (a' * V_5 - V_5 * a') * a')")
    else:
        print(f"✗ MISMATCH: operator_form vs P_5 differ by {nz} non-zero terms")
        for w, c in list(diff.items())[:5]:
            if c != 0:
                word = ''.join('a' if x == 0 else 'b' for x in w)
                print(f"   {sp.nsimplify(c)} · {word}")


if __name__ == "__main__":
    main()
