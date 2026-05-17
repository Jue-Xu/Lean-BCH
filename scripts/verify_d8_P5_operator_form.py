#!/usr/bin/env python3
"""
CAS verification: confirm that septic_d8_P5_poly equals the ΔC_4_lin(V_5)
operator form.

P_5_d8 = (bch(x + V_5, ½a) - bch(x, ½a))_deg8 where V_5 has deg 5.
At deg 8, the only contribution comes from linear-in-V_5 in C_4 (since
C_4 has deg 4 and replacing one z with V_5 gives deg 4 + (5-1) = 8;
higher-order V_5 contributions exceed deg 8).

Using C_4(z, y) = -(1/24)·[y, [z, [z, y]]] (Lean def of bch_quartic_term),
the linear-in-V_5 perturbation when z → x + V_5 gives:

  ΔC_4_lin(V_5, x, a') = -(1/24)·([a', [V_5, [x, a']]]
                                  + [a', [x, [V_5, a']]])

d8 analog of verify_P4_operator_form.py (V_4 → V_5).
"""

import sympy as sp
from collections import defaultdict


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
        print(f"  {label}: 0 non-zero terms")
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

    bch_inner = bch_series(half_a, b, 5)
    V5 = extract_degree(bch_inner, 5)

    minus_one_24th = sp.Rational(-1, 24)
    bracket_x_a = ncpoly_bracket(x, half_a)
    bracket_V5_a = ncpoly_bracket(V5, half_a)
    inner1 = ncpoly_bracket(V5, bracket_x_a)
    inner2 = ncpoly_bracket(x, bracket_V5_a)
    outer1 = ncpoly_bracket(half_a, inner1)
    outer2 = ncpoly_bracket(half_a, inner2)

    operator_form = ncpoly_scale(ncpoly_add(outer1, outer2), minus_one_24th)
    print("== Operator form -(1/24)·([a', [V_5, [x, a']]] + [a', [x, [V_5, a']]]) ==")
    summarize(operator_form, "operator_form")

    bch_static = bch_series(x, half_a, 8)
    P5 = extract_degree(
        ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, 8), bch_static), 8
    )
    print()
    print("== Direct P_5_d8 = (bch(x+V_5, ½a) - bch(x, ½a))_deg8 ==")
    summarize(P5, "P5_d8_direct")

    diff = ncpoly_diff(operator_form, P5)
    nz = sum(1 for c in diff.values() if c != 0)
    print()
    if nz == 0:
        print("✓ VERIFIED: operator_form == P_5_d8")
        print("  ΔC_4_lin(V_5) operator equals septic_d8_P5_poly exactly.")
    else:
        print(f"✗ MISMATCH: differ by {nz} terms")
        for w, c in list(diff.items())[:5]:
            if c != 0:
                word = ''.join('a' if x == 0 else 'b' for x in w)
                print(f"   {sp.nsimplify(c)} · {word}")


if __name__ == "__main__":
    main()
