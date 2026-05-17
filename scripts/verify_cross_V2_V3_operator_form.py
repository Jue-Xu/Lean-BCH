#!/usr/bin/env python3
"""
CAS verification: confirm Cross(V_2, V_3) operator form.

Cross(V_2, V_3) = (bch(x + V_2 + V_3, ½a) − bch(x + V_2, ½a)
                  − bch(x + V_3, ½a) + bch(x, ½a))_deg7

At deg 7, the contributions come from:
  • Bilinear V_2·V_3 from C_p with 2+ z positions: deg = p + 3.
    For deg 7, p = 4. C_4 = -(1/24)·[y, [z, [z, y]]] has 2 z's per word ✓.
  • Higher-order from C_p with 3+ z positions: deg p + 4 or more.
    For deg 7, need p ≤ 3 with ≥ 3 z positions. C_3 has max 2 z positions ✗.

So Cross(V_2, V_3) = bilinear V_2·V_3 from C_4 ONLY.

Using C_4(z, y) = -(1/24)·[y, [z, [z, y]]], the bilinear V_2·V_3 part:
  [z, [z, y]] bilinear V_2·V_3 = [V_2, [V_3, y]] + [V_3, [V_2, y]]

So ΔC_4_bil(V_2, V_3, a') = -(1/24)·{[a', [V_2, [V_3, a']]] + [a', [V_3, [V_2, a']]]}

where a' = ½a, V_2 = ½·[a', b], V_3 = bch_cubic_term(½a, b).
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

    bch_inner = bch_series(half_a, b, 7)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)

    # Operator form: -(1/24)·([a', [V_2, [V_3, a']]] + [a', [V_3, [V_2, a']]])
    minus_one_24th = sp.Rational(-1, 24)

    bracket_V3_a = ncpoly_bracket(V3, half_a)  # [V_3, a']
    bracket_V2_a = ncpoly_bracket(V2, half_a)  # [V_2, a']

    inner1 = ncpoly_bracket(V2, bracket_V3_a)  # [V_2, [V_3, a']]
    inner2 = ncpoly_bracket(V3, bracket_V2_a)  # [V_3, [V_2, a']]

    outer1 = ncpoly_bracket(half_a, inner1)  # [a', [V_2, [V_3, a']]]
    outer2 = ncpoly_bracket(half_a, inner2)  # [a', [V_3, [V_2, a']]]

    operator_form = ncpoly_scale(ncpoly_add(outer1, outer2), minus_one_24th)
    print("== Operator form -(1/24)·([a', [V_2, [V_3, a']]] + [a', [V_3, [V_2, a']]]) ==")
    summarize(operator_form, "operator_form")

    # Direct Cross(V_2, V_3):
    bch_23 = bch_series(ncpoly_add(ncpoly_add(x, V2), V3), half_a, 7)
    bch_2 = bch_series(ncpoly_add(x, V2), half_a, 7)
    bch_3 = bch_series(ncpoly_add(x, V3), half_a, 7)
    bch_0 = bch_series(x, half_a, 7)
    cross = ncpoly_sub(ncpoly_sub(bch_23, bch_2), ncpoly_sub(bch_3, bch_0))
    cross_d7 = extract_degree(cross, 7)
    print()
    print("== Direct Cross(V_2, V_3) ==")
    summarize(cross_d7, "cross_d7")

    diff = ncpoly_diff(operator_form, cross_d7)
    nz = sum(1 for c in diff.values() if c != 0)
    print()
    if nz == 0:
        print("✓ VERIFIED: operator_form == Cross(V_2, V_3)")
        print("  ΔC_4_bil(V_2, V_3) operator equals septic_d7_cross_V2_V3_poly exactly.")
        print("  (No trilinear V_2²·V_3 contribution — C_3 has only 2 z-positions max,")
        print("   so trilinear needs C_p with 3+ z-positions giving deg p+4 ≥ 8 > 7.)")
    else:
        print(f"✗ MISMATCH: differ by {nz} terms")
        summarize(diff, "diff")


if __name__ == "__main__":
    main()
