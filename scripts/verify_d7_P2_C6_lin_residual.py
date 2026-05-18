#!/usr/bin/env python3
"""
CAS verification: the residual

    R := bch_sextic_term(x + V_2, a') - bch_sextic_term(x, a')
         - septic_d7_P2_C6_lin_poly

is a polynomial in {a, b} containing ONLY deg-8+ terms (i.e., the deg-7
"matching" is exact: septic_d7_P2_C6_lin_poly captures all the deg-7
contributions to the C_6-diff under the V_2 substitution).

Outputs the residual's term count, LCM, and Σ|num|/LCM. This determines
whether a direct polynomial-form Lean identity is feasible (small residual)
or whether we need a Lipschitz-style approach (large residual).

For context: bch_sextic_term has 28 terms in {a, b} at deg 6. Substituting
x → x + V_2 with x = ½a + b, a' = ½a, V_2 = bch_quadratic_term(½a, b)
= (1/4)·[a, b] gives a polynomial in {a, b}. The deg-7 part is
septic_d7_P2_C6_lin_poly (60 terms). The deg-8+ part is the residual.

Higher-order contributions: substituting k V_2's into k z-positions of C_6
gives deg = 6 - k + 2k = 6 + k. So k=1 gives deg 7 (= P_2_C6_lin), k=2
gives deg 8, etc. C_6 has up to 6 z-positions, so contributions exist up
to k=6 (deg 12).
"""

import sympy as sp
from collections import defaultdict
import sys


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


def extract_ge_degree(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) >= k})


def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def summarize(p, label):
    n = sum(1 for c in p.values() if c != 0)
    if n == 0:
        print(f"  {label}: 0 non-zero terms", file=sys.stderr)
        return
    LCM = 1
    for c in p.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for c in p.values() if c != 0)
    max_abs = max(abs(int(sp.nsimplify(c * LCM))) for c in p.values() if c != 0)
    deg_min = min(len(w) for w, c in p.items() if c != 0)
    deg_max = max(len(w) for w, c in p.items() if c != 0)
    print(f"  {label}: {n} terms, deg [{deg_min}..{deg_max}], LCM = {LCM}, "
          f"Σ|num| = {sum_abs}, max|num| = {max_abs}, "
          f"Σ|num|/LCM ≈ {sum_abs/LCM:.4f}", file=sys.stderr)


def substitute(p, sub_a, sub_b):
    """Substitute atom 0 → sub_a, atom 1 → sub_b in noncomm polynomial p."""
    result = ncpoly_zero()
    for word, coef in p.items():
        prod = ncpoly_from_scalar(1)
        for atom in word:
            sub_poly = sub_a if atom == 0 else sub_b
            prod = ncpoly_mul(prod, sub_poly)
        result = ncpoly_add(result, ncpoly_scale(prod, coef))
    return result


def main():
    # Setup
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    MX = 12  # need enough degrees for the full diff (up to deg 12)

    # V_2 = (1/4)·[a, b] (the deg-2 part of bch(½a, b))
    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)
    summarize(V2, "V_2 (= bch_quadratic_term(½a, b))")

    # bch_sextic_term as a polynomial in 2 abstract atoms (we'll feed in
    # substitutions for the two arguments).
    # Per Basic.lean lines 3033-3062: bch_sextic_term has 28 terms with
    # LCM 1440. We compute it directly via the BCH series at deg 6.
    bch_to_6 = bch_series(a, b, 6)
    bch_6_abs = extract_degree(bch_to_6, 6)
    summarize(bch_6_abs, "bch_sextic_term (abstract, in {a, b})")

    # bch_sextic_term(x + V_2, a') - bch_sextic_term(x, a') as poly in {a, b}
    x_plus_V2 = ncpoly_add(x, V2)
    sextic_at_xV2 = substitute(bch_6_abs, x_plus_V2, half_a)
    sextic_at_x = substitute(bch_6_abs, x, half_a)
    full_diff = ncpoly_sub(sextic_at_xV2, sextic_at_x)
    summarize(full_diff, "full diff: bch_sextic_term(x+V_2, a') - bch_sextic_term(x, a')")

    # Decompose by degree
    print("\n=== Full diff by degree ===", file=sys.stderr)
    for k in range(6, 13):
        comp = extract_degree(full_diff, k)
        summarize(comp, f"  deg {k}")

    # The deg-7 part should match septic_d7_P2_C6_lin_poly
    deg7_part = extract_degree(full_diff, 7)
    summarize(deg7_part, "deg-7 part (= septic_d7_P2_C6_lin_poly, expected 60 terms LCM 92160)")

    # The deg-8+ part is the residual
    deg8_plus = extract_ge_degree(full_diff, 8)
    summarize(deg8_plus, "deg-8+ residual (= full_diff - septic_d7_P2_C6_lin_poly)")

    # === Per-V_2-power decomposition ===
    # Substituting k V_2's gives degree 6 + k. Verify each level matches.
    print("\n=== Per-V_2-power decomposition ===", file=sys.stderr)
    # k=0: bch_sextic_term(x, a') (subtracted away)
    # k=1: deg-7 = septic_d7_P2_C6_lin_poly
    # k=2: deg-8 ...
    # k=3: deg-9 ...
    # k=4: deg-10 ...
    # k=5: deg-11 ...
    # k=6: deg-12 ...

    # Total residual ratio
    deg8_part = extract_degree(full_diff, 8)
    deg9_part = extract_degree(full_diff, 9)
    deg10_part = extract_degree(full_diff, 10)
    deg11_part = extract_degree(full_diff, 11)
    deg12_part = extract_degree(full_diff, 12)
    summarize(deg8_part, "deg-8 (k=2 substitutions, V_2² · C_6)")
    summarize(deg9_part, "deg-9 (k=3 substitutions, V_2³ · C_6)")
    summarize(deg10_part, "deg-10 (k=4)")
    summarize(deg11_part, "deg-11 (k=5)")
    summarize(deg12_part, "deg-12 (k=6)")

    # === Implications for Lean formalization ===
    print("\n=== Lean formalization implications ===", file=sys.stderr)
    n_residual = sum(1 for c in deg8_plus.values() if c != 0)
    print(f"Residual size: {n_residual} terms in {{a, b}}", file=sys.stderr)
    if n_residual <= 200:
        print(f"  → Direct polynomial-form Lean DEF + identity FEASIBLE", file=sys.stderr)
        print(f"    (similar to existing septic_d7_P2_C6_lin_poly with 60 terms)", file=sys.stderr)
    elif n_residual <= 500:
        print(f"  → Marginal: split into per-deg sub-pieces (deg 8..12)", file=sys.stderr)
    else:
        print(f"  → Direct polynomial encoding TOO LARGE: use Lipschitz-residual", file=sys.stderr)
        print(f"    approach via norm_bch_sextic_term_diff_le composed with ‖V_2‖² ≤ s⁴", file=sys.stderr)


if __name__ == "__main__":
    main()
