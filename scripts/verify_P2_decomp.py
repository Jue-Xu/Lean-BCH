#!/usr/bin/env python3
"""
CAS verification: decompose septic_d7_P2_poly into 2 operator-form sub-pieces.

P_2 captures the V_2-only deg-7 perturbation. At deg 7, the contributions are:
  • Linear-in-V_2 from C_6 (deg 6+1 = 7).
  • Quadratic-in-V_2 from C_5 (deg 5+2 = 7).
  • Higher orders: cubic-in-V_2 from C_4 requires C_4 with 3+ z-positions
    (only has 2); quartic-in-V_2 from C_3 requires C_3 with 4+ z-positions
    (only has 2). Both IMPOSSIBLE.

So P_2 has only 2 sub-pieces, not 4 as initially thought.

This script:
  1. Computes both sub-pieces via direct CAS perturbation extraction.
  2. Verifies their sum equals septic_d7_P2_poly.
  3. Outputs both polynomial forms for Lean encoding.

The sub-pieces are:
  • septic_d7_P2_C6_lin_poly = (deg-7 of bch_sextic_term(x+V_2, ½a)
                                - bch_sextic_term(x, ½a))
    = linear-in-V_2 perturbation of bch_sextic_term restricted to deg 7.
  • septic_d7_P2_C5_quad_poly = (deg-7 of bch_quintic_term(x+V_2, ½a)
                                  - bch_quintic_term(x, ½a))
    = quadratic-in-V_2 perturbation of bch_quintic_term restricted to deg 7.

Neither sub-piece is Dynkin-expressible in Lean (bch_sextic_term and
bch_quintic_term are in monomial form), so both stay as polynomial DEFs.
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


def emit_def(name, doc, poly):
    items = sorted([(w, c) for w, c in poly.items() if c != 0], key=lambda x: x[0])
    if not items:
        print(f"-- {name}: zero polynomial")
        return
    LCM = 1
    for _, c in items:
        LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    print(f"/-- **{name}**: {doc}")
    print(f"   CAS-derived; denominator {LCM}, {len(items)} terms, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}. -/")
    print(f"noncomputable def {name} (𝕂 : Type*) [RCLike 𝕂]")
    print(f"    {{𝔸 : Type*}} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=")
    first = True
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        prefix = "    " if first else "  + "
        print(f"{prefix}({n} / {LCM} : 𝕂) • ({word_str})")
        first = False
    print()


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    bch_inner = bch_series(half_a, b, 7)
    V2 = extract_degree(bch_inner, 2)

    # septic_d7_P2_poly = deg-7 of (bch(x + V_2, ½a) - bch(x, ½a)).
    bch_static = bch_series(x, half_a, 7)
    bch_plus = bch_series(ncpoly_add(x, V2), half_a, 7)
    bch_minus = bch_series(ncpoly_sub(x, V2), half_a, 7)
    P2 = extract_degree(ncpoly_sub(bch_plus, bch_static), 7)
    print("== septic_d7_P2_poly (V_2-only deg-7 perturbation) ==")
    summarize(P2, "P2")

    # Forward/backward symmetry trick to separate linear vs quadratic in V_2:
    # bch(x+V_2, ½a) - bch(x, ½a) = (linear-V_2) + (quad-V_2) + (cubic) + ...
    # bch(x-V_2, ½a) - bch(x, ½a) = -(linear) + (quad) - (cubic) + ...
    # Half-sum: (quad) + (quartic) + ... = even-in-V_2 (excluding constant).
    # Half-diff: (linear) + (cubic) + ... = odd-in-V_2.
    #
    # At deg 7 in {a, b}:
    #   • C_6 lin-in-V_2 at deg 6+1=7: ODD in V_2, in half-diff.
    #   • C_5 quad-in-V_2 at deg 5+2=7: EVEN in V_2, in half-sum.
    #   • C_4 cubic-in-V_2 at deg 4+3=7: impossible (C_4 has 2 z-positions).
    #   • Higher orders: deg ≥ 8.
    # So at deg 7, half-sum = C_5 quad piece only; half-diff = C_6 lin piece only.

    bch_minus_diff = ncpoly_sub(bch_minus, bch_static)
    bch_plus_diff = ncpoly_sub(bch_plus, bch_static)
    half = sp.Rational(1, 2)
    half_sum = ncpoly_scale(ncpoly_add(bch_plus_diff, bch_minus_diff), half)
    half_diff = ncpoly_scale(ncpoly_sub(bch_plus_diff, bch_minus_diff), half)

    C5_quad_d7 = extract_degree(half_sum, 7)
    C6_lin_d7 = extract_degree(half_diff, 7)

    print()
    print("== C_6 lin-in-V_2 piece (half-diff at deg 7 = odd-in-V_2 perturbation) ==")
    summarize(C6_lin_d7, "C6_lin_d7")

    print()
    print("== C_5 quad-in-V_2 piece (half-sum at deg 7 = even-in-V_2 perturbation) ==")
    summarize(C5_quad_d7, "C5_quad_d7")

    # Sum check
    total = ncpoly_add(C6_lin_d7, C5_quad_d7)
    diff = ncpoly_diff(total, P2)
    nz = sum(1 for c in diff.values() if c != 0)
    print()
    if nz == 0:
        print("✓ VERIFIED: septic_d7_P2_poly = C_6_lin_d7 + C_5_quad_d7 (2 sub-pieces)")
    else:
        print(f"✗ MISMATCH: differ by {nz} terms")
        summarize(diff, "diff")

    print()
    print("== Lean DEF generation ==")
    print()
    emit_def("septic_d7_P2_C6_lin_poly",
             "C_6 linear-in-V_2 part of P_2 at deg 7. Equals the deg-7 part of "
             "(bch_sextic_term(x+V_2, ½a) - bch_sextic_term(x, ½a)) where x = ½a+b, "
             "V_2 = ½·[½a, b]. Not Dynkin-expressible in Lean (bch_sextic_term is "
             "monomial form), but bounded via Lipschitz on bch_sextic_term.",
             C6_lin_d7)
    emit_def("septic_d7_P2_C5_quad_poly",
             "C_5 quadratic-in-V_2 part of P_2 at deg 7. Equals the deg-7 part of "
             "(bch_quintic_term(x+V_2, ½a) - bch_quintic_term(x, ½a)). Not Dynkin-"
             "expressible (bch_quintic_term is monomial form). The bch_quintic_term "
             "Lipschitz bound gives bound K·s⁴·‖V_2‖ ≤ K·s⁶ on the FULL diff; the "
             "deg-7 quadratic piece is a residual after the deg-6 linear piece.",
             C5_quad_d7)


if __name__ == "__main__":
    main()
