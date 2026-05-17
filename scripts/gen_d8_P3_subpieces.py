#!/usr/bin/env python3
"""
Generate Lean DEFs for the 2 sub-pieces of septic_d8_P3_poly:

  septic_d8_P3_poly = septic_d8_P3_C4_quad_poly + septic_d8_P3_C6_lin_poly

where:
  • C_4 quad sub-piece: quadratic-in-V_3 from C_4 (Dynkin-expressible).
      C_4_quad(V_3, a') = -(1/24)·[a', [V_3, [V_3, a']]]
    Using C_4(z, y) = -(1/24)·[y, [z, [z, y]]] with BOTH z's replaced by V_3.
  • C_6 lin sub-piece: linear-in-V_3 from C_6 (NOT Dynkin-expressible).
    Defined as septic_d8_P3_poly - C_4_quad_poly. Uses bch_sextic_term
    implicitly (the linear directional derivative of bch_sextic_term in
    its first arg, evaluated at (x, a'), applied to V_3).

d8 analog of `scripts/verify_P3_decomp.py` at one degree higher
(V_3·V_3 quadratic from C_4 instead of C_3; V_3 linear from C_6 instead
of C_5).

Outputs:
  1. The 2 sub-piece polynomial defs (CAS-extracted).
  2. The sum identity theorem `septic_d8_P3_pieces_decomp`.

Term count expectations (CAS-derived):
  • C_4 quad: should match Lie poly [V_3, [V_3, a']] scaled by -(1/24).
  • C_6 lin: ~ 150 terms (P_3 has 166 terms).
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
        print(f"  {label}: 0 non-zero terms", file=sys.stderr)
        return
    LCM = 1
    for c in p.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for c in p.values() if c != 0)
    print(f"  {label}: {n} terms, LCM = {LCM}, Σ|num| = {sum_abs}, Σ|num|/LCM ≈ {sum_abs/LCM:.4f}",
          file=sys.stderr)


def emit_def(name, doc, poly, file=None):
    if file is None:
        file = sys.stdout
    items = sorted([(w, c) for w, c in poly.items() if c != 0], key=lambda x: x[0])
    if not items:
        print(f"-- {name}: zero polynomial", file=file)
        return
    LCM = 1
    for _, c in items:
        LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    print(f"/-- **{name}**: {doc}", file=file)
    print(file=file)
    print(f"CAS-derived; denominator {LCM}, {len(items)} terms, "
          f"Σ|num|/LCM ≈ {sum_abs/LCM:.4f}. -/", file=file)
    print(f"noncomputable def {name} (𝕂 : Type*) [RCLike 𝕂]", file=file)
    print(f"    {{𝔸 : Type*}} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=", file=file)
    first = True
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        prefix = "    " if first else "  + "
        print(f"{prefix}({n} / {LCM} : 𝕂) • ({word_str})", file=file)
        first = False
    print(file=file)


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    bch_inner = bch_series(half_a, b, 6)
    V3 = extract_degree(bch_inner, 3)

    # C_4 quadratic-in-V_3 part: -(1/24)·[a', [V_3, [V_3, a']]]
    minus_one_24th = sp.Rational(-1, 24)
    bracket_V3_a = ncpoly_bracket(V3, half_a)               # [V_3, a']
    inner = ncpoly_bracket(V3, bracket_V3_a)                # [V_3, [V_3, a']]
    outer = ncpoly_bracket(half_a, inner)                   # [a', [V_3, [V_3, a']]]
    C4_quad = ncpoly_scale(outer, minus_one_24th)
    summarize(C4_quad, "C4_quad")

    # septic_d8_P3 from bch series
    bch_static = bch_series(x, half_a, 8)
    P3 = extract_degree(
        ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, 8), bch_static), 8
    )
    summarize(P3, "P3_d8")

    # C_6 lin part = P3 - C4_quad
    C6_lin = ncpoly_sub(P3, C4_quad)
    summarize(C6_lin, "C6_lin")

    # Verify
    total = ncpoly_add(C4_quad, C6_lin)
    diff = ncpoly_diff(total, P3)
    nz = sum(1 for c in diff.values() if c != 0)
    if nz == 0:
        print("✓ VERIFIED: septic_d8_P3_poly = C4_quad + C6_lin", file=sys.stderr)
    else:
        print(f"✗ MISMATCH: differ by {nz} terms", file=sys.stderr)
        return

    # Emit Lean code to stdout
    print("/-! ### Sub-piece decomposition of `septic_d8_P3_poly`")
    print()
    print("P_3_d8 = (bch(x + V_3, ½a) - bch(x, ½a))_deg8 splits into 2 sub-pieces:")
    print("  • C_4 quadratic-in-V_3 from C_4 (deg 4 + 2·(3-1) = 8): Dynkin-expressible.")
    print("    The [z, [z, y]] term of C_4 with both z's substituted by V_3.")
    print("  • C_6 linear-in-V_3 from C_6 (deg 6 + (3-1) = 8): NOT Dynkin in Lean")
    print("    (bch_sextic_term is monomial form, not Dynkin Lie poly).")
    print()
    print("d8 analog of `septic_d7_P3_pieces_decomp` (C_3 quad + C_5 lin).")
    print()
    print("CAS-derived: `scripts/gen_d8_P3_subpieces.py`. The polynomial form of")
    print("C_4 quad is computed from the Dynkin formula directly; C_6 lin is")
    print("defined as `septic_d8_P3_poly − septic_d8_P3_C4_quad_poly`.")
    print("-/")
    print()

    emit_def("septic_d8_P3_C4_quad_poly",
             "C_4 quadratic-in-V_3 part of P_3 at deg 8. Equals "
             "-(1/24)·[a', [V_3, [V_3, a']]] where V_3 = bch_cubic_term(½a, b), "
             "a' = ½a. The simpler of the 2 sub-pieces of P_3_d8 (Dynkin-expressible "
             "via the d8 analog of C_3 quad in d7).",
             C4_quad)
    emit_def("septic_d8_P3_C6_lin_poly",
             "C_6 linear-in-V_3 part of P_3 at deg 8. Defined as septic_d8_P3_poly - "
             "septic_d8_P3_C4_quad_poly (the residual after extracting the C_4 quadratic "
             "piece). Operator-form interpretation: the linear-in-V_3 perturbation of "
             "bch_sextic_term restricted to deg 8.",
             C6_lin)

    print("/-- **2-piece sub-decomposition of `septic_d8_P3_poly`**.")
    print()
    print("CAS-verified: septic_d8_P3_poly = septic_d8_P3_C4_quad_poly +")
    print("septic_d8_P3_C6_lin_poly. The C_4 quad piece is Dynkin-expressible")
    print("(see `septic_d8_P3_C4_quad_op_form`); the C_6 lin piece uses")
    print("`bch_sextic_term` in monomial form and needs a Lipschitz-style")
    print("operator-form treatment (analog of d7's C_5 lin piece). -/")
    print("private theorem septic_d8_P3_pieces_decomp")
    print("    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]")
    print("    (a b : 𝔸) :")
    print("    septic_d8_P3_poly 𝕂 a b =")
    print("      septic_d8_P3_C4_quad_poly 𝕂 a b + septic_d8_P3_C6_lin_poly 𝕂 a b := by")
    print("  unfold septic_d8_P3_poly septic_d8_P3_C4_quad_poly septic_d8_P3_C6_lin_poly")
    print("  match_scalars <;> ring")


if __name__ == "__main__":
    import sys
    main()
