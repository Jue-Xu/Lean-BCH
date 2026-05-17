#!/usr/bin/env python3
"""
Generate Lean DEFs for the 6 operator-form pieces of septic_d7_perturbation_poly:

  septic_d7_perturbation_poly
    = septic_d7_P2_poly + septic_d7_P3_poly + septic_d7_P4_poly + septic_d7_P5_poly
      + septic_d7_cross_V2_V3_poly + septic_d7_cross_V2_V4_poly

CAS-verified at `scripts/verify_d7_operator_decomp.py`. Each piece is an
explicit polynomial in {a, b} with rational coefficients.

This script outputs Lean source code for:
  • 6 noncomputable defs (each piece as an explicit polynomial).
  • 1 theorem `septic_d7_perturbation_poly_pieces_decomp` stating the sum
    of the 6 pieces equals septic_d7_perturbation_poly.

The theorem's proof is `unfold + match_scalars <;> ring` (each piece's def
unfolds to its explicit polynomial form, then ring closes the goal).
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


def cross(x, Vj, Vk, halfa, mx, target_deg):
    bch_jk = bch_series(ncpoly_add(ncpoly_add(x, Vj), Vk), halfa, mx)
    bch_j = bch_series(ncpoly_add(x, Vj), halfa, mx)
    bch_k = bch_series(ncpoly_add(x, Vk), halfa, mx)
    bch_0 = bch_series(x, halfa, mx)
    result = ncpoly_sub(ncpoly_sub(bch_jk, bch_j), ncpoly_sub(bch_k, bch_0))
    return extract_degree(result, target_deg)


def fmt_word(w):
    return ' * '.join('a' if x == 0 else 'b' for x in w)


def emit_def(name, doc, poly, indent="    ", first_prefix=None):
    """Emit a Lean noncomputable def for the given polynomial."""
    items = sorted([(w, c) for w, c in poly.items() if c != 0], key=lambda x: x[0])
    LCM = 1
    for _, c in items:
        LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    print(f"/-- **{name}**: {doc}")
    print()
    print(f"CAS-derived; denominator {LCM}, {len(items)} terms,")
    print(f"Σ|num|/LCM = {sum_abs}/{LCM} ≈ {sum_abs/LCM:.4f}. -/")
    print(f"noncomputable def {name} (𝕂 : Type*) [RCLike 𝕂]")
    print(f"    {{𝔸 : Type*}} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=")
    first = True
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = fmt_word(w)
        prefix = indent if first else "  + "
        print(f"{prefix}({n} / {LCM} : 𝕂) • ({word_str})")
        first = False
    print()


def main():
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)
    bch_inner = bch_series(half_a, b, 7)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)

    bch_static = bch_series(x, half_a, 7)
    P2 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V2), half_a, 7), bch_static), 7)
    P3 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, 7), bch_static), 7)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, 7), bch_static), 7)
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, 7), bch_static), 7)
    cross_23 = cross(x, V2, V3, half_a, 7, 7)
    cross_24 = cross(x, V2, V4, half_a, 7, 7)

    print("/-! ## 6-piece operator-form decomposition of septic_d7_perturbation_poly")
    print()
    print("From CAS verification (`scripts/verify_d7_operator_decomp.py`):")
    print()
    print("    septic_d7_perturbation_poly")
    print("      = septic_d7_P2_poly + septic_d7_P3_poly + septic_d7_P4_poly")
    print("        + septic_d7_P5_poly + septic_d7_cross_V2_V3_poly + septic_d7_cross_V2_V4_poly")
    print()
    print("Each piece corresponds to a specific operator-form perturbation:")
    print("  • P_j := (bch(x + V_j, ½a) − bch(x, ½a))_deg7  (single-V_j perturbation).")
    print("  • Cross(V_j, V_k) := (bch(x+V_j+V_k, ½a) − bch(x+V_j, ½a)")
    print("                       − bch(x+V_k, ½a) + bch(x, ½a))_deg7  (mixed cross).")
    print()
    print("Foundation for the Phase B-septic operator-form identity (eventual O(s⁹)")
    print("joint bound replacing the current O(s⁷) per-piece bound on")
    print("septic_d7_perturbation_poly via Lipschitz bounds on each operator form).")
    print("-/")
    print()

    emit_def("septic_d7_P2_poly",
             "V_2-only deg-7 perturbation piece (P_2). Captures contributions from "
             "linear-in-V_2 in C_6, quadratic-in-V_2 in C_5, cubic-in-V_2 in C_4, "
             "and quartic-in-V_2 in C_3.", P2)
    emit_def("septic_d7_P3_poly",
             "V_3-only deg-7 perturbation piece (P_3). Captures linear-in-V_3 in C_5 "
             "and quadratic-in-V_3 in C_3.", P3)
    emit_def("septic_d7_P4_poly",
             "V_4-only deg-7 perturbation piece (P_4). Captures only linear-in-V_4 "
             "in C_4 (higher-order V_4 contributions exceed deg 7).", P4)
    emit_def("septic_d7_P5_poly",
             "V_5-only deg-7 perturbation piece (P_5). Captures only linear-in-V_5 "
             "in C_3 (higher-order V_5 contributions exceed deg 7).", P5)
    emit_def("septic_d7_cross_V2_V3_poly",
             "V_2·V_3 cross deg-7 perturbation piece. Bilinear V_2·V_3 from C_4 "
             "(deg 4+1+2=7) plus trilinear V_2²·V_3 from C_3 (deg 3+1+1+2=7).",
             cross_23)
    emit_def("septic_d7_cross_V2_V4_poly",
             "V_2·V_4 cross deg-7 perturbation piece. Bilinear V_2·V_4 from C_3 "
             "(deg 3+1+3=7); only contribution at deg 7.", cross_24)

    print("/-- **6-piece decomposition of `septic_d7_perturbation_poly`**.")
    print()
    print("CAS-verified at `scripts/verify_d7_operator_decomp.py`: the polynomial")
    print("`septic_d7_perturbation_poly(a, b)` equals the sum of 6 operator-form")
    print("pieces (P_2, P_3, P_4, P_5, Cross(V_2,V_3), Cross(V_2,V_4)) defined above.")
    print()
    print("This is the polynomial-form Phase B-septic identity foundation. The")
    print("operator-form Phase B-septic identity (where each piece equals a specific")
    print("BCH-series expression) will be established by separate `match_scalars`")
    print("lemmas for each piece in a follow-up session. -/")
    print("private theorem septic_d7_perturbation_poly_pieces_decomp")
    print("    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]")
    print("    (a b : 𝔸) :")
    print("    septic_d7_perturbation_poly 𝕂 a b =")
    print("      septic_d7_P2_poly 𝕂 a b + septic_d7_P3_poly 𝕂 a b +")
    print("        septic_d7_P4_poly 𝕂 a b + septic_d7_P5_poly 𝕂 a b +")
    print("        septic_d7_cross_V2_V3_poly 𝕂 a b + septic_d7_cross_V2_V4_poly 𝕂 a b := by")
    print("  unfold septic_d7_perturbation_poly")
    print("        septic_d7_P2_poly septic_d7_P3_poly septic_d7_P4_poly septic_d7_P5_poly")
    print("        septic_d7_cross_V2_V3_poly septic_d7_cross_V2_V4_poly")
    print("  match_scalars <;> ring")


if __name__ == "__main__":
    main()
