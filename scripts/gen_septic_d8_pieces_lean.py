#!/usr/bin/env python3
"""
Generate Lean DEFs for the 9 operator-form pieces of septic_d8_perturbation_poly:

  septic_d8_perturbation_poly
    = septic_d8_P2_poly + septic_d8_P3_poly + septic_d8_P4_poly
      + septic_d8_P5_poly + septic_d8_P6_poly
      + septic_d8_cross_V2_V3_poly + septic_d8_cross_V2_V4_poly
      + septic_d8_cross_V2_V5_poly + septic_d8_cross_V3_V4_poly

CAS-verified at `scripts/verify_d8_operator_decomp.py`. Each piece is an
explicit polynomial in {a, b} with rational coefficients.

This script outputs Lean source code for:
  • 9 noncomputable defs (each piece as an explicit polynomial).
  • 1 theorem `septic_d8_perturbation_poly_pieces_decomp` stating the sum
    of the 9 pieces equals septic_d8_perturbation_poly.

The theorem's proof is `unfold + match_scalars <;> ring` (each piece's def
unfolds to its explicit polynomial form, then ring closes the goal).

d8 analog of `gen_septic_d7_pieces_lean.py` at one degree higher: 9 pieces
(5 single + 4 cross) instead of 6 (4 single + 2 cross). The structural
derivation appears in CLAUDE.md session 47.
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

    MX = 8
    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)
    V6 = extract_degree(bch_inner, 6)

    bch_static = bch_series(x, half_a, MX)

    P2 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V2), half_a, MX), bch_static), 8)
    P3 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V3), half_a, MX), bch_static), 8)
    P4 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V4), half_a, MX), bch_static), 8)
    P5 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V5), half_a, MX), bch_static), 8)
    P6 = extract_degree(ncpoly_sub(bch_series(ncpoly_add(x, V6), half_a, MX), bch_static), 8)

    cross_23 = cross(x, V2, V3, half_a, MX, 8)
    cross_24 = cross(x, V2, V4, half_a, MX, 8)
    cross_25 = cross(x, V2, V5, half_a, MX, 8)
    cross_34 = cross(x, V3, V4, half_a, MX, 8)

    print("/-! ## 9-piece operator-form decomposition of septic_d8_perturbation_poly")
    print()
    print("From CAS verification (`scripts/verify_d8_operator_decomp.py`):")
    print()
    print("    septic_d8_perturbation_poly")
    print("      = septic_d8_P2_poly + septic_d8_P3_poly + septic_d8_P4_poly")
    print("        + septic_d8_P5_poly + septic_d8_P6_poly")
    print("        + septic_d8_cross_V2_V3_poly + septic_d8_cross_V2_V4_poly")
    print("        + septic_d8_cross_V2_V5_poly + septic_d8_cross_V3_V4_poly")
    print()
    print("Each piece corresponds to a specific operator-form perturbation:")
    print("  • P_j := (bch(x + V_j, ½a) − bch(x, ½a))_deg8  (single-V_j perturbation).")
    print("  • Cross(V_j, V_k) := (bch(x+V_j+V_k, ½a) − bch(x+V_j, ½a)")
    print("                       − bch(x+V_k, ½a) + bch(x, ½a))_deg8  (mixed cross).")
    print()
    print("d8 analog of the 6-piece d7 decomposition. Three potential cross pieces")
    print("(Cross(V_2,V_6), Cross(V_3,V_5), Cross(V_4,V_5)) vanish at deg 8 because")
    print("the required C_p with p+(j-1)+(k-1) = 8 and j,k ≥ 3 forces p ≤ 2, but")
    print("C_2 has only 1 z-position and cannot admit bilinear substitution.")
    print()
    print("Foundation for the Phase C-septic operator-form identity (eventual O(s⁹)")
    print("joint bound replacing the current O(s⁸) per-piece bound on")
    print("septic_d8_perturbation_poly via Lipschitz bounds on each operator form).")
    print("-/")
    print()

    emit_def("septic_d8_P2_poly",
             "V_2-only deg-8 perturbation piece (P_2_d8). Captures linear-in-V_2 "
             "from C_7, quadratic-in-V_2 from C_6, and cubic V_2³ from C_5.", P2)
    emit_def("septic_d8_P3_poly",
             "V_3-only deg-8 perturbation piece (P_3_d8). Captures linear-in-V_3 "
             "from C_6 and quadratic-in-V_3 from C_4.", P3)
    emit_def("septic_d8_P4_poly",
             "V_4-only deg-8 perturbation piece (P_4_d8). Captures only linear-in-V_4 "
             "from C_5 (higher-order V_4 contributions exceed deg 8).", P4)
    emit_def("septic_d8_P5_poly",
             "V_5-only deg-8 perturbation piece (P_5_d8). Captures only linear-in-V_5 "
             "from C_4 (higher-order V_5 contributions exceed deg 8).", P5)
    emit_def("septic_d8_P6_poly",
             "V_6-only deg-8 perturbation piece (P_6_d8). Captures only linear-in-V_6 "
             "from C_3 (higher-order V_6 contributions exceed deg 8).", P6)
    emit_def("septic_d8_cross_V2_V3_poly",
             "V_2·V_3 cross deg-8 perturbation piece. Bilinear V_2·V_3 from C_5 "
             "(deg 3 + 1 + 2 + 2 = 8 from a length-5 nested-bracket with two z-positions).",
             cross_23)
    emit_def("septic_d8_cross_V2_V4_poly",
             "V_2·V_4 cross deg-8 perturbation piece. Bilinear V_2·V_4 from C_4 "
             "(deg 2 + 1 + 1 + 4 = 8).", cross_24)
    emit_def("septic_d8_cross_V2_V5_poly",
             "V_2·V_5 cross deg-8 perturbation piece. Bilinear V_2·V_5 from C_3 "
             "(deg 1 + 2 + 5 = 8).", cross_25)
    emit_def("septic_d8_cross_V3_V4_poly",
             "V_3·V_4 cross deg-8 perturbation piece. Bilinear V_3·V_4 from C_3 "
             "(deg 1 + 3 + 4 = 8).", cross_34)

    print("/-- **9-piece decomposition of `septic_d8_perturbation_poly`**.")
    print()
    print("CAS-verified at `scripts/verify_d8_operator_decomp.py`: the polynomial")
    print("`septic_d8_perturbation_poly(a, b)` equals the sum of 9 operator-form")
    print("pieces (P_2, P_3, P_4, P_5, P_6, Cross(V_2,V_3), Cross(V_2,V_4),")
    print("Cross(V_2,V_5), Cross(V_3,V_4)) defined above.")
    print()
    print("This is the polynomial-form Phase C-septic identity foundation, parallel")
    print("to `septic_d7_perturbation_poly_pieces_decomp`. The operator-form")
    print("Phase C-septic identity (where each piece equals a specific BCH-series")
    print("expression) will be established by separate `match_scalars` lemmas for")
    print("each piece in a follow-up session.")
    print()
    print("(Section-level `maxHeartbeats 64000000` covers this proof.) -/")
    print("private theorem septic_d8_perturbation_poly_pieces_decomp")
    print("    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]")
    print("    (a b : 𝔸) :")
    print("    septic_d8_perturbation_poly 𝕂 a b =")
    print("      septic_d8_P2_poly 𝕂 a b + septic_d8_P3_poly 𝕂 a b +")
    print("        septic_d8_P4_poly 𝕂 a b + septic_d8_P5_poly 𝕂 a b +")
    print("        septic_d8_P6_poly 𝕂 a b +")
    print("        septic_d8_cross_V2_V3_poly 𝕂 a b + septic_d8_cross_V2_V4_poly 𝕂 a b +")
    print("        septic_d8_cross_V2_V5_poly 𝕂 a b + septic_d8_cross_V3_V4_poly 𝕂 a b := by")
    print("  unfold septic_d8_perturbation_poly")
    print("        septic_d8_P2_poly septic_d8_P3_poly septic_d8_P4_poly")
    print("        septic_d8_P5_poly septic_d8_P6_poly")
    print("        septic_d8_cross_V2_V3_poly septic_d8_cross_V2_V4_poly")
    print("        septic_d8_cross_V2_V5_poly septic_d8_cross_V3_V4_poly")
    print("  match_scalars <;> ring")


if __name__ == "__main__":
    main()
