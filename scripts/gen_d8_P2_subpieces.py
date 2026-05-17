#!/usr/bin/env python3
"""
Generate Lean DEFs for the 3 sub-pieces of septic_d8_P2_poly:

  septic_d8_P2_poly = septic_d8_P2_C5_cubic_poly
                    + septic_d8_P2_C6_quad_poly
                    + septic_d8_P2_C7_lin_poly

where:
  • C_5 cubic-in-V_2 sub-piece (deg 5 + 3·(2-1) = 8): the deg-8 part of
    bch_quintic_term(x + V_2, ½a) - bch_quintic_term(x, ½a).
  • C_6 quadratic-in-V_2 sub-piece (deg 6 + 2·(2-1) = 8): the deg-8 part of
    bch_sextic_term(x + V_2, ½a) - bch_sextic_term(x, ½a).
  • C_7 linear-in-V_2 sub-piece (deg 7 + 1·(2-1) = 8): the deg-8 part of
    bch_septic_term(x + V_2, ½a) - bch_septic_term(x, ½a).

None of the 3 sub-pieces are Dynkin-expressible in Lean (bch_quintic_term,
bch_sextic_term, bch_septic_term are all monomial form in Lean, not Dynkin
Lie polynomials). All 3 will need Lipschitz-style bounds.

d8 analog of `scripts/verify_P2_decomp.py` (d7 P_2 has only 2 sub-pieces:
C_5 quad + C_6 lin, since at d7 cubic-in-V_2 from C_4 is impossible —
C_4 has only 2 z-positions but cubic requires 3 substitutions).

Extraction method: each sub-piece is computed INDEPENDENTLY from its
specific bch_kth_term:
  - bch_kth_term(x + V_2, a') - bch_kth_term(x, a') reduced to deg 8 gives
    the "k V_2-substitutions" contribution exclusively (since 0-V_2 gives
    deg k < 8 and >k V_2's gives deg > 8, the only deg-8 contribution is
    (k mod) at k-V_2 substitutions... wait the relation is k + (subs) = 8).
  - For k=5: 3 V_2 subs.
  - For k=6: 2 V_2 subs.
  - For k=7: 1 V_2 sub.

This gives 3 independent extractions, which we verify sum to P_2_d8 (computed
via the FULL bch series).

Outputs:
  1. The 3 sub-piece polynomial defs (CAS-extracted, independent).
  2. The sum identity theorem `septic_d8_P2_pieces_decomp`.

Term count expectations (CAS-derived):
  • C_5 cubic: cubic in V_2 = [a',b]/2. Smallest of the 3.
  • C_6 quad: quadratic in V_2. Medium.
  • C_7 lin: linear in V_2. Largest.
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
    """BCH series in (x, y). x and y must be poly arguments (typically ncpoly_a() and ncpoly_b())."""
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def substitute(p, sub_a, sub_b):
    """Substitute atom 0 with sub_a and atom 1 with sub_b in poly p.
    p has atoms {0, 1}; sub_a and sub_b are polys (possibly in {0, 1}).
    Result has atoms {0, 1} (after the substitution chain)."""
    result = ncpoly_zero()
    for word, coef in p.items():
        prod = ncpoly_from_scalar(1)
        for atom in word:
            sub_poly = sub_a if atom == 0 else sub_b
            prod = ncpoly_mul(prod, sub_poly)
        result = ncpoly_add(result, ncpoly_scale(prod, coef))
    return result


def ncpoly_diff(p, q):
    r = ncpoly_zero()
    keys = set(p.keys()) | set(q.keys())
    for w in keys:
        d = sp.nsimplify(p.get(w, 0) - q.get(w, 0))
        if d != 0:
            r[w] = d
    return r


def summarize(p, label):
    import sys
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
    import sys
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
    import sys

    # Setup
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)

    # V_2 = (1/2)·[½a, b] = ½·(½a·b - b·½a)
    V2 = ncpoly_scale(ncpoly_bracket(half_a, b), half)
    summarize(V2, "V_2 (= (1/2)·[½a, b])")

    # x + V_2
    x_plus_V2 = ncpoly_add(x, V2)

    # Compute bch_kth_term for k = 5, 6, 7 as abstract polynomials in (z, y) = (a, b).
    # Using bch_series(a, b, k) and extracting degree k.
    bch_full = bch_series(a, b, 7)
    bch_5_abstract = extract_degree(bch_full, 5)
    bch_6_abstract = extract_degree(bch_full, 6)
    bch_7_abstract = extract_degree(bch_full, 7)
    summarize(bch_5_abstract, "bch_quintic_term abstract")
    summarize(bch_6_abstract, "bch_sextic_term abstract")
    summarize(bch_7_abstract, "bch_septic_term abstract")

    # Extract each sub-piece via substitution and deg-8 extraction.

    # C_7 lin: extract_deg(bch_septic_term(x + V_2, ½a) - bch_septic_term(x, ½a), 8)
    bch_7_at_xV2 = substitute(bch_7_abstract, x_plus_V2, half_a)
    bch_7_at_x = substitute(bch_7_abstract, x, half_a)
    C7_lin = extract_degree(ncpoly_sub(bch_7_at_xV2, bch_7_at_x), 8)
    summarize(C7_lin, "C_7 lin")

    # C_6 quad: extract_deg(bch_sextic_term(x + V_2, ½a) - bch_sextic_term(x, ½a), 8)
    bch_6_at_xV2 = substitute(bch_6_abstract, x_plus_V2, half_a)
    bch_6_at_x = substitute(bch_6_abstract, x, half_a)
    C6_quad = extract_degree(ncpoly_sub(bch_6_at_xV2, bch_6_at_x), 8)
    summarize(C6_quad, "C_6 quad")

    # C_5 cubic: extract_deg(bch_quintic_term(x + V_2, ½a) - bch_quintic_term(x, ½a), 8)
    bch_5_at_xV2 = substitute(bch_5_abstract, x_plus_V2, half_a)
    bch_5_at_x = substitute(bch_5_abstract, x, half_a)
    C5_cubic = extract_degree(ncpoly_sub(bch_5_at_xV2, bch_5_at_x), 8)
    summarize(C5_cubic, "C_5 cubic")

    # Cross-check: total should equal septic_d8_P2_poly = (bch(x + V_2, ½a) - bch(x, ½a))_d8
    bch_static = bch_series(x, half_a, 8)
    bch_at_xV2 = bch_series(x_plus_V2, half_a, 8)
    P2_d8 = extract_degree(ncpoly_sub(bch_at_xV2, bch_static), 8)
    summarize(P2_d8, "P_2_d8 (direct)")

    total = ncpoly_add(ncpoly_add(C5_cubic, C6_quad), C7_lin)
    summarize(total, "Sum (C_5_cubic + C_6_quad + C_7_lin)")

    diff = ncpoly_diff(total, P2_d8)
    nz = sum(1 for c in diff.values() if c != 0)
    if nz == 0:
        print("✓ VERIFIED: septic_d8_P2_poly = C_5_cubic + C_6_quad + C_7_lin", file=sys.stderr)
    else:
        print(f"✗ MISMATCH: differ by {nz} terms", file=sys.stderr)
        for w, c in list(diff.items())[:5]:
            if c != 0:
                word = ''.join('a' if x == 0 else 'b' for x in w)
                print(f"   {sp.nsimplify(c)} · {word}", file=sys.stderr)
        return

    # Emit Lean code
    print("/-! ### Sub-piece decomposition of `septic_d8_P2_poly`")
    print()
    print("P_2_d8 = (bch(x + V_2, ½a) - bch(x, ½a))_deg8 splits into 3 sub-pieces.")
    print("At deg 8 with V_2 = (1/2)·[½a, b] (deg 2), the contributions come from")
    print("C_p substitutions with k V_2's such that p + k = 8 and k ≤ #z-positions in C_p:")
    print("  • C_7 linear-in-V_2 (k=1, p=7): bch_septic_term(x+V_2, a') - bch_septic_term(x, a') at deg 8.")
    print("  • C_6 quadratic-in-V_2 (k=2, p=6): bch_sextic_term(x+V_2, a') - bch_sextic_term(x, a') at deg 8.")
    print("  • C_5 cubic-in-V_2 (k=3, p=5): bch_quintic_term(x+V_2, a') - bch_quintic_term(x, a') at deg 8.")
    print()
    print("Higher k impossible: C_p with p ≤ 4 has ≤ 2 z-positions, can't accept k ≥ 4 substitutions.")
    print()
    print("d8 analog of `septic_d7_P2_pieces_decomp` (d7 has only 2 sub-pieces:")
    print("C_5 quad + C_6 lin, since cubic-in-V_2 at d7 requires p+3=7 → p=4 with 3 z-positions,")
    print("but C_4 has only 2 z-positions).")
    print()
    print("None of these 3 sub-pieces are Dynkin-expressible (bch_quintic_term/sextic_term/")
    print("septic_term are all monomial form in Lean). All need Lipschitz-style bounds.")
    print()
    print("CAS-derived: `scripts/gen_d8_P2_subpieces.py`. Each piece extracted independently")
    print("from its specific bch_kth_term, with sum verified to match P_2_d8.")
    print("-/")
    print()

    emit_def("septic_d8_P2_C7_lin_poly",
             "C_7 linear-in-V_2 part of P_2_d8 at deg 8. Equals the deg-8 part of "
             "bch_septic_term(x + V_2, ½a) - bch_septic_term(x, ½a) where "
             "V_2 = (1/2)·[½a, b], x = ½a + b, a' = ½a.",
             C7_lin)
    emit_def("septic_d8_P2_C6_quad_poly",
             "C_6 quadratic-in-V_2 part of P_2_d8 at deg 8. Equals the deg-8 part of "
             "bch_sextic_term(x + V_2, ½a) - bch_sextic_term(x, ½a).",
             C6_quad)
    emit_def("septic_d8_P2_C5_cubic_poly",
             "C_5 cubic-in-V_2 part of P_2_d8 at deg 8. Equals the deg-8 part of "
             "bch_quintic_term(x + V_2, ½a) - bch_quintic_term(x, ½a).",
             C5_cubic)

    print("/-- **3-piece sub-decomposition of `septic_d8_P2_poly`**.")
    print()
    print("CAS-verified: septic_d8_P2_poly = septic_d8_P2_C7_lin_poly +")
    print("septic_d8_P2_C6_quad_poly + septic_d8_P2_C5_cubic_poly. None of the 3")
    print("sub-pieces are Dynkin-expressible (all use bch_kth_term in monomial form")
    print("for k ≥ 5), so they will need Lipschitz-style operator-form bounds in the")
    print("eventual joint analysis. -/")
    print("private theorem septic_d8_P2_pieces_decomp")
    print("    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]")
    print("    (a b : 𝔸) :")
    print("    septic_d8_P2_poly 𝕂 a b =")
    print("      septic_d8_P2_C7_lin_poly 𝕂 a b +")
    print("        septic_d8_P2_C6_quad_poly 𝕂 a b + septic_d8_P2_C5_cubic_poly 𝕂 a b := by")
    print("  unfold septic_d8_P2_poly septic_d8_P2_C7_lin_poly")
    print("        septic_d8_P2_C6_quad_poly septic_d8_P2_C5_cubic_poly")
    print("  match_scalars <;> ring")


if __name__ == "__main__":
    main()
