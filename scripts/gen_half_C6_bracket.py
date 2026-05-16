#!/usr/bin/env python3
"""
Generate the explicit polynomial form of `½·[bch_sextic_term(½a, b), ½a]`,
the deg-7 analog of `half_C4_bracket_eq` (Phase B-quintic piece).

Used in the Phase B-septic identity (`symmetric_bch_septic_deg7_cancellation_pure_identity`).

Outputs Lean code for:
    set_option maxHeartbeats 16000000 in
    private theorem half_C6_bracket_eq (a b : 𝔸) :
        (2 : 𝕂)⁻¹ • (bch_sextic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b * ((2 : 𝕂)⁻¹ • a) -
                      ((2 : 𝕂)⁻¹ • a) * bch_sextic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b) =
          <explicit polynomial in {a, b}, deg 7>

The proof strategy mirrors `half_C4_bracket_eq`: `unfold bch_sextic_term` then
`simp only [smul/mul distribution]` then `match_scalars <;> ring`.
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
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in p.items() if len(w) == k})


def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def main():
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    # C₆(½a, b) = deg-6 of bch(½a, b).
    z = bch_series(half_a, b, 6)
    C6_inner = extract_degree(z, 6)
    # ½·[C₆(½a, b), ½a] = ½·(C₆·½a − ½a·C₆) — deg-7 polynomial in {a, b}.
    bracket = ncpoly_sub(ncpoly_mul(C6_inner, half_a), ncpoly_mul(half_a, C6_inner))
    half_bracket = ncpoly_scale(bracket, half)

    # Sanity: should all be degree-7 words.
    for w, c in half_bracket.items():
        assert len(w) == 7, f"unexpected degree {len(w)} for word {w}"

    # Find LCM of denominators.
    LCM = 1
    for c in half_bracket.values():
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)

    items = sorted([(w, c) for w, c in half_bracket.items() if c != 0],
                   key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)

    print(f"-- {len(items)} terms, LCM = {LCM}, Σ|num| = {sum_abs}")
    print(f"-- Σ|num|/LCM ≈ {sum_abs/LCM:.4f}")
    print()
    print("/-- **Sub-lemma (Phase B-septic, piece for ½·[C₆(½a, b), ½a])**:")
    print("`½·[bch_sextic_term(½a, b), ½a]` equals an explicit deg-7 polynomial in")
    print(f"`{{a, b}}`. CAS-derived: denominator {LCM}, {len(items)} terms.")
    print()
    print("Deg-7 analog of `half_C4_bracket_eq` (quintic Phase B piece for")
    print("`½·[bch_quartic_term(½a, b), ½a]`) at one degree higher. -/")
    print("set_option maxHeartbeats 16000000 in")
    print("private theorem half_C6_bracket_eq")
    print("    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]")
    print("    (a b : 𝔸) :")
    print("    (2 : 𝕂)⁻¹ • (bch_sextic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b * ((2 : 𝕂)⁻¹ • a) -")
    print("                  ((2 : 𝕂)⁻¹ • a) * bch_sextic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b) =")
    first = True
    for w, c in items:
        n = int(sp.nsimplify(c * LCM))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        if first:
            print(f"      ({n} / {LCM} : 𝕂) • ({word_str})")
            first = False
        else:
            print(f"    + ({n} / {LCM} : 𝕂) • ({word_str})")
    print("    := by")
    print("  unfold bch_sextic_term")
    print("  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,")
    print("             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]")
    print("  match_scalars <;> ring")


if __name__ == "__main__":
    main()
