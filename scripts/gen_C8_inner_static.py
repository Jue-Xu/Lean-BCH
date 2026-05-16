#!/usr/bin/env python3
"""
Generate explicit polynomial forms for `bch_octic_term(½a, b)` and
`bch_octic_term(½a + b, ½a)`.

These are the deg-8 analogs of `C6_inner_eq` and `C6_static_eq` (Phase C
quintic pieces) at one degree higher, needed for the eventual septic
discharge Phase C-septic identity (deg-8 cancellation, analog of
`symmetric_bch_quintic_deg6_cancellation_pure_identity`).

The `bch_octic_term` def has 124 monomials in {a, b} (LCM 120960).
Substituting in (½a, b) gives a deg-8 polynomial in {a, b} with each
position taking values from {½a, b}.

Substituting in (½a+b, ½a) is more complex: each x-slot can be ½a OR b.
The resulting polynomial has up to 2^8 = 256 deg-8 words, with many
collisions due to the (½a, b) structure.

Outputs Lean code for:
    private theorem C8_inner_eq (a b : 𝔸) :
        bch_octic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b = <explicit polynomial>
    private theorem C8_static_eq (a b : 𝔸) :
        bch_octic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) = <explicit polynomial>
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


def emit_lean(poly: NCPoly, lcm: int, lhs: str, theorem_name: str,
              docstring: str, proof_body: str):
    items = sorted([(w, c) for w, c in poly.items() if c != 0],
                   key=lambda x: x[0])
    sum_abs = sum(abs(int(sp.nsimplify(c * lcm))) for _, c in items)

    print(f"-- {theorem_name}: {len(items)} terms, LCM={lcm}, Σ|num|={sum_abs}, Σ|num|/LCM ≈ {sum_abs/lcm:.4f}")
    print(f"/-- {docstring} -/")
    print(f"private theorem {theorem_name}")
    print(f"    {{𝕂 : Type*}} [RCLike 𝕂] {{𝔸 : Type*}} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]")
    print(f"    (a b : 𝔸) :")
    print(f"    {lhs} =")
    first = True
    for w, c in items:
        n = int(sp.nsimplify(c * lcm))
        word_str = ' * '.join('a' if x == 0 else 'b' for x in w)
        sign = "  " if first else "+ "
        if n < 0:
            sign = "  " if first else "- "
            n_abs = -n
            print(f"      {sign}({n_abs} / {lcm} : 𝕂) • ({word_str})")
        else:
            print(f"      {sign}({n} / {lcm} : 𝕂) • ({word_str})")
        first = False
    print(f"    := by")
    print(proof_body)


def main():
    MAX = 8
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    half_a_plus_b = ncpoly_add(half_a, b)
    # C₈(½a, b) = deg-8 of bch(½a, b)
    C8_inner = extract_degree(bch_series(half_a, b, MAX), 8)
    # C₈(½a+b, ½a) = deg-8 of bch(½a+b, ½a)
    C8_static = extract_degree(bch_series(half_a_plus_b, half_a, MAX), 8)

    # LCM of denominators across both polys.
    LCM = 1
    for c in C8_inner.values():
        if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    for c in C8_static.values():
        if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)

    # Emit C8_inner_eq.
    emit_lean(C8_inner, LCM,
              lhs="bch_octic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b",
              theorem_name="C8_inner_eq",
              docstring=("**Sub-lemma (Phase C-septic, piece 4)**: `bch_octic_term(½a, b)` "
                         f"equals an explicit deg-8 polynomial in `{{a, b}}`. CAS-derived; "
                         f"denominator {LCM}. Deg-8 analog of `C6_inner_eq` (Phase C-quintic "
                         "piece) at one degree higher.\n(Section-level `maxHeartbeats 64000000` "
                         "covers this proof.)"),
              proof_body=("  unfold bch_octic_term\n"
                          "  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,\n"
                          "             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]\n"
                          "  match_scalars <;> ring"))
    print()
    # Emit C8_static_eq.
    emit_lean(C8_static, LCM,
              lhs="bch_octic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a)",
              theorem_name="C8_static_eq",
              docstring=("**Sub-lemma (Phase C-septic, piece 5)**: `bch_octic_term(½a+b, ½a)` "
                         f"equals an explicit deg-8 polynomial in `{{a, b}}`. CAS-derived; "
                         f"denominator {LCM}. Deg-8 analog of `C6_static_eq` (Phase C-quintic "
                         "piece) at one degree higher.\n(Section-level `maxHeartbeats 64000000` "
                         "covers this proof.)"),
              proof_body=("  unfold bch_octic_term\n"
                          "  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,\n"
                          "             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]\n"
                          "  match_scalars <;> ring"))


if __name__ == "__main__":
    main()
