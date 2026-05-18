#!/usr/bin/env python3
"""
Generate Lean code for the d=8 P_2_C6_quad matching identity.

The C_6 + V_2 perturbation expansion has 4 degree contributions:
  k=1, deg 7: septic_d7_P2_C6_lin_poly (existing, session 46)
  k=2, deg 8: septic_d8_P2_C6_quad_poly (existing, session 51)
  k=3, deg 9: septic_d8_P2_C6_cubic_residual_poly (NEW; 120 terms)
  k=4, deg 10: septic_d8_P2_C6_quartic_residual_poly (NEW; 74 terms)

Matching identity (proof via `unfold + simp + match_scalars <;> ring`):
    bch_sextic_term(½a + b + V_2, ½a) − bch_sextic_term(½a + b, ½a)
      = septic_d7_P2_C6_lin_poly
      + septic_d8_P2_C6_quad_poly
      + septic_d8_P2_C6_cubic_residual_poly
      + septic_d8_P2_C6_quartic_residual_poly

where V_2 inlined as (1/4)·(a·b − b·a).
"""

import sympy as sp
from collections import defaultdict
import sys


def ncpoly_zero(): return defaultdict(lambda: sp.Integer(0))
def ncpoly_from_scalar(c):
    r = ncpoly_zero(); c = sp.sympify(c)
    if c != 0: r[()] = c
    return r
def ncpoly_a(): r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r
def ncpoly_b(): r = ncpoly_zero(); r[(1,)] = sp.Integer(1); return r
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
def substitute(p, sub_a, sub_b):
    result = ncpoly_zero()
    for word, coef in p.items():
        prod = ncpoly_from_scalar(1)
        for atom in word:
            sub_poly = sub_a if atom == 0 else sub_b
            prod = ncpoly_mul(prod, sub_poly)
        result = ncpoly_add(result, ncpoly_scale(prod, coef))
    return result


def emit_lean_def(p, name, denom, doc):
    items = []
    nonzero = sorted([(w, c) for w, c in p.items() if c != 0])
    for w, c in nonzero:
        c_r = sp.nsimplify(c)
        num = sp.numer(c_r) * (denom // sp.denom(c_r))
        assert num == c_r * denom
        num = int(num)
        word_str = " * ".join("a" if a == 0 else "b" for a in w)
        items.append(f"  + ({num} / {denom} : 𝕂) • ({word_str})")
    body = "\n".join(items)
    if body.startswith("  + "):
        body = "    " + body[4:]
    return f"""/-- {doc} -/
noncomputable def {name} (𝕂 : Type*) [RCLike 𝕂]
    {{𝔸 : Type*}} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
{body}
"""


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)
    MX = 12
    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)

    bch_to_6 = bch_series(a, b, 6)
    bch_6_abs = extract_degree(bch_to_6, 6)

    x_plus_V2 = ncpoly_add(x, V2)
    full = ncpoly_sub(substitute(bch_6_abs, x_plus_V2, half_a),
                      substitute(bch_6_abs, x, half_a))

    deg7_part  = extract_degree(full, 7)
    deg8_part  = extract_degree(full, 8)
    deg9_part  = extract_degree(full, 9)
    deg10_part = extract_degree(full, 10)

    def lcm_of(p):
        LCM = 1
        for c in p.values():
            if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
        return int(LCM)

    print(f"# deg-7 terms: {sum(1 for c in deg7_part.values() if c != 0)}, LCM = {lcm_of(deg7_part)}", file=sys.stderr)
    print(f"# deg-8 terms: {sum(1 for c in deg8_part.values() if c != 0)}, LCM = {lcm_of(deg8_part)}", file=sys.stderr)
    print(f"# deg-9 terms: {sum(1 for c in deg9_part.values() if c != 0)}, LCM = {lcm_of(deg9_part)}", file=sys.stderr)
    print(f"# deg-10 terms: {sum(1 for c in deg10_part.values() if c != 0)}, LCM = {lcm_of(deg10_part)}", file=sys.stderr)

    # Emit the deg-9 def
    print("-- === Deg-9 residual (k=3 V_2 in C_6) ===\n")
    print(emit_lean_def(
        deg9_part,
        "septic_d8_P2_C6_cubic_residual_poly",
        lcm_of(deg9_part),
        "Deg-9 residual = (k=3 V_2 substitution part) of "
        "(bch_sextic_term(x+V_2, ½a) - bch_sextic_term(x, ½a)). 120 terms."
    ))

    # Emit the deg-10 def
    print("\n-- === Deg-10 residual (k=4 V_2 in C_6) ===\n")
    print(emit_lean_def(
        deg10_part,
        "septic_d8_P2_C6_quartic_residual_poly",
        lcm_of(deg10_part),
        "Deg-10 residual = (k=4 V_2 substitution part) of "
        "(bch_sextic_term(x+V_2, ½a) - bch_sextic_term(x, ½a)). 74 terms."
    ))

    # Emit the matching identity
    print("\n-- === Matching identity ===\n")
    print("""/-- **d8 P_2 C_6 matching identity**: the full bch_sextic_term diff under
V_2 perturbation decomposes into deg-7, deg-8, deg-9, deg-10 pieces. The
deg-7 piece matches `septic_d7_P2_C6_lin_poly` (session 46) and the deg-8
piece matches `septic_d8_P2_C6_quad_poly` (session 51).

C_6 has up to 6 z-positions, but the bch_sextic_term def has at most 4 a's
per word, so the deg-11 (k=5) and deg-12 (k=6) contributions vanish. -/
private theorem bch_sextic_term_V2_shift_decomp
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    bch_sextic_term 𝕂 ((1/2 : 𝕂) • a + b +
                         (1/4 : 𝕂) • (a * b - b * a)) ((1/2 : 𝕂) • a) -
    bch_sextic_term 𝕂 ((1/2 : 𝕂) • a + b) ((1/2 : 𝕂) • a) =
      septic_d7_P2_C6_lin_poly 𝕂 a b
      + septic_d8_P2_C6_quad_poly 𝕂 a b
      + septic_d8_P2_C6_cubic_residual_poly 𝕂 a b
      + septic_d8_P2_C6_quartic_residual_poly 𝕂 a b := by
  unfold bch_sextic_term septic_d7_P2_C6_lin_poly septic_d8_P2_C6_quad_poly
        septic_d8_P2_C6_cubic_residual_poly septic_d8_P2_C6_quartic_residual_poly
  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,
             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  match_scalars <;> ring
""")


if __name__ == "__main__":
    main()
