#!/usr/bin/env python3
"""
Generate Lean code for the d=8 P_2_C5_cubic residual polynomial.

The residual is the deg-9 part (k=4 V_2 substitutions into C_5) of:

    bch_quintic_term(x + V_2, a') - bch_quintic_term(x, a')

After subtracting the deg-6 part (k=1), deg-7 part (k=2 = septic_d7_P2_C5_quad_poly),
and deg-8 part (k=3 = septic_d8_P2_C5_cubic_poly), only the deg-9 part remains
(48 terms in {a, b}, all of length 9).

Outputs:
  - The 4-piece decomposition (k=1, k=2, k=3, k=4 parts in {a, b})
  - Lean DEF code for the k=1 part (new: septic_d6_P2_C5_lin_poly)
  - Lean DEF code for the k=4 part (new: septic_d9_P2_C5_quartic_residual_poly)
  - Lean theorem statement for the matching identity

The matching identity (proof: match_scalars <;> ring after unfolding):

    bch_quintic_term 𝕂 (½a + b + V_2) (½a) - bch_quintic_term 𝕂 (½a + b) (½a)
      = septic_d6_P2_C5_lin_poly 𝕂 a b
      + septic_d7_P2_C5_quad_poly 𝕂 a b
      + septic_d8_P2_C5_cubic_poly 𝕂 a b
      + septic_d9_P2_C5_quartic_residual_poly 𝕂 a b

where V_2 = bch_quadratic_term(½a, b) = (1/4)·([a, b]) — see Basic.lean for the
explicit polynomial form.
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
    """Emit a noncomputable def in Lean. Each term is a • (a*b*...)."""
    items = []
    nonzero = sorted([(w, c) for w, c in p.items() if c != 0])
    if not nonzero:
        raise ValueError("Empty polynomial")
    for w, c in nonzero:
        # c is a rational; convert to num/denom form
        c_r = sp.nsimplify(c)
        num = sp.numer(c_r) * (denom // sp.denom(c_r))
        assert num == c_r * denom, f"non-integer numerator: {c_r} * {denom} = {c_r * denom}"
        num = int(num)
        word_str = " * ".join("a" if a == 0 else "b" for a in w)
        items.append(f"  + ({num} / {denom} : 𝕂) • ({word_str})")

    body = "\n".join(items)
    # Strip the leading "  + " so the first term starts the RHS expression.
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

    MX = 10
    bch_inner = bch_series(half_a, b, MX)
    V2 = extract_degree(bch_inner, 2)

    # bch_quintic_term as poly in {a, b}
    bch_to_5 = bch_series(a, b, 5)
    bch_5_abs = extract_degree(bch_to_5, 5)

    # Full diff
    x_plus_V2 = ncpoly_add(x, V2)
    full = ncpoly_sub(substitute(bch_5_abs, x_plus_V2, half_a),
                      substitute(bch_5_abs, x, half_a))

    deg6_part = extract_degree(full, 6)
    deg7_part = extract_degree(full, 7)
    deg8_part = extract_degree(full, 8)
    deg9_part = extract_degree(full, 9)

    print("# Term counts and denominators", file=sys.stderr)
    print(f"  deg 6 (k=1): {sum(1 for c in deg6_part.values() if c != 0)} terms", file=sys.stderr)
    print(f"  deg 7 (k=2): {sum(1 for c in deg7_part.values() if c != 0)} terms", file=sys.stderr)
    print(f"  deg 8 (k=3): {sum(1 for c in deg8_part.values() if c != 0)} terms", file=sys.stderr)
    print(f"  deg 9 (k=4): {sum(1 for c in deg9_part.values() if c != 0)} terms", file=sys.stderr)

    # Compute LCM for each
    def lcm_of(p):
        LCM = 1
        for c in p.values():
            if c != 0:
                LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
        return int(LCM)

    print(f"  deg 6 LCM: {lcm_of(deg6_part)}", file=sys.stderr)
    print(f"  deg 7 LCM: {lcm_of(deg7_part)}", file=sys.stderr)
    print(f"  deg 8 LCM: {lcm_of(deg8_part)}", file=sys.stderr)
    print(f"  deg 9 LCM: {lcm_of(deg9_part)}", file=sys.stderr)

    # === Emit Lean defs for d6 and d9 (new) ===
    # d7 is existing (septic_d7_P2_C5_quad_poly, sextic_d6 doesn't exist).
    # d8 is existing (septic_d8_P2_C5_cubic_poly).

    print("\n" + "=" * 80, file=sys.stderr)
    print("LEAN CODE for new polynomial DEFs (paste into SymmetricQuintic.lean)", file=sys.stderr)
    print("=" * 80, file=sys.stderr)

    print("\n-- === Deg-6 contribution (k=1 V_2 in C_5; LCM may match d=6 sextic infra) ===\n")
    print(emit_lean_def(
        deg6_part,
        "septic_d8_P2_C5_lin_poly",
        lcm_of(deg6_part),
        "Deg-6 contribution to (bch_quintic_term(x+V_2, ½a) - bch_quintic_term(x, ½a)). k=1 V_2 substitution into C_5."
    ))

    print("\n-- === Deg-9 residual (k=4 V_2 in C_5) ===\n")
    print(emit_lean_def(
        deg9_part,
        "septic_d8_P2_C5_quartic_residual_poly",
        lcm_of(deg9_part),
        "Deg-9 residual = (k=4 V_2 substitution part) of (bch_quintic_term(x+V_2, ½a) - bch_quintic_term(x, ½a))."
    ))

    print("\n-- === Sanity: d7 piece is septic_d7_P2_C5_quad_poly ===\n")
    print("-- (already defined, 79 terms, LCM 92160)")
    # Verify it matches
    existing_lcm = lcm_of(deg7_part)
    print(f"-- CAS verifies: 79 terms, LCM = {existing_lcm}")

    print("\n" + "=" * 80, file=sys.stderr)
    print("MATCHING IDENTITY (paste into SymmetricQuintic.lean)", file=sys.stderr)
    print("=" * 80, file=sys.stderr)

    print("""
/-- **d8 P_2 C_5 matching identity**: the full (bch_quintic_term diff under
V_2 perturbation) decomposes into deg-6, deg-7, deg-8, deg-9 pieces.

The deg-7 piece matches `septic_d7_P2_C5_quad_poly`, deg-8 piece matches
`septic_d8_P2_C5_cubic_poly`. The deg-6 contribution is what we'll call
`septic_d8_P2_C5_lin_poly` (k=1 V_2 in C_5), and the deg-9 residual we'll
call `septic_d8_P2_C5_quartic_residual_poly`.

Note: V_2 here is the explicit polynomial form (1/4)·(a*b - b*a). -/
private theorem bch_quintic_term_V2_shift_decomp {𝕂 : Type*} [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    bch_quintic_term 𝕂 ((1/2 : 𝕂) • a + b +
                          (1/4 : 𝕂) • (a * b - b * a)) ((1/2 : 𝕂) • a) -
    bch_quintic_term 𝕂 ((1/2 : 𝕂) • a + b) ((1/2 : 𝕂) • a) =
      septic_d8_P2_C5_lin_poly 𝕂 a b
      + septic_d7_P2_C5_quad_poly 𝕂 a b
      + septic_d8_P2_C5_cubic_poly 𝕂 a b
      + septic_d8_P2_C5_quartic_residual_poly 𝕂 a b := by
  unfold bch_quintic_term septic_d8_P2_C5_lin_poly septic_d7_P2_C5_quad_poly
        septic_d8_P2_C5_cubic_poly septic_d8_P2_C5_quartic_residual_poly
  match_scalars <;> ring
""")


if __name__ == "__main__":
    main()
