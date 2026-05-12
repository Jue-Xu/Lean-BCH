#!/usr/bin/env python3
"""Verify the τ⁷ matching identity at the polynomial-in-(a,b)-and-p level.

The matching identity asserts (modulo IsSuzukiCubic, i.e., 4p³+(1-4p)³ = 0):

  γ_7·E_7 + c_L_E5·[V,[V,E_5]] + c_Q_E3·[E_3,[V,E_3]] + c_L_E3_E5·[V,[V,[V,[V,E_3]]]] = R_7

where:
  V = a+b
  E_k = deg-k Taylor coefficient of log(exp(a/2)·exp(b)·exp(a/2))
        (= symmetric_bch_cubic_poly for k=3, ..._quintic_poly for k=5, etc.)
  γ_7 = 4p^7 + (1-4p)^7   (suzuki5_bch_septic_coeff)
  c_L_E5 = (1/3) p (1-4p) (1-2p) (p² - (1-4p)²) (p² + (1-4p)²)
                   (from sym_cubic_poly_linear_part_at_strangBlock_E5)
  c_Q_E3 = (1/3) p (1-4p) (2p³ + (1-4p)³) (p² - (1-4p)²)
                   (from sym_cubic_poly_quadratic_part_at_strangBlock_E3)
  c_L_E3_E5 = -(1/180) p (1-4p) (1-2p) (1-5p) (1-3p) (12p² - 6p - 1)
                   (from sym_quintic_poly_linear_part_at_strangBlock_E3, this commit)
  R_7 = order-7 BCH residual of Suzuki S₄ (computed by compute_bch_r7.py)

Both sides are polynomials in (a, b) of degree 7. Coefficients are polynomials
in p. Equality is verified by symbolically reducing each (a, b)-word
coefficient via the Suzuki cubic reduction `p³ = (48p² - 12p + 1)/60` and
checking that all are zero.
"""
import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple
import sys, os

# Import the NC poly machinery from Lean-Trotter's compute_bch_r7.py.
_LEANTROTTER_SCRIPT = os.path.join(
    os.path.dirname(__file__), '..', '..',
    'Lean-Trotter', 'scripts', 'compute_bch_r7.py'
)
with open(_LEANTROTTER_SCRIPT) as fh:
    _src = fh.read().split('def main')[0]
exec(_src, globals())


# ------- Lie commutator on NCPoly: [X, Y] := X*Y - Y*X. -------

def commBr(x: NCPoly, y: NCPoly) -> NCPoly:
    return ncpoly_sub(ncpoly_mul(x, y), ncpoly_mul(y, x))


# ------- Evaluate a polynomial-in-(a, b) at substituted NCPoly inputs. -------

def ncpoly_eval(poly: NCPoly, a_sub: NCPoly, b_sub: NCPoly) -> NCPoly:
    """Evaluate a polynomial poly(a, b) at given NCPoly inputs.

    Each word w = (w_0, w_1, ..., w_{n-1}) becomes the product
    `s_{w_0} * s_{w_1} * ... * s_{w_{n-1}}` where s_0 = a_sub, s_1 = b_sub.
    """
    result = ncpoly_zero()
    for word, coef in poly.items():
        if coef == 0:
            continue
        term = ncpoly_from_scalar(1)
        for letter in word:
            sub = a_sub if letter == 0 else b_sub
            term = ncpoly_mul(term, sub)
        result = ncpoly_add(result, ncpoly_scale(term, coef))
    return result


# ------- Main: compute LHS and RHS, verify. -------

def main():
    print("=" * 75)
    print("τ⁷ matching identity verification (modulo IsSuzukiCubic)")
    print("=" * 75)

    p = sp.Symbol('p')

    # E_3, E_5, E_7 = symmetric BCH coefficients (deg-3, 5, 7 of log of strang block).
    # Compute strang_block_series(1, 7), then take log_one_plus, and extract deg-k parts.
    print("\nComputing symmetric BCH coefficients (E_3, E_5, E_7) ...")
    sb1 = strang_block_series(sp.Integer(1), 7)
    # y = sb1 - 1
    y = defaultdict(lambda: sp.Integer(0), {w: c for w, c in sb1.items() if w != ()})
    log_sb = ncpoly_log_one_plus(y, 7)

    E_3 = extract_degree(log_sb, 3)
    E_5 = extract_degree(log_sb, 5)
    E_7 = extract_degree(log_sb, 7)

    print(f"  E_3 has {len(E_3)} non-zero 3-letter words.")
    print(f"  E_5 has {len(E_5)} non-zero 5-letter words.")
    print(f"  E_7 has {len(E_7)} non-zero 7-letter words.")

    # V = a + b
    V = ncpoly_add(ncpoly_a(), ncpoly_b())

    # Compute the three commutator pieces.
    print("\nComputing commutator pieces ...")

    # [V, [V, E_5]] -- deg-7 in (a, b).
    VV_E5 = commBr(V, commBr(V, E_5))
    print(f"  [V, [V, E_5]] has {len(VV_E5)} non-zero 7-letter words.")

    # [E_3, [V, E_3]] -- deg-7.
    E3_V_E3 = commBr(E_3, commBr(V, E_3))
    print(f"  [E_3, [V, E_3]] has {len(E3_V_E3)} non-zero 7-letter words.")

    # [V, [V, [V, [V, E_3]]]] -- deg-7.
    ad_V4_E3 = commBr(V, commBr(V, commBr(V, commBr(V, E_3))))
    print(f"  [V, [V, [V, [V, E_3]]]] has {len(ad_V4_E3)} non-zero 7-letter words.")

    # γ_7 = 4p^7 + (1-4p)^7  (the bch septic coeff)
    gamma_7 = 4*p**7 + (1 - 4*p)**7

    # Closed-form coefficients.
    c_L_E5 = sp.Rational(1, 3) * p * (1 - 4*p) * (1 - 2*p) * (p**2 - (1 - 4*p)**2) * (p**2 + (1 - 4*p)**2)
    c_Q_E3 = sp.Rational(1, 3) * p * (1 - 4*p) * (2*p**3 + (1 - 4*p)**3) * (p**2 - (1 - 4*p)**2)
    c_L_E3_E5 = -sp.Rational(1, 180) * p * (1 - 4*p) * (1 - 2*p) * (1 - 5*p) * (1 - 3*p) * (12*p**2 - 6*p - 1)

    print(f"\nClosed-form coefficients:")
    print(f"  γ_7         = {sp.expand(gamma_7)}")
    print(f"  c_L_E5      = {sp.expand(c_L_E5)}")
    print(f"  c_Q_E3      = {sp.expand(c_Q_E3)}")
    print(f"  c_L_E3_E5   = {sp.expand(c_L_E3_E5)}")

    # Build LHS = γ_7·E_7 + c_L_E5·[V,[V,E_5]] + c_Q_E3·[E_3,[V,E_3]] + c_L_E3_E5·ad_V^4(E_3)
    LHS = ncpoly_scale(E_7, gamma_7)
    LHS = ncpoly_add(LHS, ncpoly_scale(VV_E5, c_L_E5))
    LHS = ncpoly_add(LHS, ncpoly_scale(E3_V_E3, c_Q_E3))
    LHS = ncpoly_add(LHS, ncpoly_scale(ad_V4_E3, c_L_E3_E5))
    print(f"\n  LHS has {len(LHS)} non-zero 7-letter words (before Suzuki reduction).")

    # Build RHS = R_7 (the order-7 BCH residual of Suzuki S_4).
    print("\nComputing R_7 = order-7 BCH residual of Suzuki S₄ ...")
    print("(This takes a few minutes for full deg-7 expansion ...)")
    residual = log_s4_residual(p, max_degree=7)
    R_7 = extract_degree(residual, 7)
    print(f"  R_7 has {len(R_7)} non-zero 7-letter words (before Suzuki reduction).")

    # Compute LHS - R_7.
    diff = ncpoly_sub(LHS, R_7)
    print(f"\n  LHS - R_7 has {len(diff)} non-zero 7-letter words (before Suzuki reduction).")

    # Apply Suzuki cubic reduction to each word's coefficient.
    print("\nApplying Suzuki cubic reduction p^3 = (48p² - 12p + 1)/60 ...")
    nz_after_reduction = 0
    nonzero_words = []
    for w, c in sorted(diff.items()):
        c_red = simplify_under_suzuki(c, p)
        if c_red != 0:
            nz_after_reduction += 1
            nonzero_words.append((w, c_red))

    print(f"\n  After Suzuki reduction: {nz_after_reduction} non-zero words.")

    if nz_after_reduction == 0:
        print("\n" + "=" * 75)
        print("✓ τ⁷ MATCHING IDENTITY HOLDS (modulo IsSuzukiCubic).")
        print("=" * 75)
        print("\nThe matching identity is verified at the polynomial-in-(a,b) level.")
    else:
        print("\n" + "=" * 75)
        print("✗ MISMATCH: τ⁷ matching identity does NOT hold.")
        print("=" * 75)
        print("\nFirst 10 mismatched (word, residual) pairs:")
        for w, c in nonzero_words[:10]:
            word_str = ''.join('a' if x == 0 else 'b' for x in w)
            print(f"  {word_str}: {c}")
        if len(nonzero_words) > 10:
            print(f"  ... ({len(nonzero_words) - 10} more)")


if __name__ == "__main__":
    main()
