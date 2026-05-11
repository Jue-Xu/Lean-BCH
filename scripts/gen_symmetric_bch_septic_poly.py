#!/usr/bin/env python3
"""Generate the Lean def for `symmetric_bch_septic_poly` — the τ⁷ Taylor
coefficient of `log(exp(a/2)·exp(b)·exp(a/2))` (3-factor Strang block).

This is the deg-7 analog of `symmetric_bch_quintic_poly` (which is in
BCH/SymmetricQuintic.lean for deg-5).

CAS source: `Lean-Trotter/scripts/compute_bch_r7.py` (provides the NCPoly
machinery and `strang_block_series`).
"""
import sys, os
import sympy as sp
from collections import defaultdict
import math

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..',
                                'Lean-Trotter', 'scripts'))
with open(os.path.join(os.path.dirname(__file__), '..', '..',
                       'Lean-Trotter', 'scripts', 'compute_bch_r7.py')) as fh:
    exec(fh.read().split('def main')[0], globals())


def main():
    print("Computing symmetric_bch_septic_poly via strang_block_series(1, 7) + log...")
    sb = strang_block_series(1, 7)
    sb_minus_one = defaultdict(lambda: sp.Integer(0), {w: c for w, c in sb.items() if w != ()})
    ls = ncpoly_log_one_plus(sb_minus_one, 7)
    sept = extract_degree(ls, 7)

    items = sorted(sept.items())
    print(f"Non-zero 7-letter words: {len(items)}")

    # Find LCM of denominators
    denoms = set()
    for _, c in items:
        if c != 0:
            denoms.add(int(c.q if hasattr(c, 'q') else c.as_numer_denom()[1]))
    lcm = 1
    for d in denoms:
        lcm = lcm * d // math.gcd(lcm, d)
    print(f"LCM of denominators: {lcm}")

    # Sum of |numerators|/LCM as a sanity check for the norm bound.
    abs_sum = sp.Integer(0)
    for _, c in items:
        if c != 0:
            num = c.p if hasattr(c, 'p') else c.as_numer_denom()[0]
            denom = c.q if hasattr(c, 'q') else c.as_numer_denom()[1]
            abs_sum += sp.Abs(sp.Rational(num, denom))
    print(f"Σ|coef| ≈ {float(abs_sum):.6f} (so norm bound K·s⁷ with K = {float(abs_sum)})")

    # Output Lean code
    print()
    print("=" * 70)
    print("Lean definition (paste into BCH/SymmetricQuintic.lean):")
    print("=" * 70)
    print()
    print(f"/-- **τ⁷ coefficient of `log(exp(a/2)·exp(b)·exp(a/2))`** — explicit")
    print(f"126-term polynomial form (3-factor Strang block at order 7).")
    print(f"")
    print(f"The coefficients are rational with LCM {lcm}; written individually.")
    print(f"This is the analog of `symmetric_bch_quintic_poly` at one higher degree.")
    print(f"Used in Stage 3 of the septic axiom discharge as the deg-7 BCH")
    print(f"correction.")
    print(f"")
    print(f"Σ|coef|/{lcm} ≈ {float(abs_sum):.6f} — used for the norm bound")
    print(f"`‖symmetric_bch_septic_poly(a, b)‖ ≤ {float(abs_sum):.4f}·(‖a‖+‖b‖)⁷`.")
    print(f"")
    print(f"Source: `compute_bch_r7.py::strang_block_series(1, 7)` after")
    print(f"`log_one_plus` extraction and degree-7 filtering. -/")
    print(f"noncomputable def symmetric_bch_septic_poly (𝕂 : Type*) [RCLike 𝕂] {{𝔸 : Type*}}")
    print(f"    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=")

    lines = []
    for idx, (w, c) in enumerate(items):
        num = c.p if hasattr(c, 'p') else c.as_numer_denom()[0]
        denom = c.q if hasattr(c, 'q') else c.as_numer_denom()[1]
        # Adjust to common LCM
        scaled_num = int(num) * (lcm // int(denom))
        word_lean = ' * '.join('a' if x == 0 else 'b' for x in w)
        sign = '  ' if idx == 0 else '+ '
        lines.append(f'  {sign}({scaled_num} / {lcm} : 𝕂) • ({word_lean})')
    print('\n'.join(lines))

    # Emit the homogeneity proof.
    print()
    print()
    print("/-! ## Homogeneity: `c⁷` scaling -/")
    print()
    print("/-- **7-fold smul-product identity**: `(c•x₁)·…·(c•x₇) = c⁷ • (x₁·…·x₇)`. -/")
    print("private lemma seven_fold_smul_mul (c : 𝕂) (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : 𝔸) :")
    print("    (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) * (c • x₆) * (c • x₇) =")
    print("      c ^ 7 • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇) := by")
    print("  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]")
    print("  ring_nf")
    print()
    print("/-- **Homogeneity of `symmetric_bch_septic_poly`**: `E₇(c•a, c•b) = c⁷•E₇(a, b)`. -/")
    print("theorem symmetric_bch_septic_poly_smul (a b : 𝔸) (c : 𝕂) :")
    print("    symmetric_bch_septic_poly 𝕂 (c • a) (c • b) =")
    print("      c ^ 7 • symmetric_bch_septic_poly 𝕂 a b := by")
    print("  unfold symmetric_bch_septic_poly")
    print("  simp only [seven_fold_smul_mul c, smul_comm _ (c ^ 7 : 𝕂), ← smul_add]")


if __name__ == "__main__":
    main()
