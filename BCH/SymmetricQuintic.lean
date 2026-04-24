/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH/SymmetricQuintic — τ⁵ coefficient of the 3-factor symmetric BCH

Provides the degree-5 polynomial form `symmetric_bch_quintic_poly a b` for
the τ⁵ Taylor coefficient of `log(exp(a/2)·exp(b)·exp(a/2))`, plus its
`c⁵` homogeneity.

This mirrors the existing `symmetric_bch_cubic_poly` in `Basic.lean` and
is the Tier-1 infrastructure piece (definition + homogeneity) for
discharging Lean-BCH's `suzuki5_R5_identification_axiom`.

## Status (Option 1 scope, partial)

**Done this session:**
- `symmetric_bch_quintic_poly a b` — 30-term explicit polynomial form,
  CAS-derived from `Lean-Trotter/scripts/compute_bch_prefactors.py`.
  Rational coefficients with common denominator 5760 (integer
  numerators in `{7, ±7, 42, 72, 12, 32, ±28, ±48, ±8, 192}`).
- `symmetric_bch_quintic_poly_smul` — `c⁵` scaling homogeneity.
  Provable by `simp` on the 5-fold-smul-mul helper.

**Deferred to a follow-up session:**
- `norm_symmetric_bch_quintic_poly_le` — `‖E₅(a, b)‖ ≤ (‖a‖+‖b‖)⁵`.
  Straightforward in principle (30-way triangle inequality + word
  norm ≤ s⁵ + Σ |coef|/5760 = 1216/5760 < 1), but the 29-step
  `norm_add_le` chain is verbose (~50 lines). Not blocking downstream
  development — the definition is fully specified and downstream
  proofs can use pointwise per-term bounds until the global bound lands.
- Full Taylor expansion theorem

      ∃ δ > 0, ∃ K ≥ 0, ∀ τ, ‖τ‖ < δ →
        ‖symmetric_bch(c·τ·a, c·τ·b) − (c·τ)•(a+b)
           − (c·τ)³•symmetric_bch_cubic_poly a b
           − (c·τ)⁵•symmetric_bch_quintic_poly a b‖ ≤ K·‖c·τ‖⁷·(‖a‖+‖b‖)⁷

  requires a degree-5+ symbolic BCH expansion machinery (extend H1/H2's
  cubic/quartic to quintic). This is the B1.c piece of the session-9+
  roadmap for discharging `suzuki5_R5_identification_axiom`.
-/

import BCH.Basic

namespace BCH

section SymmetricQuinticPoly

variable {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-!
## The 30-term τ⁵ polynomial

CAS-derived from
`Lean-Trotter/scripts/compute_bch_prefactors.py::strang_block_series`
at degree 5. Each of the 30 non-zero 5-letter words `x₁x₂x₃x₄x₅` with
`xᵢ ∈ {a, b}` has a rational coefficient with common denominator 5760.

Palindromic symmetry: `coef(w) = coef(reverse(w))` — 12 word/reverse
pairs plus 6 self-palindromic words (AABAA, ABABA, ABBBA, BAAAB,
BABAB, BBABB).
-/

/-- **τ⁵ coefficient of `log(exp(a/2)·exp(b)·exp(a/2))`** — explicit
30-term polynomial form.

The coefficients are rational with LCM 5760; written individually here.
This is the 3-factor Strang block's quintic BCH coefficient, analogous
to `symmetric_bch_cubic_poly` for the cubic coefficient.

Source: `compute_bch_prefactors.py::strang_block_series(1, max_degree=5)`
after `log_one_plus` extraction and degree-5 filtering. -/
noncomputable def symmetric_bch_quintic_poly (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
    (7 / 5760 : 𝕂) • (a * a * a * a * b)
  + (-28 / 5760 : 𝕂) • (a * a * a * b * a)
  + (-28 / 5760 : 𝕂) • (a * a * a * b * b)
  + (42 / 5760 : 𝕂) • (a * a * b * a * a)
  + (72 / 5760 : 𝕂) • (a * a * b * a * b)
  + (12 / 5760 : 𝕂) • (a * a * b * b * a)
  + (32 / 5760 : 𝕂) • (a * a * b * b * b)
  + (-28 / 5760 : 𝕂) • (a * b * a * a * a)
  + (-48 / 5760 : 𝕂) • (a * b * a * a * b)
  + (-48 / 5760 : 𝕂) • (a * b * a * b * a)
  + (-48 / 5760 : 𝕂) • (a * b * a * b * b)
  + (12 / 5760 : 𝕂) • (a * b * b * a * a)
  + (-48 / 5760 : 𝕂) • (a * b * b * a * b)
  + (32 / 5760 : 𝕂) • (a * b * b * b * a)
  + (-8 / 5760 : 𝕂) • (a * b * b * b * b)
  + (7 / 5760 : 𝕂) • (b * a * a * a * a)
  + (32 / 5760 : 𝕂) • (b * a * a * a * b)
  + (-48 / 5760 : 𝕂) • (b * a * a * b * a)
  + (-48 / 5760 : 𝕂) • (b * a * a * b * b)
  + (72 / 5760 : 𝕂) • (b * a * b * a * a)
  + (192 / 5760 : 𝕂) • (b * a * b * a * b)
  + (-48 / 5760 : 𝕂) • (b * a * b * b * a)
  + (32 / 5760 : 𝕂) • (b * a * b * b * b)
  + (-28 / 5760 : 𝕂) • (b * b * a * a * a)
  + (-48 / 5760 : 𝕂) • (b * b * a * a * b)
  + (-48 / 5760 : 𝕂) • (b * b * a * b * a)
  + (-48 / 5760 : 𝕂) • (b * b * a * b * b)
  + (32 / 5760 : 𝕂) • (b * b * b * a * a)
  + (32 / 5760 : 𝕂) • (b * b * b * a * b)
  + (-8 / 5760 : 𝕂) • (b * b * b * b * a)

/-!
## Homogeneity: `c⁵` scaling

For any `c : 𝕂`, `symmetric_bch_quintic_poly(c•a, c•b) = c⁵ •
symmetric_bch_quintic_poly(a, b)`. Follows from each 5-letter word being
homogeneous of degree 5 in `(a, b)`.
-/

/-- **5-fold smul-product identity**: `(c•x₁)·(c•x₂)·(c•x₃)·(c•x₄)·(c•x₅)
= c⁵ • (x₁·x₂·x₃·x₄·x₅)`. Used in the homogeneity proof below. -/
private lemma five_fold_smul_mul (c : 𝕂) (x₁ x₂ x₃ x₄ x₅ : 𝔸) :
    (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) =
      c ^ 5 • (x₁ * x₂ * x₃ * x₄ * x₅) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1; ring

/-- **Homogeneity of `symmetric_bch_quintic_poly`**:
`E₅(c•a, c•b) = c⁵ • E₅(a, b)`. -/
theorem symmetric_bch_quintic_poly_smul (a b : 𝔸) (c : 𝕂) :
    symmetric_bch_quintic_poly 𝕂 (c • a) (c • b) =
      c ^ 5 • symmetric_bch_quintic_poly 𝕂 a b := by
  unfold symmetric_bch_quintic_poly
  simp only [five_fold_smul_mul c, smul_comm _ (c ^ 5 : 𝕂), ← smul_add]

end SymmetricQuinticPoly

end BCH
