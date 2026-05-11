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

/-! ## τ⁷ symmetric BCH coefficient (deg-7 Strang block) -/

/-- **τ⁷ coefficient of `log(exp(a/2)·exp(b)·exp(a/2))`** — explicit
126-term polynomial form (3-factor Strang block at order 7).

The coefficients are rational with LCM 967680; written individually.
This is the analog of `symmetric_bch_quintic_poly` at one higher degree.
Used in Stage 3 of the septic axiom discharge as the deg-7 BCH
correction.

Σ|coef|/967680 ≈ 0.086037 — used for the norm bound
`‖symmetric_bch_septic_poly(a, b)‖ ≤ 0.0860·(‖a‖+‖b‖)⁷`.

Source: `compute_bch_r7.py::strang_block_series(1, 7)` after
`log_one_plus` extraction and degree-7 filtering. -/
noncomputable def symmetric_bch_septic_poly (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
    (-31 / 967680 : 𝕂) • (a * a * a * a * a * a * b)
  + (186 / 967680 : 𝕂) • (a * a * a * a * a * b * a)
  + (186 / 967680 : 𝕂) • (a * a * a * a * a * b * b)
  + (-465 / 967680 : 𝕂) • (a * a * a * a * b * a * a)
  + (-612 / 967680 : 𝕂) • (a * a * a * a * b * a * b)
  + (-318 / 967680 : 𝕂) • (a * a * a * a * b * b * a)
  + (-416 / 967680 : 𝕂) • (a * a * a * a * b * b * b)
  + (620 / 967680 : 𝕂) • (a * a * a * b * a * a * a)
  + (816 / 967680 : 𝕂) • (a * a * a * b * a * a * b)
  + (816 / 967680 : 𝕂) • (a * a * a * b * a * b * a)
  + (816 / 967680 : 𝕂) • (a * a * a * b * a * b * b)
  + (228 / 967680 : 𝕂) • (a * a * a * b * b * a * a)
  + (816 / 967680 : 𝕂) • (a * a * a * b * b * a * b)
  + (32 / 967680 : 𝕂) • (a * a * a * b * b * b * a)
  + (424 / 967680 : 𝕂) • (a * a * a * b * b * b * b)
  + (-465 / 967680 : 𝕂) • (a * a * b * a * a * a * a)
  + (-864 / 967680 : 𝕂) • (a * a * b * a * a * a * b)
  + (144 / 967680 : 𝕂) • (a * a * b * a * a * b * a)
  + (144 / 967680 : 𝕂) • (a * a * b * a * a * b * b)
  + (-1368 / 967680 : 𝕂) • (a * a * b * a * b * a * a)
  + (-2880 / 967680 : 𝕂) • (a * a * b * a * b * a * b)
  + (144 / 967680 : 𝕂) • (a * a * b * a * b * b * a)
  + (-864 / 967680 : 𝕂) • (a * a * b * a * b * b * b)
  + (228 / 967680 : 𝕂) • (a * a * b * b * a * a * a)
  + (144 / 967680 : 𝕂) • (a * a * b * b * a * a * b)
  + (144 / 967680 : 𝕂) • (a * a * b * b * a * b * a)
  + (144 / 967680 : 𝕂) • (a * a * b * b * a * b * b)
  + (-192 / 967680 : 𝕂) • (a * a * b * b * b * a * a)
  + (-864 / 967680 : 𝕂) • (a * a * b * b * b * a * b)
  + (312 / 967680 : 𝕂) • (a * a * b * b * b * b * a)
  + (-192 / 967680 : 𝕂) • (a * a * b * b * b * b * b)
  + (186 / 967680 : 𝕂) • (a * b * a * a * a * a * a)
  + (480 / 967680 : 𝕂) • (a * b * a * a * a * a * b)
  + (-192 / 967680 : 𝕂) • (a * b * a * a * a * b * a)
  + (-192 / 967680 : 𝕂) • (a * b * a * a * a * b * b)
  + (144 / 967680 : 𝕂) • (a * b * a * a * b * a * a)
  + (1152 / 967680 : 𝕂) • (a * b * a * a * b * a * b)
  + (-864 / 967680 : 𝕂) • (a * b * a * a * b * b * a)
  + (-192 / 967680 : 𝕂) • (a * b * a * a * b * b * b)
  + (816 / 967680 : 𝕂) • (a * b * a * b * a * a * a)
  + (1152 / 967680 : 𝕂) • (a * b * a * b * a * a * b)
  + (1152 / 967680 : 𝕂) • (a * b * a * b * a * b * a)
  + (1152 / 967680 : 𝕂) • (a * b * a * b * a * b * b)
  + (144 / 967680 : 𝕂) • (a * b * a * b * b * a * a)
  + (1152 / 967680 : 𝕂) • (a * b * a * b * b * a * b)
  + (-192 / 967680 : 𝕂) • (a * b * a * b * b * b * a)
  + (480 / 967680 : 𝕂) • (a * b * a * b * b * b * b)
  + (-318 / 967680 : 𝕂) • (a * b * b * a * a * a * a)
  + (-192 / 967680 : 𝕂) • (a * b * b * a * a * a * b)
  + (-864 / 967680 : 𝕂) • (a * b * b * a * a * b * a)
  + (-864 / 967680 : 𝕂) • (a * b * b * a * a * b * b)
  + (144 / 967680 : 𝕂) • (a * b * b * a * b * a * a)
  + (1152 / 967680 : 𝕂) • (a * b * b * a * b * a * b)
  + (-864 / 967680 : 𝕂) • (a * b * b * a * b * b * a)
  + (-192 / 967680 : 𝕂) • (a * b * b * a * b * b * b)
  + (32 / 967680 : 𝕂) • (a * b * b * b * a * a * a)
  + (-192 / 967680 : 𝕂) • (a * b * b * b * a * a * b)
  + (-192 / 967680 : 𝕂) • (a * b * b * b * a * b * a)
  + (-192 / 967680 : 𝕂) • (a * b * b * b * a * b * b)
  + (312 / 967680 : 𝕂) • (a * b * b * b * b * a * a)
  + (480 / 967680 : 𝕂) • (a * b * b * b * b * a * b)
  + (-192 / 967680 : 𝕂) • (a * b * b * b * b * b * a)
  + (32 / 967680 : 𝕂) • (a * b * b * b * b * b * b)
  + (-31 / 967680 : 𝕂) • (b * a * a * a * a * a * a)
  + (-192 / 967680 : 𝕂) • (b * a * a * a * a * a * b)
  + (480 / 967680 : 𝕂) • (b * a * a * a * a * b * a)
  + (480 / 967680 : 𝕂) • (b * a * a * a * a * b * b)
  + (-864 / 967680 : 𝕂) • (b * a * a * a * b * a * a)
  + (-1536 / 967680 : 𝕂) • (b * a * a * a * b * a * b)
  + (-192 / 967680 : 𝕂) • (b * a * a * a * b * b * a)
  + (-640 / 967680 : 𝕂) • (b * a * a * a * b * b * b)
  + (816 / 967680 : 𝕂) • (b * a * a * b * a * a * a)
  + (1152 / 967680 : 𝕂) • (b * a * a * b * a * a * b)
  + (1152 / 967680 : 𝕂) • (b * a * a * b * a * b * a)
  + (1152 / 967680 : 𝕂) • (b * a * a * b * a * b * b)
  + (144 / 967680 : 𝕂) • (b * a * a * b * b * a * a)
  + (1152 / 967680 : 𝕂) • (b * a * a * b * b * a * b)
  + (-192 / 967680 : 𝕂) • (b * a * a * b * b * b * a)
  + (480 / 967680 : 𝕂) • (b * a * a * b * b * b * b)
  + (-612 / 967680 : 𝕂) • (b * a * b * a * a * a * a)
  + (-1536 / 967680 : 𝕂) • (b * a * b * a * a * a * b)
  + (1152 / 967680 : 𝕂) • (b * a * b * a * a * b * a)
  + (1152 / 967680 : 𝕂) • (b * a * b * a * a * b * b)
  + (-2880 / 967680 : 𝕂) • (b * a * b * a * b * a * a)
  + (-6912 / 967680 : 𝕂) • (b * a * b * a * b * a * b)
  + (1152 / 967680 : 𝕂) • (b * a * b * a * b * b * a)
  + (-1536 / 967680 : 𝕂) • (b * a * b * a * b * b * b)
  + (816 / 967680 : 𝕂) • (b * a * b * b * a * a * a)
  + (1152 / 967680 : 𝕂) • (b * a * b * b * a * a * b)
  + (1152 / 967680 : 𝕂) • (b * a * b * b * a * b * a)
  + (1152 / 967680 : 𝕂) • (b * a * b * b * a * b * b)
  + (-864 / 967680 : 𝕂) • (b * a * b * b * b * a * a)
  + (-1536 / 967680 : 𝕂) • (b * a * b * b * b * a * b)
  + (480 / 967680 : 𝕂) • (b * a * b * b * b * b * a)
  + (-192 / 967680 : 𝕂) • (b * a * b * b * b * b * b)
  + (186 / 967680 : 𝕂) • (b * b * a * a * a * a * a)
  + (480 / 967680 : 𝕂) • (b * b * a * a * a * a * b)
  + (-192 / 967680 : 𝕂) • (b * b * a * a * a * b * a)
  + (-192 / 967680 : 𝕂) • (b * b * a * a * a * b * b)
  + (144 / 967680 : 𝕂) • (b * b * a * a * b * a * a)
  + (1152 / 967680 : 𝕂) • (b * b * a * a * b * a * b)
  + (-864 / 967680 : 𝕂) • (b * b * a * a * b * b * a)
  + (-192 / 967680 : 𝕂) • (b * b * a * a * b * b * b)
  + (816 / 967680 : 𝕂) • (b * b * a * b * a * a * a)
  + (1152 / 967680 : 𝕂) • (b * b * a * b * a * a * b)
  + (1152 / 967680 : 𝕂) • (b * b * a * b * a * b * a)
  + (1152 / 967680 : 𝕂) • (b * b * a * b * a * b * b)
  + (144 / 967680 : 𝕂) • (b * b * a * b * b * a * a)
  + (1152 / 967680 : 𝕂) • (b * b * a * b * b * a * b)
  + (-192 / 967680 : 𝕂) • (b * b * a * b * b * b * a)
  + (480 / 967680 : 𝕂) • (b * b * a * b * b * b * b)
  + (-416 / 967680 : 𝕂) • (b * b * b * a * a * a * a)
  + (-640 / 967680 : 𝕂) • (b * b * b * a * a * a * b)
  + (-192 / 967680 : 𝕂) • (b * b * b * a * a * b * a)
  + (-192 / 967680 : 𝕂) • (b * b * b * a * a * b * b)
  + (-864 / 967680 : 𝕂) • (b * b * b * a * b * a * a)
  + (-1536 / 967680 : 𝕂) • (b * b * b * a * b * a * b)
  + (-192 / 967680 : 𝕂) • (b * b * b * a * b * b * a)
  + (-640 / 967680 : 𝕂) • (b * b * b * a * b * b * b)
  + (424 / 967680 : 𝕂) • (b * b * b * b * a * a * a)
  + (480 / 967680 : 𝕂) • (b * b * b * b * a * a * b)
  + (480 / 967680 : 𝕂) • (b * b * b * b * a * b * a)
  + (480 / 967680 : 𝕂) • (b * b * b * b * a * b * b)
  + (-192 / 967680 : 𝕂) • (b * b * b * b * b * a * a)
  + (-192 / 967680 : 𝕂) • (b * b * b * b * b * a * b)
  + (32 / 967680 : 𝕂) • (b * b * b * b * b * b * a)


/-! ## Homogeneity: `c⁷` scaling -/

/-- **7-fold smul-product identity**: `(c•x₁)·…·(c•x₇) = c⁷ • (x₁·…·x₇)`. -/
private lemma seven_fold_smul_mul (c : 𝕂) (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : 𝔸) :
    (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) * (c • x₆) * (c • x₇) =
      c ^ 7 • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
  ring_nf

/-- **Homogeneity of `symmetric_bch_septic_poly`**: `E₇(c•a, c•b) = c⁷•E₇(a, b)`. -/
theorem symmetric_bch_septic_poly_smul (a b : 𝔸) (c : 𝕂) :
    symmetric_bch_septic_poly 𝕂 (c • a) (c • b) =
      c ^ 7 • symmetric_bch_septic_poly 𝕂 a b := by
  unfold symmetric_bch_septic_poly
  simp only [seven_fold_smul_mul c, smul_comm _ (c ^ 7 : 𝕂), ← smul_add]


/-!
## Norm bound: `‖E₅(a, b)‖ ≤ (‖a‖ + ‖b‖)⁵`

Proof strategy: each 5-letter word has norm ≤ `s⁵` where
`s = ‖a‖ + ‖b‖`; the sum of `|coef|·5760` over the 30 terms is
`1216 ≤ 5760`, giving total `‖E₅‖ ≤ (1216/5760)·s⁵ ≤ s⁵`.
-/

/-- **Word norm bound**: a 5-letter product `x₁·x₂·x₃·x₄·x₅` with each
`xᵢ ∈ {a, b}` has norm ≤ `(‖a‖+‖b‖)⁵`. -/
private lemma norm_five_word_le (a b x₁ x₂ x₃ x₄ x₅ : 𝔸)
    (h₁ : ‖x₁‖ ≤ ‖a‖ + ‖b‖) (h₂ : ‖x₂‖ ≤ ‖a‖ + ‖b‖)
    (h₃ : ‖x₃‖ ≤ ‖a‖ + ‖b‖) (h₄ : ‖x₄‖ ≤ ‖a‖ + ‖b‖)
    (h₅ : ‖x₅‖ ≤ ‖a‖ + ‖b‖) :
    ‖x₁ * x₂ * x₃ * x₄ * x₅‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  set s := ‖a‖ + ‖b‖
  have hs_nn : 0 ≤ s := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖x₁ * x₂ * x₃ * x₄ * x₅‖
      ≤ ‖x₁ * x₂ * x₃ * x₄‖ * ‖x₅‖ := norm_mul_le _ _
    _ ≤ (‖x₁ * x₂ * x₃‖ * ‖x₄‖) * ‖x₅‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((‖x₁ * x₂‖ * ‖x₃‖) * ‖x₄‖) * ‖x₅‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ (((‖x₁‖ * ‖x₂‖) * ‖x₃‖) * ‖x₄‖) * ‖x₅‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ (((s * s) * s) * s) * s := by gcongr
    _ = s ^ 5 := by ring

/-- **Scaled-word norm bound**: for any `k : ℤ` and word `w` with
`‖w‖ ≤ s⁵`, `‖((k : 𝕂)/5760) • w‖ ≤ |k|/5760 · s⁵`. -/
private lemma norm_scaled_word_le (k : ℤ) (w : 𝔸) (s : ℝ)
    (hw : ‖w‖ ≤ s ^ 5) (hs_nn : 0 ≤ s) :
    ‖((k : 𝕂) / 5760) • w‖ ≤ |(k : ℝ)| / 5760 * s ^ 5 := by
  have h5760_norm : ‖(5760 : 𝕂)‖ = 5760 := by
    rw [show (5760 : 𝕂) = ((5760 : ℕ) : 𝕂) from by norm_cast, RCLike.norm_natCast]
    norm_num
  have hs5_nn : 0 ≤ s ^ 5 := pow_nonneg hs_nn 5
  have hc_nn : (0 : ℝ) ≤ |(k : ℝ)| / 5760 := by positivity
  have hk_norm : ‖((k : ℤ) : 𝕂)‖ = |(k : ℝ)| := by
    rw [show ((k : ℤ) : 𝕂) = ((k : ℝ) : 𝕂) from by push_cast; rfl, RCLike.norm_ofReal]
  calc ‖((k : 𝕂) / 5760) • w‖
      ≤ ‖((k : 𝕂) / 5760)‖ * ‖w‖ := norm_smul_le _ _
    _ = |(k : ℝ)| / 5760 * ‖w‖ := by
        rw [norm_div, h5760_norm, hk_norm]
    _ ≤ |(k : ℝ)| / 5760 * s ^ 5 := mul_le_mul_of_nonneg_left hw hc_nn

/-- **Norm bound for `symmetric_bch_quintic_poly`**:
`‖E₅(a, b)‖ ≤ (‖a‖ + ‖b‖)⁵`.

Proof: each of the 30 terms is bounded by `|coef|·s⁵` via
`norm_scaled_word_le`; the 30 integer numerators `|k|` sum to 1216
(< 5760), so the triangle-inequality chain yields the `s⁵` bound.

Auxiliary extracted to `norm_symmetric_bch_quintic_poly_le_aux` with
increased heartbeats to accommodate the 29-step `norm_add_le` chain
that linarith collapses. -/
private lemma norm_symmetric_bch_quintic_poly_le_aux (a b : 𝔸)
    (s : ℝ) (hs_def : s = ‖a‖ + ‖b‖) :
    ‖symmetric_bch_quintic_poly 𝕂 a b‖ ≤ s ^ 5 := by
  have hs_nn : 0 ≤ s := by rw [hs_def]; exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs5_nn : 0 ≤ s ^ 5 := pow_nonneg hs_nn 5
  have ha_le : ‖a‖ ≤ s := by rw [hs_def]; linarith [norm_nonneg b]
  have hb_le : ‖b‖ ≤ s := by rw [hs_def]; linarith [norm_nonneg a]
  -- Helper: word norm ≤ s⁵.
  have hw : ∀ (x₁ x₂ x₃ x₄ x₅ : 𝔸), ‖x₁‖ ≤ s → ‖x₂‖ ≤ s → ‖x₃‖ ≤ s →
      ‖x₄‖ ≤ s → ‖x₅‖ ≤ s → ‖x₁ * x₂ * x₃ * x₄ * x₅‖ ≤ s ^ 5 :=
    fun x₁ x₂ x₃ x₄ x₅ h₁ h₂ h₃ h₄ h₅ => by
      have := norm_five_word_le (𝔸 := 𝔸) a b x₁ x₂ x₃ x₄ x₅
        (by rw [hs_def] at h₁; exact h₁) (by rw [hs_def] at h₂; exact h₂)
        (by rw [hs_def] at h₃; exact h₃) (by rw [hs_def] at h₄; exact h₄)
        (by rw [hs_def] at h₅; exact h₅)
      rw [hs_def]; exact this
  -- The 30 individual word norm bounds.
  have w01 := hw a a a a b ha_le ha_le ha_le ha_le hb_le
  have w02 := hw a a a b a ha_le ha_le ha_le hb_le ha_le
  have w03 := hw a a a b b ha_le ha_le ha_le hb_le hb_le
  have w04 := hw a a b a a ha_le ha_le hb_le ha_le ha_le
  have w05 := hw a a b a b ha_le ha_le hb_le ha_le hb_le
  have w06 := hw a a b b a ha_le ha_le hb_le hb_le ha_le
  have w07 := hw a a b b b ha_le ha_le hb_le hb_le hb_le
  have w08 := hw a b a a a ha_le hb_le ha_le ha_le ha_le
  have w09 := hw a b a a b ha_le hb_le ha_le ha_le hb_le
  have w10 := hw a b a b a ha_le hb_le ha_le hb_le ha_le
  have w11 := hw a b a b b ha_le hb_le ha_le hb_le hb_le
  have w12 := hw a b b a a ha_le hb_le hb_le ha_le ha_le
  have w13 := hw a b b a b ha_le hb_le hb_le ha_le hb_le
  have w14 := hw a b b b a ha_le hb_le hb_le hb_le ha_le
  have w15 := hw a b b b b ha_le hb_le hb_le hb_le hb_le
  have w16 := hw b a a a a hb_le ha_le ha_le ha_le ha_le
  have w17 := hw b a a a b hb_le ha_le ha_le ha_le hb_le
  have w18 := hw b a a b a hb_le ha_le ha_le hb_le ha_le
  have w19 := hw b a a b b hb_le ha_le ha_le hb_le hb_le
  have w20 := hw b a b a a hb_le ha_le hb_le ha_le ha_le
  have w21 := hw b a b a b hb_le ha_le hb_le ha_le hb_le
  have w22 := hw b a b b a hb_le ha_le hb_le hb_le ha_le
  have w23 := hw b a b b b hb_le ha_le hb_le hb_le hb_le
  have w24 := hw b b a a a hb_le hb_le ha_le ha_le ha_le
  have w25 := hw b b a a b hb_le hb_le ha_le ha_le hb_le
  have w26 := hw b b a b a hb_le hb_le ha_le hb_le ha_le
  have w27 := hw b b a b b hb_le hb_le ha_le hb_le hb_le
  have w28 := hw b b b a a hb_le hb_le hb_le ha_le ha_le
  have w29 := hw b b b a b hb_le hb_le hb_le ha_le hb_le
  have w30 := hw b b b b a hb_le hb_le hb_le hb_le ha_le
  -- The 30 per-term norm bounds, via norm_scaled_word_le, with integer
  -- casts matching the definition's `(k / 5760 : 𝕂)` literal form.
  -- Integer-to-𝕂 cast: `((k : ℤ) : 𝕂) / 5760 = (k / 5760 : 𝕂)` for concrete k,
  -- which we convert by `push_cast`.
  have t01 : ‖(7 / 5760 : 𝕂) • (a * a * a * a * b)‖ ≤ 7 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 7 (a * a * a * a * b) s w01 hs_nn
    have heq : ((7 : ℤ) : 𝕂) / 5760 = (7 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((7 : ℤ) : ℝ)| = 7 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t02 : ‖(-28 / 5760 : 𝕂) • (a * a * a * b * a)‖ ≤ 28 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-28) (a * a * a * b * a) s w02 hs_nn
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t03 : ‖(-28 / 5760 : 𝕂) • (a * a * a * b * b)‖ ≤ 28 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-28) (a * a * a * b * b) s w03 hs_nn
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t04 : ‖(42 / 5760 : 𝕂) • (a * a * b * a * a)‖ ≤ 42 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 42 (a * a * b * a * a) s w04 hs_nn
    have heq : ((42 : ℤ) : 𝕂) / 5760 = (42 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((42 : ℤ) : ℝ)| = 42 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t05 : ‖(72 / 5760 : 𝕂) • (a * a * b * a * b)‖ ≤ 72 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 72 (a * a * b * a * b) s w05 hs_nn
    have heq : ((72 : ℤ) : 𝕂) / 5760 = (72 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((72 : ℤ) : ℝ)| = 72 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t06 : ‖(12 / 5760 : 𝕂) • (a * a * b * b * a)‖ ≤ 12 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 12 (a * a * b * b * a) s w06 hs_nn
    have heq : ((12 : ℤ) : 𝕂) / 5760 = (12 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((12 : ℤ) : ℝ)| = 12 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t07 : ‖(32 / 5760 : 𝕂) • (a * a * b * b * b)‖ ≤ 32 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 32 (a * a * b * b * b) s w07 hs_nn
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t08 : ‖(-28 / 5760 : 𝕂) • (a * b * a * a * a)‖ ≤ 28 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-28) (a * b * a * a * a) s w08 hs_nn
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t09 : ‖(-48 / 5760 : 𝕂) • (a * b * a * a * b)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (a * b * a * a * b) s w09 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t10 : ‖(-48 / 5760 : 𝕂) • (a * b * a * b * a)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (a * b * a * b * a) s w10 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t11 : ‖(-48 / 5760 : 𝕂) • (a * b * a * b * b)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (a * b * a * b * b) s w11 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t12 : ‖(12 / 5760 : 𝕂) • (a * b * b * a * a)‖ ≤ 12 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 12 (a * b * b * a * a) s w12 hs_nn
    have heq : ((12 : ℤ) : 𝕂) / 5760 = (12 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((12 : ℤ) : ℝ)| = 12 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t13 : ‖(-48 / 5760 : 𝕂) • (a * b * b * a * b)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (a * b * b * a * b) s w13 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t14 : ‖(32 / 5760 : 𝕂) • (a * b * b * b * a)‖ ≤ 32 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 32 (a * b * b * b * a) s w14 hs_nn
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t15 : ‖(-8 / 5760 : 𝕂) • (a * b * b * b * b)‖ ≤ 8 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-8) (a * b * b * b * b) s w15 hs_nn
    have heq : ((-8 : ℤ) : 𝕂) / 5760 = (-8 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-8 : ℤ) : ℝ)| = 8 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t16 : ‖(7 / 5760 : 𝕂) • (b * a * a * a * a)‖ ≤ 7 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 7 (b * a * a * a * a) s w16 hs_nn
    have heq : ((7 : ℤ) : 𝕂) / 5760 = (7 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((7 : ℤ) : ℝ)| = 7 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t17 : ‖(32 / 5760 : 𝕂) • (b * a * a * a * b)‖ ≤ 32 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 32 (b * a * a * a * b) s w17 hs_nn
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t18 : ‖(-48 / 5760 : 𝕂) • (b * a * a * b * a)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (b * a * a * b * a) s w18 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t19 : ‖(-48 / 5760 : 𝕂) • (b * a * a * b * b)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (b * a * a * b * b) s w19 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t20 : ‖(72 / 5760 : 𝕂) • (b * a * b * a * a)‖ ≤ 72 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 72 (b * a * b * a * a) s w20 hs_nn
    have heq : ((72 : ℤ) : 𝕂) / 5760 = (72 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((72 : ℤ) : ℝ)| = 72 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t21 : ‖(192 / 5760 : 𝕂) • (b * a * b * a * b)‖ ≤ 192 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 192 (b * a * b * a * b) s w21 hs_nn
    have heq : ((192 : ℤ) : 𝕂) / 5760 = (192 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((192 : ℤ) : ℝ)| = 192 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t22 : ‖(-48 / 5760 : 𝕂) • (b * a * b * b * a)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (b * a * b * b * a) s w22 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t23 : ‖(32 / 5760 : 𝕂) • (b * a * b * b * b)‖ ≤ 32 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 32 (b * a * b * b * b) s w23 hs_nn
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t24 : ‖(-28 / 5760 : 𝕂) • (b * b * a * a * a)‖ ≤ 28 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-28) (b * b * a * a * a) s w24 hs_nn
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t25 : ‖(-48 / 5760 : 𝕂) • (b * b * a * a * b)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (b * b * a * a * b) s w25 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t26 : ‖(-48 / 5760 : 𝕂) • (b * b * a * b * a)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (b * b * a * b * a) s w26 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t27 : ‖(-48 / 5760 : 𝕂) • (b * b * a * b * b)‖ ≤ 48 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-48) (b * b * a * b * b) s w27 hs_nn
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t28 : ‖(32 / 5760 : 𝕂) • (b * b * b * a * a)‖ ≤ 32 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 32 (b * b * b * a * a) s w28 hs_nn
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t29 : ‖(32 / 5760 : 𝕂) • (b * b * b * a * b)‖ ≤ 32 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) 32 (b * b * b * a * b) s w29 hs_nn
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t30 : ‖(-8 / 5760 : 𝕂) • (b * b * b * b * a)‖ ≤ 8 / 5760 * s ^ 5 := by
    have := norm_scaled_word_le (𝕂 := 𝕂) (-8) (b * b * b * b * a) s w30 hs_nn
    have heq : ((-8 : ℤ) : 𝕂) / 5760 = (-8 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-8 : ℤ) : ℝ)| = 8 := by push_cast; norm_num
    rw [habs] at this; exact this
  -- 29-step triangle inequality chain via norm_add_le.
  unfold symmetric_bch_quintic_poly
  set T01 := (7 / 5760 : 𝕂) • (a * a * a * a * b)
  set T02 := (-28 / 5760 : 𝕂) • (a * a * a * b * a)
  set T03 := (-28 / 5760 : 𝕂) • (a * a * a * b * b)
  set T04 := (42 / 5760 : 𝕂) • (a * a * b * a * a)
  set T05 := (72 / 5760 : 𝕂) • (a * a * b * a * b)
  set T06 := (12 / 5760 : 𝕂) • (a * a * b * b * a)
  set T07 := (32 / 5760 : 𝕂) • (a * a * b * b * b)
  set T08 := (-28 / 5760 : 𝕂) • (a * b * a * a * a)
  set T09 := (-48 / 5760 : 𝕂) • (a * b * a * a * b)
  set T10 := (-48 / 5760 : 𝕂) • (a * b * a * b * a)
  set T11 := (-48 / 5760 : 𝕂) • (a * b * a * b * b)
  set T12 := (12 / 5760 : 𝕂) • (a * b * b * a * a)
  set T13 := (-48 / 5760 : 𝕂) • (a * b * b * a * b)
  set T14 := (32 / 5760 : 𝕂) • (a * b * b * b * a)
  set T15 := (-8 / 5760 : 𝕂) • (a * b * b * b * b)
  set T16 := (7 / 5760 : 𝕂) • (b * a * a * a * a)
  set T17 := (32 / 5760 : 𝕂) • (b * a * a * a * b)
  set T18 := (-48 / 5760 : 𝕂) • (b * a * a * b * a)
  set T19 := (-48 / 5760 : 𝕂) • (b * a * a * b * b)
  set T20 := (72 / 5760 : 𝕂) • (b * a * b * a * a)
  set T21 := (192 / 5760 : 𝕂) • (b * a * b * a * b)
  set T22 := (-48 / 5760 : 𝕂) • (b * a * b * b * a)
  set T23 := (32 / 5760 : 𝕂) • (b * a * b * b * b)
  set T24 := (-28 / 5760 : 𝕂) • (b * b * a * a * a)
  set T25 := (-48 / 5760 : 𝕂) • (b * b * a * a * b)
  set T26 := (-48 / 5760 : 𝕂) • (b * b * a * b * a)
  set T27 := (-48 / 5760 : 𝕂) • (b * b * a * b * b)
  set T28 := (32 / 5760 : 𝕂) • (b * b * b * a * a)
  set T29 := (32 / 5760 : 𝕂) • (b * b * b * a * b)
  set T30 := (-8 / 5760 : 𝕂) • (b * b * b * b * a)
  -- Chain of norm_add_le applications on each partial sum.
  have S02 : ‖T01 + T02‖ ≤ ‖T01‖ + ‖T02‖ := norm_add_le _ _
  have S03 : ‖T01 + T02 + T03‖ ≤ ‖T01 + T02‖ + ‖T03‖ := norm_add_le _ _
  have S04 : ‖T01 + T02 + T03 + T04‖ ≤ ‖T01 + T02 + T03‖ + ‖T04‖ := norm_add_le _ _
  have S05 : ‖T01 + T02 + T03 + T04 + T05‖ ≤ ‖T01 + T02 + T03 + T04‖ + ‖T05‖ := norm_add_le _ _
  have S06 : ‖T01 + T02 + T03 + T04 + T05 + T06‖ ≤
      ‖T01 + T02 + T03 + T04 + T05‖ + ‖T06‖ := norm_add_le _ _
  have S07 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06‖ + ‖T07‖ := norm_add_le _ _
  have S08 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07‖ + ‖T08‖ := norm_add_le _ _
  have S09 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08‖ + ‖T09‖ := norm_add_le _ _
  have S10 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09‖ + ‖T10‖ := norm_add_le _ _
  have S11 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10‖ + ‖T11‖ := norm_add_le _ _
  have S12 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11‖ + ‖T12‖ := norm_add_le _ _
  have S13 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12‖ + ‖T13‖ := norm_add_le _ _
  have S14 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13‖ + ‖T14‖ := norm_add_le _ _
  have S15 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14‖ + ‖T15‖ :=
    norm_add_le _ _
  have S16 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15‖ + ‖T16‖ :=
    norm_add_le _ _
  have S17 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16‖ + ‖T17‖ :=
    norm_add_le _ _
  have S18 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17‖ + ‖T18‖ :=
    norm_add_le _ _
  have S19 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18‖ + ‖T19‖ :=
    norm_add_le _ _
  have S20 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19‖ + ‖T20‖ :=
    norm_add_le _ _
  have S21 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20‖ + ‖T21‖ :=
    norm_add_le _ _
  have S22 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21‖ + ‖T22‖ :=
    norm_add_le _ _
  have S23 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22‖ + ‖T23‖ :=
    norm_add_le _ _
  have S24 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23‖ + ‖T24‖ :=
    norm_add_le _ _
  have S25 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24‖ + ‖T25‖ :=
    norm_add_le _ _
  have S26 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25‖ + ‖T26‖ :=
    norm_add_le _ _
  have S27 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26‖ + ‖T27‖ :=
    norm_add_le _ _
  have S28 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27‖ + ‖T28‖ :=
    norm_add_le _ _
  have S29 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28 + T29‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28‖ + ‖T29‖ :=
    norm_add_le _ _
  have S30 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28 + T29 + T30‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28 + T29‖ + ‖T30‖ :=
    norm_add_le _ _
  -- Sum of 30 per-term bounds: Σ |kᵢ|/5760 · s⁵ = 1216/5760 · s⁵ ≤ s⁵.
  linarith [t01, t02, t03, t04, t05, t06, t07, t08, t09, t10,
            t11, t12, t13, t14, t15, t16, t17, t18, t19, t20,
            t21, t22, t23, t24, t25, t26, t27, t28, t29, t30,
            S02, S03, S04, S05, S06, S07, S08, S09, S10,
            S11, S12, S13, S14, S15, S16, S17, S18, S19, S20,
            S21, S22, S23, S24, S25, S26, S27, S28, S29, S30]

set_option maxHeartbeats 800000 in
/-- **Norm bound for `symmetric_bch_quintic_poly`**:
`‖E₅(a, b)‖ ≤ (‖a‖ + ‖b‖)⁵`. Wrapper over the auxiliary lemma. -/
theorem norm_symmetric_bch_quintic_poly_le (a b : 𝔸) :
    ‖symmetric_bch_quintic_poly 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 :=
  norm_symmetric_bch_quintic_poly_le_aux a b (‖a‖ + ‖b‖) rfl

/-!
## Vanishing on `(α•V, β•V)` (B2.2.a)

`symmetric_bch_quintic_poly` evaluated at scalar multiples of a single element
`V : 𝔸` is identically zero:

  `E₅(α•V, β•V) = 0`  for any  `α, β : 𝕂, V : 𝔸`.

This is a structural property: each 5-letter word `x₁x₂x₃x₄x₅` (with each
`xᵢ ∈ {α•V, β•V}`) evaluates to `(α^k · β^(5−k)) • V⁵` where `k` is the number
of `α`-slots. Summing the 30 word coefficients per `k`-group gives identically
zero polynomials in `(α, β)`:

* `k = 4` (5 words `xxxxy` with one `b`):  `7 − 28 + 42 − 28 + 7 = 0`
* `k = 3` (10 words):  `−28 + 72 + 12 − 48 − 48 + 12 + 32 − 48 + 72 − 28 = 0`
* `k = 2` (10 words):  `32 − 48 − 48 + 32 − 48 + 192 − 48 − 48 − 48 + 32 = 0`
* `k = 1` (5 words `xyyyy` with one `a`):  `−8 + 32 − 48 + 32 − 8 = 0`
* `k = 0, 5`:  no terms in the polynomial (no `aaaaa` or `bbbbb` words).

This is the **foundation lemma for B2.2**: when expanding
`sym_quintic_poly(4X, Y)` with `X = (pτ)•V + R_X` and `Y = ((1−4p)τ)•V + R_Y`,
the leading "all-V-linear" τ⁵ contribution vanishes, leaving only "≥1
residual" cross-terms which sit at `O(τ⁷)` (since each residual is `O(τ³)`).

**Why this matters**: in the τ⁵ identification of `suzuki5_R5`, the
`sym_quintic_poly(4X, Y)` contribution turns out to be `O(τ⁷)` — i.e., it
doesn't contribute at τ⁵ — so the entire τ⁵ residue comes from
`sym_cubic_poly(4X, Y)` plus the per-block quintic `(4p⁵+(1−4p)⁵)·E₅_sym`. -/

/-- **5-fold smul-mul absorption (single element)**: 5 factors each of the
form `sᵢ • V` collapse to `(s₁·s₂·s₃·s₄·s₅) • (V·V·V·V·V)`. -/
private lemma five_fold_smul_mul_eq (V : 𝔸) (s₁ s₂ s₃ s₄ s₅ : 𝕂) :
    (s₁ • V) * (s₂ • V) * (s₃ • V) * (s₄ • V) * (s₅ • V) =
      (s₁ * s₂ * s₃ * s₄ * s₅) • (V * V * V * V * V) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1; ring

/-- **5-letter product Lipschitz**: `‖x₁x₂x₃x₄x₅ − y₁y₂y₃y₄y₅‖ ≤ N⁴·Σᵢ ‖xᵢ−yᵢ‖`
when `‖xᵢ‖, ‖yᵢ‖ ≤ N`. Telescoping identity + triangle inequality. -/
private lemma word_5_diff_le (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : 𝔸) (N : ℝ)
    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N) (hx₅ : ‖x₅‖ ≤ N)
    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N) (hy₅ : ‖y₅‖ ≤ N)
    (hN_nn : 0 ≤ N) :
    ‖x₁ * x₂ * x₃ * x₄ * x₅ - y₁ * y₂ * y₃ * y₄ * y₅‖ ≤
      N ^ 4 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖) := by
  -- Telescoping identity: x₁..x₅ − y₁..y₅ = Σᵢ y₁..yᵢ₋₁·(xᵢ−yᵢ)·xᵢ₊₁..x₅
  have hid : x₁ * x₂ * x₃ * x₄ * x₅ - y₁ * y₂ * y₃ * y₄ * y₅ =
      (x₁ - y₁) * x₂ * x₃ * x₄ * x₅ +
      y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ +
      y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ +
      y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ +
      y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) := by noncomm_ring
  rw [hid]
  -- Bound each of the 5 telescoping terms by N⁴·‖xᵢ-yᵢ‖.
  have hN4_nn : (0 : ℝ) ≤ N ^ 4 := pow_nonneg hN_nn 4
  have hd₁_nn : 0 ≤ ‖x₁ - y₁‖ := norm_nonneg _
  have hd₂_nn : 0 ≤ ‖x₂ - y₂‖ := norm_nonneg _
  have hd₃_nn : 0 ≤ ‖x₃ - y₃‖ := norm_nonneg _
  have hd₄_nn : 0 ≤ ‖x₄ - y₄‖ := norm_nonneg _
  have hd₅_nn : 0 ≤ ‖x₅ - y₅‖ := norm_nonneg _
  -- Term i: bound ‖y₁·...·yᵢ₋₁·(xᵢ-yᵢ)·xᵢ₊₁·...·x₅‖ ≤ N^(i-1) · ‖xᵢ-yᵢ‖ · N^(5-i) = N⁴·‖xᵢ-yᵢ‖.
  have ht₁ : ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅‖ ≤ N ^ 4 * ‖x₁ - y₁‖ := by
    calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅‖
        ≤ ‖x₁ - y₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by
          calc _ ≤ ‖(x₁ - y₁) * x₂ * x₃ * x₄‖ * ‖x₅‖ := norm_mul_le _ _
            _ ≤ ‖(x₁ - y₁) * x₂ * x₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖(x₁ - y₁) * x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖x₁ - y₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
      _ ≤ ‖x₁ - y₁‖ * N * N * N * N := by gcongr
      _ = N ^ 4 * ‖x₁ - y₁‖ := by ring
  have ht₂ : ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅‖ ≤ N ^ 4 * ‖x₂ - y₂‖ := by
    calc ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅‖
        ≤ ‖y₁‖ * ‖x₂ - y₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by
          calc _ ≤ ‖y₁ * (x₂ - y₂) * x₃ * x₄‖ * ‖x₅‖ := norm_mul_le _ _
            _ ≤ ‖y₁ * (x₂ - y₂) * x₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁ * (x₂ - y₂)‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁‖ * ‖x₂ - y₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
      _ ≤ N * ‖x₂ - y₂‖ * N * N * N := by gcongr
      _ = N ^ 4 * ‖x₂ - y₂‖ := by ring
  have ht₃ : ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅‖ ≤ N ^ 4 * ‖x₃ - y₃‖ := by
    calc ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖x₃ - y₃‖ * ‖x₄‖ * ‖x₅‖ := by
          calc _ ≤ ‖y₁ * y₂ * (x₃ - y₃) * x₄‖ * ‖x₅‖ := norm_mul_le _ _
            _ ≤ ‖y₁ * y₂ * (x₃ - y₃)‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁ * y₂‖ * ‖x₃ - y₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁‖ * ‖y₂‖ * ‖x₃ - y₃‖ * ‖x₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
      _ ≤ N * N * ‖x₃ - y₃‖ * N * N := by gcongr
      _ = N ^ 4 * ‖x₃ - y₃‖ := by ring
  have ht₄ : ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅‖ ≤ N ^ 4 * ‖x₄ - y₄‖ := by
    calc ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖x₄ - y₄‖ * ‖x₅‖ := by
          calc _ ≤ ‖y₁ * y₂ * y₃ * (x₄ - y₄)‖ * ‖x₅‖ := norm_mul_le _ _
            _ ≤ ‖y₁ * y₂ * y₃‖ * ‖x₄ - y₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁ * y₂‖ * ‖y₃‖ * ‖x₄ - y₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖x₄ - y₄‖ * ‖x₅‖ := by
                gcongr; exact norm_mul_le _ _
      _ ≤ N * N * N * ‖x₄ - y₄‖ * N := by gcongr
      _ = N ^ 4 * ‖x₄ - y₄‖ := by ring
  have ht₅ : ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅)‖ ≤ N ^ 4 * ‖x₅ - y₅‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅)‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖x₅ - y₅‖ := by
          calc _ ≤ ‖y₁ * y₂ * y₃ * y₄‖ * ‖x₅ - y₅‖ := norm_mul_le _ _
            _ ≤ ‖y₁ * y₂ * y₃‖ * ‖y₄‖ * ‖x₅ - y₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁ * y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖x₅ - y₅‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖x₅ - y₅‖ := by
                gcongr; exact norm_mul_le _ _
      _ ≤ N * N * N * N * ‖x₅ - y₅‖ := by gcongr
      _ = N ^ 4 * ‖x₅ - y₅‖ := by ring
  -- Sum the 5 bounds.
  calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ +
        y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ +
        y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ +
        y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ +
        y₁ * y₂ * y₃ * y₄ * (x₅ - y₅)‖
      ≤ ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅‖ +
        ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅‖ +
        ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅‖ +
        ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅‖ +
        ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅)‖ := by
        have a4 := norm_add_le
          ((x₁-y₁)*x₂*x₃*x₄*x₅ + y₁*(x₂-y₂)*x₃*x₄*x₅ + y₁*y₂*(x₃-y₃)*x₄*x₅ +
            y₁*y₂*y₃*(x₄-y₄)*x₅) (y₁*y₂*y₃*y₄*(x₅-y₅))
        have a3 := norm_add_le
          ((x₁-y₁)*x₂*x₃*x₄*x₅ + y₁*(x₂-y₂)*x₃*x₄*x₅ + y₁*y₂*(x₃-y₃)*x₄*x₅)
          (y₁*y₂*y₃*(x₄-y₄)*x₅)
        have a2 := norm_add_le
          ((x₁-y₁)*x₂*x₃*x₄*x₅ + y₁*(x₂-y₂)*x₃*x₄*x₅) (y₁*y₂*(x₃-y₃)*x₄*x₅)
        have a1 := norm_add_le ((x₁-y₁)*x₂*x₃*x₄*x₅) (y₁*(x₂-y₂)*x₃*x₄*x₅)
        linarith
    _ ≤ N ^ 4 * ‖x₁ - y₁‖ + N ^ 4 * ‖x₂ - y₂‖ + N ^ 4 * ‖x₃ - y₃‖ +
        N ^ 4 * ‖x₄ - y₄‖ + N ^ 4 * ‖x₅ - y₅‖ := by linarith
    _ = N ^ 4 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖) := by ring

/-- **Vanishing of `sym_cubic_poly` on scalar•V inputs (B2.2.b)**:
`symmetric_bch_cubic_poly 𝕂 (α • V) (β • V) = 0` for any `α, β : 𝕂` and
`V : 𝔸`. Proof is immediate from `(α•V)·(β•V) - (β•V)·(α•V) = 0` (both
sides equal `αβ · V²`), which kills the inner commutator in the
sym_cubic_poly definition. -/
theorem symmetric_bch_cubic_poly_apply_smul_smul (V : 𝔸) (α β : 𝕂) :
    symmetric_bch_cubic_poly 𝕂 (α • V) (β • V) = 0 := by
  unfold symmetric_bch_cubic_poly
  -- Inner commutator (α•V)·(β•V) − (β•V)·(α•V) = αβ·V² − αβ·V² = 0.
  have hcomm : (α • V) * (β • V) - (β • V) * (α • V) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm β α]
    abel
  have hcomm2 : (β • V) * (α • V) - (α • V) * (β • V) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm β α]
    abel
  rw [hcomm, hcomm2]
  simp

set_option maxHeartbeats 800000 in
/-- **Vanishing on scalar•V inputs (B2.2.a)**:
`symmetric_bch_quintic_poly 𝕂 (α • V) (β • V) = 0` for any `α, β : 𝕂` and
`V : 𝔸`. See module-level docstring above for the structural significance.

Proof: each 5-letter word `x₁·x₂·x₃·x₄·x₅` with `xᵢ ∈ {α•V, β•V}` collapses
to `(α^(#a) · β^(#b)) • V⁵` via `five_fold_smul_mul_eq`. Summing the
resulting 30 scalar coefficients gives a polynomial in `(α, β)` whose
coefficient at each `α^k · β^(5−k)` is identically zero (by the calculations
in the docstring). The total is therefore `0 • V⁵ = 0`. -/
theorem symmetric_bch_quintic_poly_apply_smul_smul (V : 𝔸) (α β : 𝕂) :
    symmetric_bch_quintic_poly 𝕂 (α • V) (β • V) = 0 := by
  unfold symmetric_bch_quintic_poly
  -- Step 1: collapse each 5-fold product to (scalar) • V⁵; combine outer scalars.
  simp only [five_fold_smul_mul_eq, smul_smul, ← add_smul]
  -- Step 2: goal is now `(big_polynomial in α, β) • (V·V·V·V·V) = 0`.
  -- Convert RHS to (0:𝕂)•(V·V·V·V·V); then `congr 1` reduces to scalar = 0.
  conv_rhs => rw [show (0 : 𝔸) = (0 : 𝕂) • (V * V * V * V * V) from (zero_smul _ _).symm]
  congr 1
  -- Polynomial-in-(α, β) identity: each (k, 5−k) coefficient group sums to 0.
  ring

/-! ### B2.2.c — Lipschitz bound on (α•V + δa, β•V + δb) inputs

When the inputs are perturbations `(α•V + δa, β•V + δb)` of scalar multiples,
the symmetric quintic polynomial is bounded by `2·N⁴·(‖δa‖+‖δb‖)` rather than
the trivial `(‖α•V+δa‖+‖β•V+δb‖)⁵`. The structural vanishing on scalar•V inputs
(B2.2.a) is the source of the `δ`-linear factor; combined with the 5-letter
Lipschitz bound (`word_5_diff_le`), this gives a "linear in residual" bound.

For the Suzuki τ⁵ identification, this means `‖sym_quintic_poly(4X, Y)‖ = O(τ⁷)`
when `X, Y` have linear part `O(τ)` plus residual `O(τ³)`. -/

set_option maxHeartbeats 1600000 in
/-- **B2.2.c**: Lipschitz bound for `symmetric_bch_quintic_poly` on inputs of the
form `(α • V + δa, β • V + δb)`.

Combined with B2.2.a's vanishing on scalar•V inputs, the bound is
`O(N⁴ · (‖δa‖+‖δb‖))` rather than the trivial `(‖α•V+δa‖+‖β•V+δb‖)⁵`.

**Why this matters**: in the τ⁵ identification of `suzuki5_R5`, the inputs to
`symmetric_bch_quintic_poly` are `4X` and `Y` where `X = pτ•A + (residual O(τ³))`.
Setting `α = 4·p·τ`, `V = A`, and treating the residuals as `δa, δb = O(τ³)`,
the bound becomes `O(N⁴ · τ³)` where `N = O(τ)`, i.e., `O(τ⁷)` — gaining 2 orders
of `τ` over the trivial bound. The structural vanishing on `V`-only inputs is the
source of the extra factor of `τ²`.

Proof: B2.2.a gives `sym_quintic_poly(α•V, β•V) = 0`, so
`sym_quintic_poly(α•V+δa, β•V+δb) = sym_quintic_poly(α•V+δa, β•V+δb) - sym_quintic_poly(α•V, β•V)`.
The diff regroups into 30 paired smul-diff terms `cᵢ•(full_word - lin_word)`, each
bounded by `|cᵢ|/5760 · 5·(N⁴·D)` via `word_5_diff_le`. Summing gives `1216·5/5760·N⁴·D
≈ 1.06·N⁴·D ≤ 2·N⁴·D`. -/
theorem norm_symmetric_bch_quintic_poly_apply_smul_add_smul_add_le
    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) (N : ℝ)
    (hα_le : ‖α • V‖ ≤ N) (hβ_le : ‖β • V‖ ≤ N)
    (hα_δa_le : ‖α • V + δa‖ ≤ N) (hβ_δb_le : ‖β • V + δb‖ ≤ N)
    (hN_nn : 0 ≤ N) :
    ‖symmetric_bch_quintic_poly 𝕂 (α • V + δa) (β • V + δb)‖ ≤
      2 * N ^ 4 * (‖δa‖ + ‖δb‖) := by
  set fA := α • V + δa with hfA_def
  set fB := β • V + δb with hfB_def
  set lA := α • V with hlA_def
  set lB := β • V with hlB_def
  set D := ‖δa‖ + ‖δb‖ with hD_def
  have hD_nn : 0 ≤ D := by rw [hD_def]; positivity
  have hN4_nn : (0 : ℝ) ≤ N ^ 4 := pow_nonneg hN_nn 4
  have hN4D_nn : (0 : ℝ) ≤ N ^ 4 * D := mul_nonneg hN4_nn hD_nn
  have hdA_eq : ‖fA - lA‖ = ‖δa‖ := by rw [hfA_def, hlA_def]; congr 1; abel
  have hdB_eq : ‖fB - lB‖ = ‖δb‖ := by rw [hfB_def, hlB_def]; congr 1; abel
  have hδa_le_D : ‖δa‖ ≤ D := by rw [hD_def]; linarith [norm_nonneg δb]
  have hδb_le_D : ‖δb‖ ≤ D := by rw [hD_def]; linarith [norm_nonneg δa]
  have hdA_le : ‖fA - lA‖ ≤ D := hdA_eq ▸ hδa_le_D
  have hdB_le : ‖fB - lB‖ ≤ D := hdB_eq ▸ hδb_le_D
  have h0 : symmetric_bch_quintic_poly 𝕂 lA lB = 0 := by
    rw [hlA_def, hlB_def]
    exact symmetric_bch_quintic_poly_apply_smul_smul (𝕂 := 𝕂) V α β
  -- Per-word diff bound: `‖x₁..x₅ - y₁..y₅‖ ≤ 5·(N⁴·D)` via word_5_diff_le.
  have hword_bound : ∀ (x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : 𝔸),
      ‖x₁‖ ≤ N → ‖x₂‖ ≤ N → ‖x₃‖ ≤ N → ‖x₄‖ ≤ N → ‖x₅‖ ≤ N →
      ‖y₁‖ ≤ N → ‖y₂‖ ≤ N → ‖y₃‖ ≤ N → ‖y₄‖ ≤ N → ‖y₅‖ ≤ N →
      ‖x₁ - y₁‖ ≤ D → ‖x₂ - y₂‖ ≤ D → ‖x₃ - y₃‖ ≤ D → ‖x₄ - y₄‖ ≤ D → ‖x₅ - y₅‖ ≤ D →
      ‖x₁ * x₂ * x₃ * x₄ * x₅ - y₁ * y₂ * y₃ * y₄ * y₅‖ ≤ 5 * (N ^ 4 * D) := by
    intros x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅
      hx₁ hx₂ hx₃ hx₄ hx₅ hy₁ hy₂ hy₃ hy₄ hy₅ hd₁ hd₂ hd₃ hd₄ hd₅
    calc ‖x₁ * x₂ * x₃ * x₄ * x₅ - y₁ * y₂ * y₃ * y₄ * y₅‖
        ≤ N ^ 4 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖) :=
            word_5_diff_le x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ N
              hx₁ hx₂ hx₃ hx₄ hx₅ hy₁ hy₂ hy₃ hy₄ hy₅ hN_nn
      _ ≤ N ^ 4 * (D + D + D + D + D) := by gcongr
      _ = 5 * (N ^ 4 * D) := by ring
  -- 30 per-word diff bounds.
  have b01 := hword_bound fA fA fA fA fB lA lA lA lA lB
    hα_δa_le hα_δa_le hα_δa_le hα_δa_le hβ_δb_le hα_le hα_le hα_le hα_le hβ_le
    hdA_le hdA_le hdA_le hdA_le hdB_le
  have b02 := hword_bound fA fA fA fB fA lA lA lA lB lA
    hα_δa_le hα_δa_le hα_δa_le hβ_δb_le hα_δa_le hα_le hα_le hα_le hβ_le hα_le
    hdA_le hdA_le hdA_le hdB_le hdA_le
  have b03 := hword_bound fA fA fA fB fB lA lA lA lB lB
    hα_δa_le hα_δa_le hα_δa_le hβ_δb_le hβ_δb_le hα_le hα_le hα_le hβ_le hβ_le
    hdA_le hdA_le hdA_le hdB_le hdB_le
  have b04 := hword_bound fA fA fB fA fA lA lA lB lA lA
    hα_δa_le hα_δa_le hβ_δb_le hα_δa_le hα_δa_le hα_le hα_le hβ_le hα_le hα_le
    hdA_le hdA_le hdB_le hdA_le hdA_le
  have b05 := hword_bound fA fA fB fA fB lA lA lB lA lB
    hα_δa_le hα_δa_le hβ_δb_le hα_δa_le hβ_δb_le hα_le hα_le hβ_le hα_le hβ_le
    hdA_le hdA_le hdB_le hdA_le hdB_le
  have b06 := hword_bound fA fA fB fB fA lA lA lB lB lA
    hα_δa_le hα_δa_le hβ_δb_le hβ_δb_le hα_δa_le hα_le hα_le hβ_le hβ_le hα_le
    hdA_le hdA_le hdB_le hdB_le hdA_le
  have b07 := hword_bound fA fA fB fB fB lA lA lB lB lB
    hα_δa_le hα_δa_le hβ_δb_le hβ_δb_le hβ_δb_le hα_le hα_le hβ_le hβ_le hβ_le
    hdA_le hdA_le hdB_le hdB_le hdB_le
  have b08 := hword_bound fA fB fA fA fA lA lB lA lA lA
    hα_δa_le hβ_δb_le hα_δa_le hα_δa_le hα_δa_le hα_le hβ_le hα_le hα_le hα_le
    hdA_le hdB_le hdA_le hdA_le hdA_le
  have b09 := hword_bound fA fB fA fA fB lA lB lA lA lB
    hα_δa_le hβ_δb_le hα_δa_le hα_δa_le hβ_δb_le hα_le hβ_le hα_le hα_le hβ_le
    hdA_le hdB_le hdA_le hdA_le hdB_le
  have b10 := hword_bound fA fB fA fB fA lA lB lA lB lA
    hα_δa_le hβ_δb_le hα_δa_le hβ_δb_le hα_δa_le hα_le hβ_le hα_le hβ_le hα_le
    hdA_le hdB_le hdA_le hdB_le hdA_le
  have b11 := hword_bound fA fB fA fB fB lA lB lA lB lB
    hα_δa_le hβ_δb_le hα_δa_le hβ_δb_le hβ_δb_le hα_le hβ_le hα_le hβ_le hβ_le
    hdA_le hdB_le hdA_le hdB_le hdB_le
  have b12 := hword_bound fA fB fB fA fA lA lB lB lA lA
    hα_δa_le hβ_δb_le hβ_δb_le hα_δa_le hα_δa_le hα_le hβ_le hβ_le hα_le hα_le
    hdA_le hdB_le hdB_le hdA_le hdA_le
  have b13 := hword_bound fA fB fB fA fB lA lB lB lA lB
    hα_δa_le hβ_δb_le hβ_δb_le hα_δa_le hβ_δb_le hα_le hβ_le hβ_le hα_le hβ_le
    hdA_le hdB_le hdB_le hdA_le hdB_le
  have b14 := hword_bound fA fB fB fB fA lA lB lB lB lA
    hα_δa_le hβ_δb_le hβ_δb_le hβ_δb_le hα_δa_le hα_le hβ_le hβ_le hβ_le hα_le
    hdA_le hdB_le hdB_le hdB_le hdA_le
  have b15 := hword_bound fA fB fB fB fB lA lB lB lB lB
    hα_δa_le hβ_δb_le hβ_δb_le hβ_δb_le hβ_δb_le hα_le hβ_le hβ_le hβ_le hβ_le
    hdA_le hdB_le hdB_le hdB_le hdB_le
  have b16 := hword_bound fB fA fA fA fA lB lA lA lA lA
    hβ_δb_le hα_δa_le hα_δa_le hα_δa_le hα_δa_le hβ_le hα_le hα_le hα_le hα_le
    hdB_le hdA_le hdA_le hdA_le hdA_le
  have b17 := hword_bound fB fA fA fA fB lB lA lA lA lB
    hβ_δb_le hα_δa_le hα_δa_le hα_δa_le hβ_δb_le hβ_le hα_le hα_le hα_le hβ_le
    hdB_le hdA_le hdA_le hdA_le hdB_le
  have b18 := hword_bound fB fA fA fB fA lB lA lA lB lA
    hβ_δb_le hα_δa_le hα_δa_le hβ_δb_le hα_δa_le hβ_le hα_le hα_le hβ_le hα_le
    hdB_le hdA_le hdA_le hdB_le hdA_le
  have b19 := hword_bound fB fA fA fB fB lB lA lA lB lB
    hβ_δb_le hα_δa_le hα_δa_le hβ_δb_le hβ_δb_le hβ_le hα_le hα_le hβ_le hβ_le
    hdB_le hdA_le hdA_le hdB_le hdB_le
  have b20 := hword_bound fB fA fB fA fA lB lA lB lA lA
    hβ_δb_le hα_δa_le hβ_δb_le hα_δa_le hα_δa_le hβ_le hα_le hβ_le hα_le hα_le
    hdB_le hdA_le hdB_le hdA_le hdA_le
  have b21 := hword_bound fB fA fB fA fB lB lA lB lA lB
    hβ_δb_le hα_δa_le hβ_δb_le hα_δa_le hβ_δb_le hβ_le hα_le hβ_le hα_le hβ_le
    hdB_le hdA_le hdB_le hdA_le hdB_le
  have b22 := hword_bound fB fA fB fB fA lB lA lB lB lA
    hβ_δb_le hα_δa_le hβ_δb_le hβ_δb_le hα_δa_le hβ_le hα_le hβ_le hβ_le hα_le
    hdB_le hdA_le hdB_le hdB_le hdA_le
  have b23 := hword_bound fB fA fB fB fB lB lA lB lB lB
    hβ_δb_le hα_δa_le hβ_δb_le hβ_δb_le hβ_δb_le hβ_le hα_le hβ_le hβ_le hβ_le
    hdB_le hdA_le hdB_le hdB_le hdB_le
  have b24 := hword_bound fB fB fA fA fA lB lB lA lA lA
    hβ_δb_le hβ_δb_le hα_δa_le hα_δa_le hα_δa_le hβ_le hβ_le hα_le hα_le hα_le
    hdB_le hdB_le hdA_le hdA_le hdA_le
  have b25 := hword_bound fB fB fA fA fB lB lB lA lA lB
    hβ_δb_le hβ_δb_le hα_δa_le hα_δa_le hβ_δb_le hβ_le hβ_le hα_le hα_le hβ_le
    hdB_le hdB_le hdA_le hdA_le hdB_le
  have b26 := hword_bound fB fB fA fB fA lB lB lA lB lA
    hβ_δb_le hβ_δb_le hα_δa_le hβ_δb_le hα_δa_le hβ_le hβ_le hα_le hβ_le hα_le
    hdB_le hdB_le hdA_le hdB_le hdA_le
  have b27 := hword_bound fB fB fA fB fB lB lB lA lB lB
    hβ_δb_le hβ_δb_le hα_δa_le hβ_δb_le hβ_δb_le hβ_le hβ_le hα_le hβ_le hβ_le
    hdB_le hdB_le hdA_le hdB_le hdB_le
  have b28 := hword_bound fB fB fB fA fA lB lB lB lA lA
    hβ_δb_le hβ_δb_le hβ_δb_le hα_δa_le hα_δa_le hβ_le hβ_le hβ_le hα_le hα_le
    hdB_le hdB_le hdB_le hdA_le hdA_le
  have b29 := hword_bound fB fB fB fA fB lB lB lB lA lB
    hβ_δb_le hβ_δb_le hβ_δb_le hα_δa_le hβ_δb_le hβ_le hβ_le hβ_le hα_le hβ_le
    hdB_le hdB_le hdB_le hdA_le hdB_le
  have b30 := hword_bound fB fB fB fB fA lB lB lB lB lA
    hβ_δb_le hβ_δb_le hβ_δb_le hβ_δb_le hα_δa_le hβ_le hβ_le hβ_le hβ_le hα_le
    hdB_le hdB_le hdB_le hdB_le hdA_le
  -- Scaled-diff per-term bound: `‖(k/5760 : 𝕂) • w‖ ≤ |k|/5760 · 5·(N⁴·D)`.
  have h_scaled_le : ∀ (k : ℤ) (w : 𝔸),
      ‖w‖ ≤ 5 * (N ^ 4 * D) →
      ‖(((k : ℤ) : 𝕂) / 5760) • w‖ ≤ |(k : ℝ)| / 5760 * (5 * (N ^ 4 * D)) := by
    intros k w hw
    have h5760_norm : ‖(5760 : 𝕂)‖ = 5760 := by
      rw [show (5760 : 𝕂) = ((5760 : ℕ) : 𝕂) from by norm_cast, RCLike.norm_natCast]
      norm_num
    have hc_nn : (0 : ℝ) ≤ |(k : ℝ)| / 5760 := by positivity
    have hk_norm : ‖((k : ℤ) : 𝕂)‖ = |(k : ℝ)| := by
      rw [show ((k : ℤ) : 𝕂) = ((k : ℝ) : 𝕂) from by push_cast; rfl, RCLike.norm_ofReal]
    calc ‖(((k : ℤ) : 𝕂) / 5760) • w‖
        ≤ ‖(((k : ℤ) : 𝕂) / 5760)‖ * ‖w‖ := norm_smul_le _ _
      _ = |(k : ℝ)| / 5760 * ‖w‖ := by rw [norm_div, h5760_norm, hk_norm]
      _ ≤ |(k : ℝ)| / 5760 * (5 * (N ^ 4 * D)) := mul_le_mul_of_nonneg_left hw hc_nn
  -- 30 per-term smul-diff bounds.
  have t01 : ‖(7 / 5760 : 𝕂) • (fA * fA * fA * fA * fB - lA * lA * lA * lA * lB)‖ ≤
      7 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (7) (fA * fA * fA * fA * fB - lA * lA * lA * lA * lB) b01
    have heq : ((7 : ℤ) : 𝕂) / 5760 = (7 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((7 : ℤ) : ℝ)| = 7 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t02 : ‖(-28 / 5760 : 𝕂) • (fA * fA * fA * fB * fA - lA * lA * lA * lB * lA)‖ ≤
      28 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-28) (fA * fA * fA * fB * fA - lA * lA * lA * lB * lA) b02
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t03 : ‖(-28 / 5760 : 𝕂) • (fA * fA * fA * fB * fB - lA * lA * lA * lB * lB)‖ ≤
      28 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-28) (fA * fA * fA * fB * fB - lA * lA * lA * lB * lB) b03
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t04 : ‖(42 / 5760 : 𝕂) • (fA * fA * fB * fA * fA - lA * lA * lB * lA * lA)‖ ≤
      42 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (42) (fA * fA * fB * fA * fA - lA * lA * lB * lA * lA) b04
    have heq : ((42 : ℤ) : 𝕂) / 5760 = (42 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((42 : ℤ) : ℝ)| = 42 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t05 : ‖(72 / 5760 : 𝕂) • (fA * fA * fB * fA * fB - lA * lA * lB * lA * lB)‖ ≤
      72 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (72) (fA * fA * fB * fA * fB - lA * lA * lB * lA * lB) b05
    have heq : ((72 : ℤ) : 𝕂) / 5760 = (72 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((72 : ℤ) : ℝ)| = 72 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t06 : ‖(12 / 5760 : 𝕂) • (fA * fA * fB * fB * fA - lA * lA * lB * lB * lA)‖ ≤
      12 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (12) (fA * fA * fB * fB * fA - lA * lA * lB * lB * lA) b06
    have heq : ((12 : ℤ) : 𝕂) / 5760 = (12 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((12 : ℤ) : ℝ)| = 12 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t07 : ‖(32 / 5760 : 𝕂) • (fA * fA * fB * fB * fB - lA * lA * lB * lB * lB)‖ ≤
      32 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (32) (fA * fA * fB * fB * fB - lA * lA * lB * lB * lB) b07
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t08 : ‖(-28 / 5760 : 𝕂) • (fA * fB * fA * fA * fA - lA * lB * lA * lA * lA)‖ ≤
      28 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-28) (fA * fB * fA * fA * fA - lA * lB * lA * lA * lA) b08
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t09 : ‖(-48 / 5760 : 𝕂) • (fA * fB * fA * fA * fB - lA * lB * lA * lA * lB)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fA * fB * fA * fA * fB - lA * lB * lA * lA * lB) b09
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t10 : ‖(-48 / 5760 : 𝕂) • (fA * fB * fA * fB * fA - lA * lB * lA * lB * lA)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fA * fB * fA * fB * fA - lA * lB * lA * lB * lA) b10
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t11 : ‖(-48 / 5760 : 𝕂) • (fA * fB * fA * fB * fB - lA * lB * lA * lB * lB)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fA * fB * fA * fB * fB - lA * lB * lA * lB * lB) b11
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t12 : ‖(12 / 5760 : 𝕂) • (fA * fB * fB * fA * fA - lA * lB * lB * lA * lA)‖ ≤
      12 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (12) (fA * fB * fB * fA * fA - lA * lB * lB * lA * lA) b12
    have heq : ((12 : ℤ) : 𝕂) / 5760 = (12 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((12 : ℤ) : ℝ)| = 12 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t13 : ‖(-48 / 5760 : 𝕂) • (fA * fB * fB * fA * fB - lA * lB * lB * lA * lB)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fA * fB * fB * fA * fB - lA * lB * lB * lA * lB) b13
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t14 : ‖(32 / 5760 : 𝕂) • (fA * fB * fB * fB * fA - lA * lB * lB * lB * lA)‖ ≤
      32 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (32) (fA * fB * fB * fB * fA - lA * lB * lB * lB * lA) b14
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t15 : ‖(-8 / 5760 : 𝕂) • (fA * fB * fB * fB * fB - lA * lB * lB * lB * lB)‖ ≤
      8 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-8) (fA * fB * fB * fB * fB - lA * lB * lB * lB * lB) b15
    have heq : ((-8 : ℤ) : 𝕂) / 5760 = (-8 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-8 : ℤ) : ℝ)| = 8 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t16 : ‖(7 / 5760 : 𝕂) • (fB * fA * fA * fA * fA - lB * lA * lA * lA * lA)‖ ≤
      7 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (7) (fB * fA * fA * fA * fA - lB * lA * lA * lA * lA) b16
    have heq : ((7 : ℤ) : 𝕂) / 5760 = (7 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((7 : ℤ) : ℝ)| = 7 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t17 : ‖(32 / 5760 : 𝕂) • (fB * fA * fA * fA * fB - lB * lA * lA * lA * lB)‖ ≤
      32 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (32) (fB * fA * fA * fA * fB - lB * lA * lA * lA * lB) b17
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t18 : ‖(-48 / 5760 : 𝕂) • (fB * fA * fA * fB * fA - lB * lA * lA * lB * lA)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fB * fA * fA * fB * fA - lB * lA * lA * lB * lA) b18
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t19 : ‖(-48 / 5760 : 𝕂) • (fB * fA * fA * fB * fB - lB * lA * lA * lB * lB)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fB * fA * fA * fB * fB - lB * lA * lA * lB * lB) b19
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t20 : ‖(72 / 5760 : 𝕂) • (fB * fA * fB * fA * fA - lB * lA * lB * lA * lA)‖ ≤
      72 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (72) (fB * fA * fB * fA * fA - lB * lA * lB * lA * lA) b20
    have heq : ((72 : ℤ) : 𝕂) / 5760 = (72 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((72 : ℤ) : ℝ)| = 72 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t21 : ‖(192 / 5760 : 𝕂) • (fB * fA * fB * fA * fB - lB * lA * lB * lA * lB)‖ ≤
      192 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (192) (fB * fA * fB * fA * fB - lB * lA * lB * lA * lB) b21
    have heq : ((192 : ℤ) : 𝕂) / 5760 = (192 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((192 : ℤ) : ℝ)| = 192 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t22 : ‖(-48 / 5760 : 𝕂) • (fB * fA * fB * fB * fA - lB * lA * lB * lB * lA)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fB * fA * fB * fB * fA - lB * lA * lB * lB * lA) b22
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t23 : ‖(32 / 5760 : 𝕂) • (fB * fA * fB * fB * fB - lB * lA * lB * lB * lB)‖ ≤
      32 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (32) (fB * fA * fB * fB * fB - lB * lA * lB * lB * lB) b23
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t24 : ‖(-28 / 5760 : 𝕂) • (fB * fB * fA * fA * fA - lB * lB * lA * lA * lA)‖ ≤
      28 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-28) (fB * fB * fA * fA * fA - lB * lB * lA * lA * lA) b24
    have heq : ((-28 : ℤ) : 𝕂) / 5760 = (-28 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-28 : ℤ) : ℝ)| = 28 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t25 : ‖(-48 / 5760 : 𝕂) • (fB * fB * fA * fA * fB - lB * lB * lA * lA * lB)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fB * fB * fA * fA * fB - lB * lB * lA * lA * lB) b25
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t26 : ‖(-48 / 5760 : 𝕂) • (fB * fB * fA * fB * fA - lB * lB * lA * lB * lA)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fB * fB * fA * fB * fA - lB * lB * lA * lB * lA) b26
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t27 : ‖(-48 / 5760 : 𝕂) • (fB * fB * fA * fB * fB - lB * lB * lA * lB * lB)‖ ≤
      48 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-48) (fB * fB * fA * fB * fB - lB * lB * lA * lB * lB) b27
    have heq : ((-48 : ℤ) : 𝕂) / 5760 = (-48 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-48 : ℤ) : ℝ)| = 48 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t28 : ‖(32 / 5760 : 𝕂) • (fB * fB * fB * fA * fA - lB * lB * lB * lA * lA)‖ ≤
      32 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (32) (fB * fB * fB * fA * fA - lB * lB * lB * lA * lA) b28
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t29 : ‖(32 / 5760 : 𝕂) • (fB * fB * fB * fA * fB - lB * lB * lB * lA * lB)‖ ≤
      32 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (32) (fB * fB * fB * fA * fB - lB * lB * lB * lA * lB) b29
    have heq : ((32 : ℤ) : 𝕂) / 5760 = (32 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((32 : ℤ) : ℝ)| = 32 := by push_cast; norm_num
    rw [habs] at this; exact this
  have t30 : ‖(-8 / 5760 : 𝕂) • (fB * fB * fB * fB * fA - lB * lB * lB * lB * lA)‖ ≤
      8 / 5760 * (5 * (N ^ 4 * D)) := by
    have := h_scaled_le (-8) (fB * fB * fB * fB * fA - lB * lB * lB * lB * lA) b30
    have heq : ((-8 : ℤ) : 𝕂) / 5760 = (-8 / 5760 : 𝕂) := by push_cast; ring
    rw [heq] at this
    have habs : |((-8 : ℤ) : ℝ)| = 8 := by push_cast; norm_num
    rw [habs] at this; exact this
  -- Regrouping identity: sym_quintic_poly fA fB = Σ cᵢ • (full_word_i - lin_word_i).
  have hregroup : symmetric_bch_quintic_poly 𝕂 fA fB =
      (7 / 5760 : 𝕂) • (fA * fA * fA * fA * fB - lA * lA * lA * lA * lB) +
      (-28 / 5760 : 𝕂) • (fA * fA * fA * fB * fA - lA * lA * lA * lB * lA) +
      (-28 / 5760 : 𝕂) • (fA * fA * fA * fB * fB - lA * lA * lA * lB * lB) +
      (42 / 5760 : 𝕂) • (fA * fA * fB * fA * fA - lA * lA * lB * lA * lA) +
      (72 / 5760 : 𝕂) • (fA * fA * fB * fA * fB - lA * lA * lB * lA * lB) +
      (12 / 5760 : 𝕂) • (fA * fA * fB * fB * fA - lA * lA * lB * lB * lA) +
      (32 / 5760 : 𝕂) • (fA * fA * fB * fB * fB - lA * lA * lB * lB * lB) +
      (-28 / 5760 : 𝕂) • (fA * fB * fA * fA * fA - lA * lB * lA * lA * lA) +
      (-48 / 5760 : 𝕂) • (fA * fB * fA * fA * fB - lA * lB * lA * lA * lB) +
      (-48 / 5760 : 𝕂) • (fA * fB * fA * fB * fA - lA * lB * lA * lB * lA) +
      (-48 / 5760 : 𝕂) • (fA * fB * fA * fB * fB - lA * lB * lA * lB * lB) +
      (12 / 5760 : 𝕂) • (fA * fB * fB * fA * fA - lA * lB * lB * lA * lA) +
      (-48 / 5760 : 𝕂) • (fA * fB * fB * fA * fB - lA * lB * lB * lA * lB) +
      (32 / 5760 : 𝕂) • (fA * fB * fB * fB * fA - lA * lB * lB * lB * lA) +
      (-8 / 5760 : 𝕂) • (fA * fB * fB * fB * fB - lA * lB * lB * lB * lB) +
      (7 / 5760 : 𝕂) • (fB * fA * fA * fA * fA - lB * lA * lA * lA * lA) +
      (32 / 5760 : 𝕂) • (fB * fA * fA * fA * fB - lB * lA * lA * lA * lB) +
      (-48 / 5760 : 𝕂) • (fB * fA * fA * fB * fA - lB * lA * lA * lB * lA) +
      (-48 / 5760 : 𝕂) • (fB * fA * fA * fB * fB - lB * lA * lA * lB * lB) +
      (72 / 5760 : 𝕂) • (fB * fA * fB * fA * fA - lB * lA * lB * lA * lA) +
      (192 / 5760 : 𝕂) • (fB * fA * fB * fA * fB - lB * lA * lB * lA * lB) +
      (-48 / 5760 : 𝕂) • (fB * fA * fB * fB * fA - lB * lA * lB * lB * lA) +
      (32 / 5760 : 𝕂) • (fB * fA * fB * fB * fB - lB * lA * lB * lB * lB) +
      (-28 / 5760 : 𝕂) • (fB * fB * fA * fA * fA - lB * lB * lA * lA * lA) +
      (-48 / 5760 : 𝕂) • (fB * fB * fA * fA * fB - lB * lB * lA * lA * lB) +
      (-48 / 5760 : 𝕂) • (fB * fB * fA * fB * fA - lB * lB * lA * lB * lA) +
      (-48 / 5760 : 𝕂) • (fB * fB * fA * fB * fB - lB * lB * lA * lB * lB) +
      (32 / 5760 : 𝕂) • (fB * fB * fB * fA * fA - lB * lB * lB * lA * lA) +
      (32 / 5760 : 𝕂) • (fB * fB * fB * fA * fB - lB * lB * lB * lA * lB) +
      (-8 / 5760 : 𝕂) • (fB * fB * fB * fB * fA - lB * lB * lB * lB * lA)
      := by
    rw [show symmetric_bch_quintic_poly 𝕂 fA fB =
        symmetric_bch_quintic_poly 𝕂 fA fB - symmetric_bch_quintic_poly 𝕂 lA lB
        from by rw [h0, sub_zero]]
    unfold symmetric_bch_quintic_poly
    simp only [smul_sub]
    abel
  rw [hregroup]
  -- Set T_i abbreviations for the 30 paired smul-diff terms.
  set T01 := (7 / 5760 : 𝕂) • (fA * fA * fA * fA * fB - lA * lA * lA * lA * lB) with hT01
  set T02 := (-28 / 5760 : 𝕂) • (fA * fA * fA * fB * fA - lA * lA * lA * lB * lA) with hT02
  set T03 := (-28 / 5760 : 𝕂) • (fA * fA * fA * fB * fB - lA * lA * lA * lB * lB) with hT03
  set T04 := (42 / 5760 : 𝕂) • (fA * fA * fB * fA * fA - lA * lA * lB * lA * lA) with hT04
  set T05 := (72 / 5760 : 𝕂) • (fA * fA * fB * fA * fB - lA * lA * lB * lA * lB) with hT05
  set T06 := (12 / 5760 : 𝕂) • (fA * fA * fB * fB * fA - lA * lA * lB * lB * lA) with hT06
  set T07 := (32 / 5760 : 𝕂) • (fA * fA * fB * fB * fB - lA * lA * lB * lB * lB) with hT07
  set T08 := (-28 / 5760 : 𝕂) • (fA * fB * fA * fA * fA - lA * lB * lA * lA * lA) with hT08
  set T09 := (-48 / 5760 : 𝕂) • (fA * fB * fA * fA * fB - lA * lB * lA * lA * lB) with hT09
  set T10 := (-48 / 5760 : 𝕂) • (fA * fB * fA * fB * fA - lA * lB * lA * lB * lA) with hT10
  set T11 := (-48 / 5760 : 𝕂) • (fA * fB * fA * fB * fB - lA * lB * lA * lB * lB) with hT11
  set T12 := (12 / 5760 : 𝕂) • (fA * fB * fB * fA * fA - lA * lB * lB * lA * lA) with hT12
  set T13 := (-48 / 5760 : 𝕂) • (fA * fB * fB * fA * fB - lA * lB * lB * lA * lB) with hT13
  set T14 := (32 / 5760 : 𝕂) • (fA * fB * fB * fB * fA - lA * lB * lB * lB * lA) with hT14
  set T15 := (-8 / 5760 : 𝕂) • (fA * fB * fB * fB * fB - lA * lB * lB * lB * lB) with hT15
  set T16 := (7 / 5760 : 𝕂) • (fB * fA * fA * fA * fA - lB * lA * lA * lA * lA) with hT16
  set T17 := (32 / 5760 : 𝕂) • (fB * fA * fA * fA * fB - lB * lA * lA * lA * lB) with hT17
  set T18 := (-48 / 5760 : 𝕂) • (fB * fA * fA * fB * fA - lB * lA * lA * lB * lA) with hT18
  set T19 := (-48 / 5760 : 𝕂) • (fB * fA * fA * fB * fB - lB * lA * lA * lB * lB) with hT19
  set T20 := (72 / 5760 : 𝕂) • (fB * fA * fB * fA * fA - lB * lA * lB * lA * lA) with hT20
  set T21 := (192 / 5760 : 𝕂) • (fB * fA * fB * fA * fB - lB * lA * lB * lA * lB) with hT21
  set T22 := (-48 / 5760 : 𝕂) • (fB * fA * fB * fB * fA - lB * lA * lB * lB * lA) with hT22
  set T23 := (32 / 5760 : 𝕂) • (fB * fA * fB * fB * fB - lB * lA * lB * lB * lB) with hT23
  set T24 := (-28 / 5760 : 𝕂) • (fB * fB * fA * fA * fA - lB * lB * lA * lA * lA) with hT24
  set T25 := (-48 / 5760 : 𝕂) • (fB * fB * fA * fA * fB - lB * lB * lA * lA * lB) with hT25
  set T26 := (-48 / 5760 : 𝕂) • (fB * fB * fA * fB * fA - lB * lB * lA * lB * lA) with hT26
  set T27 := (-48 / 5760 : 𝕂) • (fB * fB * fA * fB * fB - lB * lB * lA * lB * lB) with hT27
  set T28 := (32 / 5760 : 𝕂) • (fB * fB * fB * fA * fA - lB * lB * lB * lA * lA) with hT28
  set T29 := (32 / 5760 : 𝕂) • (fB * fB * fB * fA * fB - lB * lB * lB * lA * lB) with hT29
  set T30 := (-8 / 5760 : 𝕂) • (fB * fB * fB * fB * fA - lB * lB * lB * lB * lA) with hT30
  -- 29-step triangle inequality chain via norm_add_le.
  have S02 : ‖T01 + T02‖ ≤
      ‖T01‖ + ‖T02‖ := norm_add_le _ _
  have S03 : ‖T01 + T02 + T03‖ ≤
      ‖T01 + T02‖ + ‖T03‖ := norm_add_le _ _
  have S04 : ‖T01 + T02 + T03 + T04‖ ≤
      ‖T01 + T02 + T03‖ + ‖T04‖ := norm_add_le _ _
  have S05 : ‖T01 + T02 + T03 + T04 + T05‖ ≤
      ‖T01 + T02 + T03 + T04‖ + ‖T05‖ := norm_add_le _ _
  have S06 : ‖T01 + T02 + T03 + T04 + T05 + T06‖ ≤
      ‖T01 + T02 + T03 + T04 + T05‖ + ‖T06‖ := norm_add_le _ _
  have S07 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06‖ + ‖T07‖ := norm_add_le _ _
  have S08 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07‖ + ‖T08‖ := norm_add_le _ _
  have S09 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08‖ + ‖T09‖ := norm_add_le _ _
  have S10 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09‖ + ‖T10‖ := norm_add_le _ _
  have S11 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10‖ + ‖T11‖ := norm_add_le _ _
  have S12 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11‖ + ‖T12‖ := norm_add_le _ _
  have S13 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12‖ + ‖T13‖ := norm_add_le _ _
  have S14 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13‖ + ‖T14‖ := norm_add_le _ _
  have S15 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14‖ + ‖T15‖ := norm_add_le _ _
  have S16 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15‖ + ‖T16‖ := norm_add_le _ _
  have S17 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16‖ + ‖T17‖ := norm_add_le _ _
  have S18 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17‖ + ‖T18‖ := norm_add_le _ _
  have S19 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18‖ + ‖T19‖ := norm_add_le _ _
  have S20 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19‖ + ‖T20‖ := norm_add_le _ _
  have S21 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20‖ + ‖T21‖ := norm_add_le _ _
  have S22 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21‖ + ‖T22‖ := norm_add_le _ _
  have S23 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22‖ + ‖T23‖ := norm_add_le _ _
  have S24 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23‖ + ‖T24‖ := norm_add_le _ _
  have S25 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24‖ + ‖T25‖ := norm_add_le _ _
  have S26 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25‖ + ‖T26‖ := norm_add_le _ _
  have S27 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26‖ + ‖T27‖ := norm_add_le _ _
  have S28 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27‖ + ‖T28‖ := norm_add_le _ _
  have S29 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28 + T29‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28‖ + ‖T29‖ := norm_add_le _ _
  have S30 : ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28 + T29 + T30‖ ≤
      ‖T01 + T02 + T03 + T04 + T05 + T06 + T07 + T08 + T09 + T10 + T11 + T12 + T13 + T14 + T15 + T16 + T17 + T18 + T19 + T20 + T21 + T22 + T23 + T24 + T25 + T26 + T27 + T28 + T29‖ + ‖T30‖ := norm_add_le _ _
  -- Σ |c|/5760 · 5·(N⁴·D) = 1216·5/5760·N⁴·D ≈ 1.056·N⁴·D ≤ 2·N⁴·D.
  -- Goal: 2 * N^4 * D atomized as 2 * (N^4 * D).
  have hgoal_eq : 2 * N ^ 4 * (‖δa‖ + ‖δb‖) = 2 * (N ^ 4 * D) := by rw [hD_def]; ring
  rw [hgoal_eq]
  linarith [t01, t02, t03, t04, t05, t06, t07, t08, t09, t10,
            t11, t12, t13, t14, t15, t16, t17, t18, t19, t20,
            t21, t22, t23, t24, t25, t26, t27, t28, t29, t30,
            S02, S03, S04, S05, S06, S07, S08, S09, S10,
            S11, S12, S13, S14, S15, S16, S17, S18, S19, S20,
            S21, S22, S23, S24, S25, S26, S27, S28, S29, S30,
            hN4D_nn]

end SymmetricQuinticPoly

/-!
## Alt-form decomposition of `symmetric_bch_quintic_poly`

CAS-derived (`Lean-Trotter/scripts/discover_quintic_alt_form.py`):

    sym_E₅(a, b) = bch_quintic_term(½a, b)
                 + bch_quintic_term(½a + b, ½a)
                 + symmetric_bch_quintic_correction_poly(a, b)

The correction polynomial is a 25-term degree-5 polynomial in `{a, b}` with
common denominator `11520` and integer numerators in
`{±15, ±20, ±30, ±40, ±50, ±60, ±90, ±110, ±160}`. It captures the three
remaining contributions:
- `½·[bch_quartic_term(½a, b), ½a]` (degree-5 from ½[z, ½a])
- `(C₃(z, ½a) − C₃(½a+b, ½a))_d5` (linear-in-z_d3 + bilinear-in-z_d2)
- `(C₄(z, ½a) − C₄(½a+b, ½a))_d5` (linear-in-z_d3 + linear-in-z_d2)

This is the analog of `symmetric_bch_cubic_poly_alt_form` (Basic.lean) at
one degree higher, and is the key infrastructure for discharging the B1.c
Tier-2 axiom `symmetric_bch_quintic_sub_poly_axiom`.
-/

section SymmetricQuinticAltForm

variable {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- **Quintic correction polynomial** — the 25-term degree-5 polynomial in
`{a, b}` that captures `sym_E₅(a, b) − bch_quintic_term(½a, b) −
bch_quintic_term(½a+b, ½a)`. CAS-derived; common denominator `11520`. -/
noncomputable def symmetric_bch_quintic_correction_poly (𝕂 : Type*) [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
    (15 / 11520 : 𝕂) • (a * a * a * a * b)
  + (-60 / 11520 : 𝕂) • (a * a * a * b * a)
  + (-50 / 11520 : 𝕂) • (a * a * a * b * b)
  + (90 / 11520 : 𝕂) • (a * a * b * a * a)
  + (110 / 11520 : 𝕂) • (a * a * b * a * b)
  + (40 / 11520 : 𝕂) • (a * a * b * b * a)
  + (20 / 11520 : 𝕂) • (a * a * b * b * b)
  + (-60 / 11520 : 𝕂) • (a * b * a * a * a)
  + (-30 / 11520 : 𝕂) • (a * b * a * a * b)
  + (-160 / 11520 : 𝕂) • (a * b * a * b * a)
  + (-20 / 11520 : 𝕂) • (a * b * a * b * b)
  + (40 / 11520 : 𝕂) • (a * b * b * a * a)
  + (-60 / 11520 : 𝕂) • (a * b * b * a * b)
  + (40 / 11520 : 𝕂) • (a * b * b * b * a)
  + (15 / 11520 : 𝕂) • (b * a * a * a * a)
  + (20 / 11520 : 𝕂) • (b * a * a * a * b)
  + (-30 / 11520 : 𝕂) • (b * a * a * b * a)
  + (-40 / 11520 : 𝕂) • (b * a * a * b * b)
  + (110 / 11520 : 𝕂) • (b * a * b * a * a)
  + (160 / 11520 : 𝕂) • (b * a * b * a * b)
  + (-60 / 11520 : 𝕂) • (b * a * b * b * a)
  + (-50 / 11520 : 𝕂) • (b * b * a * a * a)
  + (-40 / 11520 : 𝕂) • (b * b * a * a * b)
  + (-20 / 11520 : 𝕂) • (b * b * a * b * a)
  + (20 / 11520 : 𝕂) • (b * b * b * a * a)

private lemma norm_correction_word_le_helper (𝕂 : Type*) [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (k : ℤ) (w : 𝔸) (s : ℝ) (hw : ‖w‖ ≤ s ^ 5) (hs_nn : 0 ≤ s) :
    ‖((k : 𝕂) / 11520) • w‖ ≤ |(k : ℝ)| / 11520 * s ^ 5 := by
  have h11520_norm : ‖(11520 : 𝕂)‖ = 11520 := by
    rw [show (11520 : 𝕂) = ((11520 : ℕ) : 𝕂) from by norm_cast, RCLike.norm_natCast]
    norm_num
  have hc_nn : (0 : ℝ) ≤ |(k : ℝ)| / 11520 := by positivity
  have hk_norm : ‖((k : ℤ) : 𝕂)‖ = |(k : ℝ)| := by
    rw [show ((k : ℤ) : 𝕂) = ((k : ℝ) : 𝕂) from by push_cast; rfl, RCLike.norm_ofReal]
  calc ‖((k : 𝕂) / 11520) • w‖
      ≤ ‖((k : 𝕂) / 11520)‖ * ‖w‖ := norm_smul_le _ _
    _ = |(k : ℝ)| / 11520 * ‖w‖ := by
        rw [norm_div, h11520_norm, hk_norm]
    _ ≤ |(k : ℝ)| / 11520 * s ^ 5 := mul_le_mul_of_nonneg_left hw hc_nn

/-- **Norm bound for `symmetric_bch_quintic_correction_poly`** (T2-G):
`‖correction(a, b)‖ ≤ (‖a‖+‖b‖)⁵`.

CAS: sum of |numerators| over the 25 terms = 1360. So sum of bounds is
1360/11520 · s⁵ ≈ 0.118 · s⁵ ≤ s⁵.

The proof uses the auxiliary `norm_correction_word_le_helper` and standard
triangle inequality, integer-cast bridge for each of the 25 terms. -/
theorem norm_symmetric_bch_quintic_correction_poly_le (a b : 𝔸) :
    ‖symmetric_bch_quintic_correction_poly 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs5_nn : (0 : ℝ) ≤ s ^ 5 := pow_nonneg hs_nn 5
  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]
  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]
  -- Helper: 5-letter word norm.
  have hw : ∀ (x₁ x₂ x₃ x₄ x₅ : 𝔸), ‖x₁‖ ≤ s → ‖x₂‖ ≤ s → ‖x₃‖ ≤ s →
      ‖x₄‖ ≤ s → ‖x₅‖ ≤ s → ‖x₁ * x₂ * x₃ * x₄ * x₅‖ ≤ s ^ 5 :=
    fun x₁ x₂ x₃ x₄ x₅ h₁ h₂ h₃ h₄ h₅ => by
      have := norm_five_word_le (𝔸 := 𝔸) a b x₁ x₂ x₃ x₄ x₅
        (by rw [hs_def] at h₁; exact h₁) (by rw [hs_def] at h₂; exact h₂)
        (by rw [hs_def] at h₃; exact h₃) (by rw [hs_def] at h₄; exact h₄)
        (by rw [hs_def] at h₅; exact h₅)
      rw [hs_def]; exact this
  -- 25 word norm bounds (matches the 25 terms of correction_poly).
  have w01 := hw a a a a b ha_le ha_le ha_le ha_le hb_le
  have w02 := hw a a a b a ha_le ha_le ha_le hb_le ha_le
  have w03 := hw a a a b b ha_le ha_le ha_le hb_le hb_le
  have w04 := hw a a b a a ha_le ha_le hb_le ha_le ha_le
  have w05 := hw a a b a b ha_le ha_le hb_le ha_le hb_le
  have w06 := hw a a b b a ha_le ha_le hb_le hb_le ha_le
  have w07 := hw a a b b b ha_le ha_le hb_le hb_le hb_le
  have w08 := hw a b a a a ha_le hb_le ha_le ha_le ha_le
  have w09 := hw a b a a b ha_le hb_le ha_le ha_le hb_le
  have w10 := hw a b a b a ha_le hb_le ha_le hb_le ha_le
  have w11 := hw a b a b b ha_le hb_le ha_le hb_le hb_le
  have w12 := hw a b b a a ha_le hb_le hb_le ha_le ha_le
  have w13 := hw a b b a b ha_le hb_le hb_le ha_le hb_le
  have w14 := hw a b b b a ha_le hb_le hb_le hb_le ha_le
  have w15 := hw b a a a a hb_le ha_le ha_le ha_le ha_le
  have w16 := hw b a a a b hb_le ha_le ha_le ha_le hb_le
  have w17 := hw b a a b a hb_le ha_le ha_le hb_le ha_le
  have w18 := hw b a a b b hb_le ha_le ha_le hb_le hb_le
  have w19 := hw b a b a a hb_le ha_le hb_le ha_le ha_le
  have w20 := hw b a b a b hb_le ha_le hb_le ha_le hb_le
  have w21 := hw b a b b a hb_le ha_le hb_le hb_le ha_le
  have w22 := hw b b a a a hb_le hb_le ha_le ha_le ha_le
  have w23 := hw b b a a b hb_le hb_le ha_le ha_le hb_le
  have w24 := hw b b a b a hb_le hb_le ha_le hb_le ha_le
  have w25 := hw b b b a a hb_le hb_le hb_le ha_le ha_le
  -- 25 per-term scaled-word bounds.
  have c01 : ‖((15 : 𝕂) / 11520) • (a * a * a * a * b)‖ ≤ 15 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 15 _ s w01 hs_nn
    simpa [show |((15 : ℤ) : ℝ)| = 15 from by push_cast; norm_num,
           show ((15 : ℤ) : 𝕂) / 11520 = (15 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c02 : ‖((-60 : 𝕂) / 11520) • (a * a * a * b * a)‖ ≤ 60 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-60) _ s w02 hs_nn
    simpa [show |((-60 : ℤ) : ℝ)| = 60 from by push_cast; norm_num,
           show ((-60 : ℤ) : 𝕂) / 11520 = (-60 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c03 : ‖((-50 : 𝕂) / 11520) • (a * a * a * b * b)‖ ≤ 50 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-50) _ s w03 hs_nn
    simpa [show |((-50 : ℤ) : ℝ)| = 50 from by push_cast; norm_num,
           show ((-50 : ℤ) : 𝕂) / 11520 = (-50 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c04 : ‖((90 : 𝕂) / 11520) • (a * a * b * a * a)‖ ≤ 90 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 90 _ s w04 hs_nn
    simpa [show |((90 : ℤ) : ℝ)| = 90 from by push_cast; norm_num,
           show ((90 : ℤ) : 𝕂) / 11520 = (90 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c05 : ‖((110 : 𝕂) / 11520) • (a * a * b * a * b)‖ ≤ 110 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 110 _ s w05 hs_nn
    simpa [show |((110 : ℤ) : ℝ)| = 110 from by push_cast; norm_num,
           show ((110 : ℤ) : 𝕂) / 11520 = (110 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c06 : ‖((40 : 𝕂) / 11520) • (a * a * b * b * a)‖ ≤ 40 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 40 _ s w06 hs_nn
    simpa [show |((40 : ℤ) : ℝ)| = 40 from by push_cast; norm_num,
           show ((40 : ℤ) : 𝕂) / 11520 = (40 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c07 : ‖((20 : 𝕂) / 11520) • (a * a * b * b * b)‖ ≤ 20 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 20 _ s w07 hs_nn
    simpa [show |((20 : ℤ) : ℝ)| = 20 from by push_cast; norm_num,
           show ((20 : ℤ) : 𝕂) / 11520 = (20 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c08 : ‖((-60 : 𝕂) / 11520) • (a * b * a * a * a)‖ ≤ 60 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-60) _ s w08 hs_nn
    simpa [show |((-60 : ℤ) : ℝ)| = 60 from by push_cast; norm_num,
           show ((-60 : ℤ) : 𝕂) / 11520 = (-60 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c09 : ‖((-30 : 𝕂) / 11520) • (a * b * a * a * b)‖ ≤ 30 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-30) _ s w09 hs_nn
    simpa [show |((-30 : ℤ) : ℝ)| = 30 from by push_cast; norm_num,
           show ((-30 : ℤ) : 𝕂) / 11520 = (-30 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c10 : ‖((-160 : 𝕂) / 11520) • (a * b * a * b * a)‖ ≤ 160 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-160) _ s w10 hs_nn
    simpa [show |((-160 : ℤ) : ℝ)| = 160 from by push_cast; norm_num,
           show ((-160 : ℤ) : 𝕂) / 11520 = (-160 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c11 : ‖((-20 : 𝕂) / 11520) • (a * b * a * b * b)‖ ≤ 20 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-20) _ s w11 hs_nn
    simpa [show |((-20 : ℤ) : ℝ)| = 20 from by push_cast; norm_num,
           show ((-20 : ℤ) : 𝕂) / 11520 = (-20 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c12 : ‖((40 : 𝕂) / 11520) • (a * b * b * a * a)‖ ≤ 40 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 40 _ s w12 hs_nn
    simpa [show |((40 : ℤ) : ℝ)| = 40 from by push_cast; norm_num,
           show ((40 : ℤ) : 𝕂) / 11520 = (40 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c13 : ‖((-60 : 𝕂) / 11520) • (a * b * b * a * b)‖ ≤ 60 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-60) _ s w13 hs_nn
    simpa [show |((-60 : ℤ) : ℝ)| = 60 from by push_cast; norm_num,
           show ((-60 : ℤ) : 𝕂) / 11520 = (-60 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c14 : ‖((40 : 𝕂) / 11520) • (a * b * b * b * a)‖ ≤ 40 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 40 _ s w14 hs_nn
    simpa [show |((40 : ℤ) : ℝ)| = 40 from by push_cast; norm_num,
           show ((40 : ℤ) : 𝕂) / 11520 = (40 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c15 : ‖((15 : 𝕂) / 11520) • (b * a * a * a * a)‖ ≤ 15 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 15 _ s w15 hs_nn
    simpa [show |((15 : ℤ) : ℝ)| = 15 from by push_cast; norm_num,
           show ((15 : ℤ) : 𝕂) / 11520 = (15 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c16 : ‖((20 : 𝕂) / 11520) • (b * a * a * a * b)‖ ≤ 20 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 20 _ s w16 hs_nn
    simpa [show |((20 : ℤ) : ℝ)| = 20 from by push_cast; norm_num,
           show ((20 : ℤ) : 𝕂) / 11520 = (20 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c17 : ‖((-30 : 𝕂) / 11520) • (b * a * a * b * a)‖ ≤ 30 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-30) _ s w17 hs_nn
    simpa [show |((-30 : ℤ) : ℝ)| = 30 from by push_cast; norm_num,
           show ((-30 : ℤ) : 𝕂) / 11520 = (-30 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c18 : ‖((-40 : 𝕂) / 11520) • (b * a * a * b * b)‖ ≤ 40 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-40) _ s w18 hs_nn
    simpa [show |((-40 : ℤ) : ℝ)| = 40 from by push_cast; norm_num,
           show ((-40 : ℤ) : 𝕂) / 11520 = (-40 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c19 : ‖((110 : 𝕂) / 11520) • (b * a * b * a * a)‖ ≤ 110 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 110 _ s w19 hs_nn
    simpa [show |((110 : ℤ) : ℝ)| = 110 from by push_cast; norm_num,
           show ((110 : ℤ) : 𝕂) / 11520 = (110 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c20 : ‖((160 : 𝕂) / 11520) • (b * a * b * a * b)‖ ≤ 160 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 160 _ s w20 hs_nn
    simpa [show |((160 : ℤ) : ℝ)| = 160 from by push_cast; norm_num,
           show ((160 : ℤ) : 𝕂) / 11520 = (160 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c21 : ‖((-60 : 𝕂) / 11520) • (b * a * b * b * a)‖ ≤ 60 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-60) _ s w21 hs_nn
    simpa [show |((-60 : ℤ) : ℝ)| = 60 from by push_cast; norm_num,
           show ((-60 : ℤ) : 𝕂) / 11520 = (-60 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c22 : ‖((-50 : 𝕂) / 11520) • (b * b * a * a * a)‖ ≤ 50 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-50) _ s w22 hs_nn
    simpa [show |((-50 : ℤ) : ℝ)| = 50 from by push_cast; norm_num,
           show ((-50 : ℤ) : 𝕂) / 11520 = (-50 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c23 : ‖((-40 : 𝕂) / 11520) • (b * b * a * a * b)‖ ≤ 40 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-40) _ s w23 hs_nn
    simpa [show |((-40 : ℤ) : ℝ)| = 40 from by push_cast; norm_num,
           show ((-40 : ℤ) : 𝕂) / 11520 = (-40 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c24 : ‖((-20 : 𝕂) / 11520) • (b * b * a * b * a)‖ ≤ 20 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 (-20) _ s w24 hs_nn
    simpa [show |((-20 : ℤ) : ℝ)| = 20 from by push_cast; norm_num,
           show ((-20 : ℤ) : 𝕂) / 11520 = (-20 : 𝕂) / 11520 from by push_cast; ring]
      using this
  have c25 : ‖((20 : 𝕂) / 11520) • (b * b * b * a * a)‖ ≤ 20 / 11520 * s ^ 5 := by
    have := norm_correction_word_le_helper 𝕂 20 _ s w25 hs_nn
    simpa [show |((20 : ℤ) : ℝ)| = 20 from by push_cast; norm_num,
           show ((20 : ℤ) : 𝕂) / 11520 = (20 : 𝕂) / 11520 from by push_cast; ring]
      using this
  -- Triangle inequality on 25-term sum via abel rewrite + norm_add_le chain.
  -- Refactor as explicit nested binary sum with set tactics, then linarith on ‖.‖ bounds.
  unfold symmetric_bch_quintic_correction_poly
  -- Set up named variables for each of the 25 terms.
  set t1 := ((15 : 𝕂) / 11520) • (a * a * a * a * b)
  set t2 := ((-60 : 𝕂) / 11520) • (a * a * a * b * a)
  set t3 := ((-50 : 𝕂) / 11520) • (a * a * a * b * b)
  set t4 := ((90 : 𝕂) / 11520) • (a * a * b * a * a)
  set t5 := ((110 : 𝕂) / 11520) • (a * a * b * a * b)
  set t6 := ((40 : 𝕂) / 11520) • (a * a * b * b * a)
  set t7 := ((20 : 𝕂) / 11520) • (a * a * b * b * b)
  set t8 := ((-60 : 𝕂) / 11520) • (a * b * a * a * a)
  set t9 := ((-30 : 𝕂) / 11520) • (a * b * a * a * b)
  set t10 := ((-160 : 𝕂) / 11520) • (a * b * a * b * a)
  set t11 := ((-20 : 𝕂) / 11520) • (a * b * a * b * b)
  set t12 := ((40 : 𝕂) / 11520) • (a * b * b * a * a)
  set t13 := ((-60 : 𝕂) / 11520) • (a * b * b * a * b)
  set t14 := ((40 : 𝕂) / 11520) • (a * b * b * b * a)
  set t15 := ((15 : 𝕂) / 11520) • (b * a * a * a * a)
  set t16 := ((20 : 𝕂) / 11520) • (b * a * a * a * b)
  set t17 := ((-30 : 𝕂) / 11520) • (b * a * a * b * a)
  set t18 := ((-40 : 𝕂) / 11520) • (b * a * a * b * b)
  set t19 := ((110 : 𝕂) / 11520) • (b * a * b * a * a)
  set t20 := ((160 : 𝕂) / 11520) • (b * a * b * a * b)
  set t21 := ((-60 : 𝕂) / 11520) • (b * a * b * b * a)
  set t22 := ((-50 : 𝕂) / 11520) • (b * b * a * a * a)
  set t23 := ((-40 : 𝕂) / 11520) • (b * b * a * a * b)
  set t24 := ((-20 : 𝕂) / 11520) • (b * b * a * b * a)
  set t25 := ((20 : 𝕂) / 11520) • (b * b * b * a * a)
  -- 24 triangle inequalities for the partial sums.
  have h12 := norm_add_le t1 t2
  have h123 := norm_add_le (t1 + t2) t3
  have h1234 := norm_add_le (t1 + t2 + t3) t4
  have h12345 := norm_add_le (t1 + t2 + t3 + t4) t5
  have h123456 := norm_add_le (t1 + t2 + t3 + t4 + t5) t6
  have h1234567 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7
  have h12345678 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have h123456789 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9
  have h12_10 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10
  have h12_11 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11
  have h12_12 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11) t12
  have h12_13 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12) t13
  have h12_14 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13) t14
  have h12_15 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14) t15
  have h12_16 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15) t16
  have h12_17 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16) t17
  have h12_18 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17) t18
  have h12_19 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17 +
      t18) t19
  have h12_20 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17 +
      t18 + t19) t20
  have h12_21 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17 +
      t18 + t19 + t20) t21
  have h12_22 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17 +
      t18 + t19 + t20 + t21) t22
  have h12_23 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17 +
      t18 + t19 + t20 + t21 + t22) t23
  have h12_24 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17 +
      t18 + t19 + t20 + t21 + t22 + t23) t24
  have h12_25 := norm_add_le
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 + t17 +
      t18 + t19 + t20 + t21 + t22 + t23 + t24) t25
  -- linarith with all 25 c-bounds + 24 triangle inequalities.
  linarith

/-- **Alt-form decomposition of `symmetric_bch_quintic_poly`** (T2-B, Tier-2
stepping stone — now fully proved):

    sym_E₅(a, b) = bch_quintic_term(½a, b)
                 + bch_quintic_term(½a + b, ½a)
                 + symmetric_bch_quintic_correction_poly(a, b)

CAS-derived and CAS-verified (`Lean-Trotter/scripts/discover_quintic_alt_form.py`
confirms the decomposition is exact: residual = 0 across all 30 5-letter words).

This is a pure polynomial identity in `{a, b}`. Discharged session 18 via:
1. `unfold` all definitions on both sides.
2. `simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul]` to fully distribute scalars and
    products through the polynomial expressions.
3. `match_scalars` reduces to a sequence of scalar identities (one per
    {a,b}-word in the basis).
4. `ring` (commutative `𝕂`-arithmetic) closes each scalar goal.

Earlier sessions attempted `×LCM + comprehensive pattern enumeration +
noncomm_ring`, which required ~150-200 lines and failed due to simp's
associativity normalization not matching all enumerated patterns.
`match_scalars <;> ring` sidesteps that issue by working at the module level. -/
private theorem symmetric_bch_quintic_poly_alt_form
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    symmetric_bch_quintic_poly 𝕂 a b =
      bch_quintic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
      bch_quintic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) +
      symmetric_bch_quintic_correction_poly 𝕂 a b := by
  unfold symmetric_bch_quintic_poly bch_quintic_term symmetric_bch_quintic_correction_poly
    bch_quintic_group_1 bch_quintic_group_4 bch_quintic_group_6 bch_quintic_group_24
  simp only [smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul]
  match_scalars <;> ring

/-- **Sub-lemma D (T2-F7e Phase B)**: ½·[C₄(a',b), a'] equals an explicit
7-monomial polynomial in {a, b}, where a' = ½a.

CAS-derived: denominator 2304. -/
private theorem half_C4_bracket_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b) =
      (-6 / 2304 : 𝕂) • (a * a * a * b * b) +
      (12 / 2304 : 𝕂) • (a * a * b * a * b) +
      (6 / 2304 : 𝕂) • (a * a * b * b * a) +
      (-24 / 2304 : 𝕂) • (a * b * a * b * a) +
      (6 / 2304 : 𝕂) • (a * b * b * a * a) +
      (12 / 2304 : 𝕂) • (b * a * b * a * a) +
      (-6 / 2304 : 𝕂) • (b * b * a * a * a) := by
  intro a'
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl]
  unfold bch_quartic_term
  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,
             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  match_scalars <;> ring

-- **Sub-lemma A (T2-F7e Phase B)**: ΔC₃_lin(V₃, x, a') equals an explicit
-- 20-monomial polynomial in {a, b}, where V₃ = C₃(a',b), x = a'+b, a' = ½a.
-- CAS-derived: denominator 2304.
set_option maxHeartbeats 16000000 in
private theorem deltaC3_lin_V3_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    (12 : 𝕂)⁻¹ • (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) +
    (12 : 𝕂)⁻¹ • (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) +
    (12 : 𝕂)⁻¹ • (a' * (a' * V₃ - V₃ * a') - (a' * V₃ - V₃ * a') * a') =
      (2 / 2304 : 𝕂) • (a * a * a * b * b) +
      (-8 / 2304 : 𝕂) • (a * a * b * a * b) +
      (2 / 2304 : 𝕂) • (a * a * b * b * a) +
      (4 / 2304 : 𝕂) • (a * a * b * b * b) +
      (12 / 2304 : 𝕂) • (a * b * a * a * b) +
      (-8 / 2304 : 𝕂) • (a * b * a * b * a) +
      (-4 / 2304 : 𝕂) • (a * b * a * b * b) +
      (2 / 2304 : 𝕂) • (a * b * b * a * a) +
      (-12 / 2304 : 𝕂) • (a * b * b * a * b) +
      (8 / 2304 : 𝕂) • (a * b * b * b * a) +
      (-8 / 2304 : 𝕂) • (b * a * a * a * b) +
      (12 / 2304 : 𝕂) • (b * a * a * b * a) +
      (-8 / 2304 : 𝕂) • (b * a * a * b * b) +
      (-8 / 2304 : 𝕂) • (b * a * b * a * a) +
      (32 / 2304 : 𝕂) • (b * a * b * a * b) +
      (-12 / 2304 : 𝕂) • (b * a * b * b * a) +
      (2 / 2304 : 𝕂) • (b * b * a * a * a) +
      (-8 / 2304 : 𝕂) • (b * b * a * a * b) +
      (-4 / 2304 : 𝕂) • (b * b * a * b * a) +
      (4 / 2304 : 𝕂) • (b * b * b * a * a) := by
  intro a' V₃ x
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl,
             show V₃ = bch_cubic_term 𝕂 a' b from rfl,
             show x = ((2 : 𝕂)⁻¹ • a + b : 𝔸) from rfl]
  unfold bch_cubic_term
  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,
             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  match_scalars <;> ring

/-- **Sub-lemma C (T2-F7e Phase B)**: ΔC₄_lin(V₂, x, a') equals an explicit
12-monomial polynomial in {a, b}, where V₂ = ½·[a',b], x = a'+b, a' = ½a.

CAS-derived: denominator 2304. -/
private theorem deltaC4_lin_V2_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let x : 𝔸 := a' + b
    (0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) -
                     (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) * a') -
    (24 : 𝕂)⁻¹ • (a' * (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) -
                     (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) * a') =
      (3 / 2304 : 𝕂) • (a * a * a * a * b) +
      (-12 / 2304 : 𝕂) • (a * a * a * b * a) +
      (-6 / 2304 : 𝕂) • (a * a * a * b * b) +
      (18 / 2304 : 𝕂) • (a * a * b * a * a) +
      (12 / 2304 : 𝕂) • (a * a * b * a * b) +
      (6 / 2304 : 𝕂) • (a * a * b * b * a) +
      (-12 / 2304 : 𝕂) • (a * b * a * a * a) +
      (-24 / 2304 : 𝕂) • (a * b * a * b * a) +
      (6 / 2304 : 𝕂) • (a * b * b * a * a) +
      (3 / 2304 : 𝕂) • (b * a * a * a * a) +
      (12 / 2304 : 𝕂) • (b * a * b * a * a) +
      (-6 / 2304 : 𝕂) • (b * b * a * a * a) := by
  intro a' V₂ x
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl,
             show V₂ = ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) from rfl,
             show x = ((2 : 𝕂)⁻¹ • a + b : 𝔸) from rfl]
  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,
             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  match_scalars <;> ring

/-- **Sub-lemma B (T2-F7e Phase B)**: ΔC₃_quad(V₂, x, a') equals an explicit
8-monomial polynomial in {a, b}, where V₂ = ½·[a',b], a' = ½a.

CAS-derived (`verify_t2f7e_deg5_cancellation.py`): denominator 2304. -/
private theorem deltaC3_quad_V2_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    (12 : 𝕂)⁻¹ • (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) =
      (6 / 2304 : 𝕂) • (a * a * b * a * b) +
      (-6 / 2304 : 𝕂) • (a * a * b * b * a) +
      (-18 / 2304 : 𝕂) • (a * b * a * a * b) +
      (24 / 2304 : 𝕂) • (a * b * a * b * a) +
      (-6 / 2304 : 𝕂) • (a * b * b * a * a) +
      (12 / 2304 : 𝕂) • (b * a * a * a * b) +
      (-18 / 2304 : 𝕂) • (b * a * a * b * a) +
      (6 / 2304 : 𝕂) • (b * a * b * a * a) := by
  intro a' V₂
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl,
             show V₂ = ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) from rfl]
  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-- **Deg-5 cancellation pure identity** (T2-F7e Phase B, stepping-stone axiom).

For the parent discharge of the τ⁵ symmetric-BCH bridge, the deg-5 piece group
in the extended hdecomp `T₅ + T₆ + ½·[C₄(a',b), a'] − correction` has its
deg-5 part cancel as an algebraic identity in `𝕂⟨a, b⟩`.

Specifically, with `a' := ½a`, `V₂ := ½·[a',b]`, `V₃ := C₃(a',b)`, `x := a'+b`:

  ΔC₃_lin(V₃, x, a') + ΔC₃_quad(V₂, x, a')           -- = (deg-5 of T₅)
+ ΔC₄_lin(V₂, x, a')                                  -- = (deg-5 of T₆)
+ ½·(C₄(a', b)·a' − a'·C₄(a', b))                    -- = ½·[C₄(a',b), a']
= symmetric_bch_quintic_correction_poly 𝕂 a b        -- = correction(a, b)

Where the perturbation operators expand as:
- `ΔC₃_lin(V, x, y)`  = (1/12)·([V,[x,y]] + [x,[V,y]] + [y,[y,V]])
- `ΔC₃_quad(V, x, y)` = (1/12)·[V,[V,y]]
- `ΔC₄_lin(V, x, y)`  = -(1/24)·([y,[x,[V,y]]] + [y,[V,[x,y]]])

**CAS-verified** at `Lean-Trotter/scripts/verify_t2f7e_deg5_cancellation.py`:
both sides reduce to the same 25-monomial polynomial in {a, b}-words with
rational coefficients (denominator 11520).

**Status (session 21, 2026-05-09)**: discharged via 4 CAS-derived sub-lemmas
(`deltaC3_lin_V3_eq`, `deltaC3_quad_V2_eq`, `deltaC4_lin_V2_eq`, `half_C4_bracket_eq`)
each of which proves a piece equals an explicit polynomial in {a,b}
(with common denominator 2304). The combined identity follows by polynomial
arithmetic.

Connection to T2-B alt-form: from
  sym_E₅ = bqt(a',b) + bqt(a'+b, a') + correction
combined with the deg-5 expansion of `bch(z, a')` (z = bch(a', b)),
one derives `correction = ½·[C₄(a',b), a'] + (deg-5 of T₅) + (deg-5 of T₆)`,
where the deg-5 of T₅, T₆ are computed via Taylor expansion of C₃, C₄
around the static point `(a'+b, a')` in the perturbation `W = z - (a'+b)`. -/
private theorem symmetric_bch_quintic_deg5_cancellation_pure_identity
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    -- ΔC₃_lin(V₃, x, a') = (1/12)·([V₃,[x,a']] + [x,[V₃,a']] + [a',[a',V₃]])
    ((12 : 𝕂)⁻¹ • (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) +
     (12 : 𝕂)⁻¹ • (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) +
     (12 : 𝕂)⁻¹ • (a' * (a' * V₃ - V₃ * a') - (a' * V₃ - V₃ * a') * a')) +
    -- ΔC₃_quad(V₂, x, a') = (1/12)·[V₂,[V₂,a']]
    ((12 : 𝕂)⁻¹ • (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂)) +
    -- ΔC₄_lin(V₂, x, a') = -(1/24)·([a',[x,[V₂,a']]] + [a',[V₂,[x,a']]])
    ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) -
                              (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) -
                              (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) * a')) +
    -- ½·[C₄(a', b), a']
    ((2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b)) =
    symmetric_bch_quintic_correction_poly 𝕂 a b := by
  intro a' V₂ V₃ x
  rw [deltaC3_lin_V3_eq (𝕂 := 𝕂) a b,
      deltaC3_quad_V2_eq (𝕂 := 𝕂) a b,
      deltaC4_lin_V2_eq (𝕂 := 𝕂) a b,
      half_C4_bracket_eq (𝕂 := 𝕂) a b]
  unfold symmetric_bch_quintic_correction_poly
  match_scalars <;> ring

/-! ### T2-F7e Phase C: deg-6 cancellation pure identity

The deg-6 contributions to `sym_bch_cubic - sym_E₃ - sym_E₅` (zero by
palindromic vanishing of even degrees in the 3-factor product) split into
6 pieces that sum to zero algebraically.

Pieces (with `a' := ½a`, `V₂ := ½·[a',b]`, `V₃ := C₃(a',b)`, `V₄ := C₄(a',b)`,
`x := a'+b`):
1. (deg-6 of T₅) = ΔC₃_lin(V₄, x, a') + (1/12)·([V₂,[V₃,a']] + [V₃,[V₂,a']]).
2. (deg-6 of T₆) = ΔC₄_lin(V₃, x, a') + ΔC₄_quad(V₂, x, a').
3. ½·[C₅(a',b), a'] (purely deg-6).
4. C₆(a',b) = bch_sextic_term(a',b) (purely deg-6).
5. C₆(a'+b, a') = bch_sextic_term(a'+b, a') (purely deg-6).
6. (deg-6 of (C₅(z,a') − C₅(a'+b,a'))) = ΔC₅_lin(V₂, x, a') (no clean
   commutator form; explicit 36-monomial polynomial).

CAS-verified at `Lean-Trotter/scripts/verify_t2f7e_deg6_cancellation.py`:
all 6 pieces have common denominator 46080; sum across all monomials = 0.
-/

-- **Sub-lemma (T2-F7e Phase C, piece 3)**: ½·[C₅(½a, b), ½a] equals an
-- explicit 38-monomial polynomial in {a, b}. CAS-derived: denominator 46080.
set_option maxHeartbeats 16000000 in
private theorem half_C5_bracket_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    (2 : 𝕂)⁻¹ • (bch_quintic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b * ((2 : 𝕂)⁻¹ • a) -
                  ((2 : 𝕂)⁻¹ • a) * bch_quintic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b) =
      (1 / 46080 : 𝕂) • (a * a * a * a * a * b) +
      (-5 / 46080 : 𝕂) • (a * a * a * a * b * a) +
      (-8 / 46080 : 𝕂) • (a * a * a * a * b * b) +
      (10 / 46080 : 𝕂) • (a * a * a * b * a * a) +
      (12 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (20 / 46080 : 𝕂) • (a * a * a * b * b * a) +
      (-16 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (-10 / 46080 : 𝕂) • (a * a * b * a * a * a) +
      (12 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (-60 / 46080 : 𝕂) • (a * a * b * a * b * a) +
      (24 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (24 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
      (5 / 46080 : 𝕂) • (a * b * a * a * a * a) +
      (-8 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (24 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (60 / 46080 : 𝕂) • (a * b * a * b * a * a) +
      (-96 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (-32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
      (-20 / 46080 : 𝕂) • (a * b * b * a * a * a) +
      (24 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
      (-32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
      (-1 / 46080 : 𝕂) • (b * a * a * a * a * a) +
      (8 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (-12 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (-24 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (-12 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (96 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (-24 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
      (8 / 46080 : 𝕂) • (b * b * a * a * a * a) +
      (-24 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (-24 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (-48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
      (16 / 46080 : 𝕂) • (b * b * b * a * a * a) +
      (32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
      (-8 / 46080 : 𝕂) • (b * b * b * b * a * a) := by
  unfold bch_quintic_term bch_quintic_group_1 bch_quintic_group_4
    bch_quintic_group_6 bch_quintic_group_24
  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,
             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  match_scalars <;> ring

-- **Sub-lemma (T2-F7e Phase C, piece 5)**: bch_sextic_term(½a + b, ½a) equals
-- an explicit 42-monomial polynomial in {a, b}. CAS-derived: denominator 46080.
set_option maxHeartbeats 16000000 in
private theorem C6_static_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    bch_sextic_term 𝕂 (a' + b) a' =
      (-6 / 46080 : 𝕂) • (a * a * a * a * a * b) +
      (30 / 46080 : 𝕂) • (a * a * a * a * b * a) +
      (24 / 46080 : 𝕂) • (a * a * a * a * b * b) +
      (-60 / 46080 : 𝕂) • (a * a * a * b * a * a) +
      (-66 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (-30 / 46080 : 𝕂) • (a * a * a * b * b * a) +
      (-28 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (60 / 46080 : 𝕂) • (a * a * b * a * a * a) +
      (54 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (90 / 46080 : 𝕂) • (a * a * b * a * b * a) +
      (52 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (12 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
      (8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
      (-30 / 46080 : 𝕂) • (a * b * a * a * a * a) +
      (-36 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (32 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (-90 / 46080 : 𝕂) • (a * b * a * b * a * a) +
      (-128 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (-40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
      (-32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
      (30 / 46080 : 𝕂) • (a * b * b * a * a * a) +
      (32 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
      (48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
      (-20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
      (-32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
      (6 / 46080 : 𝕂) • (b * a * a * a * a * a) +
      (36 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (-54 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (-32 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (66 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (128 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (-12 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
      (-24 / 46080 : 𝕂) • (b * b * a * a * a * a) +
      (-32 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (-52 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (-48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
      (28 / 46080 : 𝕂) • (b * b * b * a * a * a) +
      (32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
      (-8 / 46080 : 𝕂) • (b * b * b * b * a * a) := by
  intro a'
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl]
  unfold bch_sextic_term
  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

-- **Sub-lemma (T2-F7e Phase C, piece 4)**: bch_sextic_term(½a, b) equals an
-- explicit 28-monomial polynomial in {a, b}. CAS-derived: denominator 46080.
private theorem C6_inner_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    bch_sextic_term 𝕂 a' b =
      (-2 / 46080 : 𝕂) • (a * a * a * a * b * b) +
      (8 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (16 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (-12 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (-24 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (-24 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (-8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
      (8 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (-24 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (96 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
      (-24 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (-48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
      (32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
      (-8 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (12 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (24 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (-8 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (-96 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (24 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (-32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
      (2 / 46080 : 𝕂) • (b * b * a * a * a * a) +
      (24 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (24 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
      (-16 / 46080 : 𝕂) • (b * b * b * a * a * a) +
      (-32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
      (8 / 46080 : 𝕂) • (b * b * b * b * a * a) := by
  intro a'
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl]
  unfold bch_sextic_term
  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

-- **Sub-lemma (T2-F7e Phase C, piece 2)**: (deg-6 of T₆) operator form equals
-- an explicit 32-monomial polynomial. T₆ = C₄(z, a') − C₄(a'+b, a'); the deg-6
-- contribution is ΔC₄_lin(V₃, x, a') + ΔC₄_quad(V₂, x, a').
-- CAS-derived: denominator 46080.
set_option maxHeartbeats 16000000 in
private theorem T6_d6_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    (0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) -
                             (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) * a') -
              (24 : 𝕂)⁻¹ • (a' * (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) -
                             (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) * a') -
              (24 : 𝕂)⁻¹ • (a' * (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) -
                             (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) * a') =
      (5 / 46080 : 𝕂) • (a * a * a * a * a * b) +
      (-25 / 46080 : 𝕂) • (a * a * a * a * b * a) +
      (50 / 46080 : 𝕂) • (a * a * a * b * a * a) +
      (-10 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (10 / 46080 : 𝕂) • (a * a * a * b * b * a) +
      (-20 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (-50 / 46080 : 𝕂) • (a * a * b * a * a * a) +
      (30 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (-30 / 46080 : 𝕂) • (a * a * b * a * b * a) +
      (20 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (60 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (-20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
      (25 / 46080 : 𝕂) • (a * b * a * a * a * a) +
      (-20 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (40 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (30 / 46080 : 𝕂) • (a * b * a * b * a * a) +
      (-160 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
      (-10 / 46080 : 𝕂) • (a * b * b * a * a * a) +
      (40 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (-40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
      (20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
      (-5 / 46080 : 𝕂) • (b * a * a * a * a * a) +
      (20 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (-30 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (-40 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (10 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (160 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (-60 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (-40 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (-20 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (20 / 46080 : 𝕂) • (b * b * b * a * a * a) := by
  intro a' V₂ V₃ x
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl,
             show V₂ = ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) from rfl,
             show V₃ = (bch_cubic_term 𝕂 a' b : 𝔸) from rfl,
             show x = ((2 : 𝕂)⁻¹ • a + b : 𝔸) from rfl]
  unfold bch_cubic_term
  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,
             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  match_scalars <;> ring

-- **Sub-lemma (T2-F7e Phase C, piece 1)**: (deg-6 of T₅) operator form equals
-- an explicit 26-monomial polynomial. T₅ = C₃(z, a') − C₃(a'+b, a') +
-- (1/96)·[b, [a, [a, b]]]; the deg-6 contribution is
-- ΔC₃_lin(V₄, x, a') + (1/12)·([V₂, [V₃, a']] + [V₃, [V₂, a']]).
-- CAS-derived: denominator 46080.
set_option maxHeartbeats 32000000 in
private theorem T5_d6_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let V₄ : 𝔸 := bch_quartic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    (12 : 𝕂)⁻¹ • (V₄ * (x * a' - a' * x) - (x * a' - a' * x) * V₄ +
                   x * (V₄ * a' - a' * V₄) - (V₄ * a' - a' * V₄) * x +
                   a' * (a' * V₄ - V₄ * a') - (a' * V₄ - V₄ * a') * a') +
    (12 : 𝕂)⁻¹ • (V₂ * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * V₂ +
                   V₃ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₃) =
      (10 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (-10 / 46080 : 𝕂) • (a * a * a * b * b * a) +
      (20 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (-30 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (30 / 46080 : 𝕂) • (a * a * b * a * b * a) +
      (-20 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (-60 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
      (20 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (-40 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (-30 / 46080 : 𝕂) • (a * b * a * b * a * a) +
      (160 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (-40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
      (10 / 46080 : 𝕂) • (a * b * b * a * a * a) +
      (-40 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
      (-20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
      (-20 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (30 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (40 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (-10 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (-160 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (60 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (40 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (20 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (-20 / 46080 : 𝕂) • (b * b * b * a * a * a) := by
  intro a' V₂ V₃ V₄ x
  show _ = _
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl,
             show V₂ = ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) from rfl,
             show V₃ = (bch_cubic_term 𝕂 a' b : 𝔸) from rfl,
             show V₄ = (bch_quartic_term 𝕂 a' b : 𝔸) from rfl,
             show x = ((2 : 𝕂)⁻¹ • a + b : 𝔸) from rfl]
  unfold bch_cubic_term bch_quartic_term
  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,
             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  match_scalars <;> ring

-- **Deg-6 cancellation pure identity** (T2-F7e Phase C, palindromic vanishing).
--
-- For the parent discharge of the τ⁵ symmetric-BCH bridge, the deg-6 piece group
-- in the extended hdecomp `(T₅ + T₆) + ½·[C₅(a',b), a'] + C₆(a',b) + C₆(a'+b, a')
-- + ΔC₅_lin(V₂, x, a')` has its deg-6 part cancel as an algebraic identity
-- in `𝕂⟨a, b⟩` — the RHS is **zero**, reflecting the palindromic vanishing of
-- the deg-6 part of `log(exp(½a)·exp(b)·exp(½a))`.
--
-- Six pieces (with `a' := ½a`, `V₂ := ½·[a',b]`, `V₃ := C₃(a',b)`,
-- `V₄ := C₄(a',b) = bch_quartic_term(a',b)`, `x := a'+b`):
--   1. (deg-6 of T₅) = ΔC₃_lin(V₄, x, a') + (1/12)·([V₂,[V₃,a']] + [V₃,[V₂,a']])
--   2. (deg-6 of T₆) = ΔC₄_lin(V₃, x, a') + ΔC₄_quad(V₂, x, a')
--   3. ½·[C₅(a',b), a'] (purely deg-6)
--   4. C₆(a',b) = bch_sextic_term(a',b) (purely deg-6)
--   5. C₆(a'+b, a') = bch_sextic_term(a'+b, a') (purely deg-6)
--   6. ΔC₅_lin(V₂, x, a') (deg-6 of `C₅(z, a') − C₅(a'+b, a')`; no clean
--      commutator form — explicit 36-monomial polynomial)
--
-- CAS-verified at `Lean-Trotter/scripts/verify_t2f7e_deg6_cancellation.py`:
-- the six pieces have common denominator 46080 and sum to zero across all
-- monomials.
set_option maxHeartbeats 16000000 in
private theorem symmetric_bch_quintic_deg6_cancellation_pure_identity
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let V₄ : 𝔸 := bch_quartic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    -- (deg-6 of T₅): ΔC₃_lin(V₄, x, a') + (1/12)·([V₂,[V₃,a']] + [V₃,[V₂,a']])
    ((12 : 𝕂)⁻¹ • (V₄ * (x * a' - a' * x) - (x * a' - a' * x) * V₄ +
                    x * (V₄ * a' - a' * V₄) - (V₄ * a' - a' * V₄) * x +
                    a' * (a' * V₄ - V₄ * a') - (a' * V₄ - V₄ * a') * a') +
     (12 : 𝕂)⁻¹ • (V₂ * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * V₂ +
                    V₃ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₃)) +
    -- (deg-6 of T₆): ΔC₄_lin(V₃, x, a') + ΔC₄_quad(V₂, x, a')
    ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) -
                              (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) * a') -
               (24 : 𝕂)⁻¹ • (a' * (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) -
                              (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) * a') -
               (24 : 𝕂)⁻¹ • (a' * (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) -
                              (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) * a')) +
    -- ½·[C₅(a',b), a']
    ((2 : 𝕂)⁻¹ • (bch_quintic_term 𝕂 a' b * a' - a' * bch_quintic_term 𝕂 a' b)) +
    -- C₆(a', b)
    bch_sextic_term 𝕂 a' b +
    -- C₆(a'+b, a')
    bch_sextic_term 𝕂 (a' + b) a' +
    -- ΔC₅_lin(V₂, x, a') as explicit 36-monomial polynomial (denom 46080)
    ((-14 / 46080 : 𝕂) • (a * a * a * a * b * b) +
     (46 / 46080 : 𝕂) • (a * a * a * b * a * b) +
     (10 / 46080 : 𝕂) • (a * a * a * b * b * a) +
     (28 / 46080 : 𝕂) • (a * a * a * b * b * b) +
     (-54 / 46080 : 𝕂) • (a * a * b * a * a * b) +
     (-30 / 46080 : 𝕂) • (a * a * b * a * b * a) +
     (-52 / 46080 : 𝕂) • (a * a * b * a * b * b) +
     (-12 / 46080 : 𝕂) • (a * a * b * b * a * b) +
     (-20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
     (-8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
     (36 / 46080 : 𝕂) • (a * b * a * a * a * b) +
     (-32 / 46080 : 𝕂) • (a * b * a * a * b * b) +
     (30 / 46080 : 𝕂) • (a * b * a * b * a * a) +
     (128 / 46080 : 𝕂) • (a * b * a * b * a * b) +
     (40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
     (32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
     (-10 / 46080 : 𝕂) • (a * b * b * a * a * a) +
     (-32 / 46080 : 𝕂) • (a * b * b * a * a * b) +
     (-40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
     (-48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
     (20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
     (32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
     (-36 / 46080 : 𝕂) • (b * a * a * a * b * a) +
     (54 / 46080 : 𝕂) • (b * a * a * b * a * a) +
     (32 / 46080 : 𝕂) • (b * a * a * b * b * a) +
     (-46 / 46080 : 𝕂) • (b * a * b * a * a * a) +
     (-128 / 46080 : 𝕂) • (b * a * b * a * b * a) +
     (12 / 46080 : 𝕂) • (b * a * b * b * a * a) +
     (-32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
     (14 / 46080 : 𝕂) • (b * b * a * a * a * a) +
     (32 / 46080 : 𝕂) • (b * b * a * a * b * a) +
     (52 / 46080 : 𝕂) • (b * b * a * b * a * a) +
     (48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
     (-28 / 46080 : 𝕂) • (b * b * b * a * a * a) +
     (-32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
     (8 / 46080 : 𝕂) • (b * b * b * b * a * a)) = (0 : 𝔸) := by
  intro a' V₂ V₃ V₄ x
  rw [T5_d6_eq (𝕂 := 𝕂) a b,
      T6_d6_eq (𝕂 := 𝕂) a b,
      half_C5_bracket_eq (𝕂 := 𝕂) a b,
      C6_inner_eq (𝕂 := 𝕂) a b,
      C6_static_eq (𝕂 := 𝕂) a b]
  match_scalars <;> ring

/-! ### T2-F7e Phase D: Extended hdecomp identity

The algebraic decomposition of `sym_bch_cubic - sym_E₃ - sym_E₅` into 13
sub-pieces (or 4 grouped pieces). Mirrors the cubic template hdecomp from
`norm_symmetric_bch_cubic_sub_poly_le` (`Basic.lean`) but extended with two
more degrees of BCH expansion (C₅, C₆) and the sym_E₅ subtraction.

The 13 sub-pieces are organized into 4 groups:

**Group A (sept-related, 3 sub-pieces)**:
- `R₁_sept` = bch(a',b) − [(a'+b) + ½[a',b] + C₃ + C₄ + C₅ + C₆](a',b)
- `R₂_sept` = bch(z,a') − [(z+a') + ½[z,a'] + C₃ + C₄ + C₅ + C₆](z,a')
- `½·[R₁_sept, a']`

**Group B (C₆ extras, 2 sub-pieces)**:
- `½·[C₆(a',b), a']`
- `C₆(z,a') − C₆(a'+b, a')`

**Group C (Phase B deg-5 cancellation group, 4 sub-pieces; sums to 0 mod
deg-7+ residual)**:
- `T₅` = C₃(z,a') − C₃(a'+b,a') + (1/96)·[b, [a, [a, b]]]  (cubic template)
- `T₆` = C₄(z,a') − C₄(a'+b, a')
- `½·[C₄(a',b), a']`
- `−correction` = `−symmetric_bch_quintic_correction_poly`

**Group D (Phase C deg-6 cancellation group, 4 sub-pieces; sums to 0 mod
deg-7+ residual)**:
- `½·[C₅(a',b), a']`
- `C₆(a',b)`
- `C₆(a'+b, a')`
- `C₅(z,a') − C₅(a'+b, a')`

The proof extends the cubic template's hdecomp by:
1. Substituting the sym_E₃ alt-form (already used in cubic template).
2. Substituting the sym_E₅ alt-form (`symmetric_bch_quintic_poly_alt_form`).
3. Using septic R-definitions instead of quintic R-definitions.
4. Using the `symmetric_bch_quartic_identity` for deg-4 cancellation
   (already used in cubic template).
-/
set_option maxHeartbeats 8000000 in
private theorem symmetric_bch_quintic_extended_hdecomp
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    let R₁_sept := z - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a') -
                   bch_cubic_term 𝕂 a' b - bch_quartic_term 𝕂 a' b -
                   bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b
    let R₂_sept := bch (𝕂 := 𝕂) z a' - (z + a') - (2 : 𝕂)⁻¹ • (z * a' - a' * z) -
                   bch_cubic_term 𝕂 z a' - bch_quartic_term 𝕂 z a' -
                   bch_quintic_term 𝕂 z a' - bch_sextic_term 𝕂 z a'
    let DC_a : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a
    symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b
        - symmetric_bch_quintic_poly 𝕂 a b =
      -- Group A: sept-related (3 sub-pieces)
      R₁_sept + R₂_sept +
      (2 : 𝕂)⁻¹ • (R₁_sept * a' - a' * R₁_sept) +
      -- Group B: C₆ extras (2 sub-pieces)
      (2 : 𝕂)⁻¹ • (bch_sextic_term 𝕂 a' b * a' - a' * bch_sextic_term 𝕂 a' b) +
      (bch_sextic_term 𝕂 z a' - bch_sextic_term 𝕂 (a' + b) a') +
      -- Group C: Phase B deg-5 cancellation group (4 sub-pieces)
      (bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
        -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
      (bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') +
      (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b) +
      -symmetric_bch_quintic_correction_poly 𝕂 a b +
      -- Group D: Phase C deg-6 cancellation group (4 sub-pieces)
      (2 : 𝕂)⁻¹ • (bch_quintic_term 𝕂 a' b * a' - a' * bch_quintic_term 𝕂 a' b) +
      bch_sextic_term 𝕂 a' b +
      bch_sextic_term 𝕂 (a' + b) a' +
      (bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a') := by
  intro a' z R₁_sept R₂_sept DC_a
  -- Use sym_E₃ alt-form (rewrite sym_E₃ as C₃(a',b) + C₃(a'+b,a') - (1/16)·DC_a).
  rw [symmetric_bch_cubic_poly_alt_form (𝕂 := 𝕂)]
  -- Use sym_E₅ alt-form (rewrite sym_E₅ as C₅(a',b) + C₅(a'+b,a') + correction).
  rw [symmetric_bch_quintic_poly_alt_form (𝕂 := 𝕂)]
  -- Express bch(z, a') via R₂_sept definition.
  have hbch_z_a' : bch (𝕂 := 𝕂) z a' = (z + a') + (2 : 𝕂)⁻¹ • (z * a' - a' * z) +
      bch_cubic_term 𝕂 z a' + bch_quartic_term 𝕂 z a' +
      bch_quintic_term 𝕂 z a' + bch_sextic_term 𝕂 z a' + R₂_sept := by
    show bch (𝕂 := 𝕂) z a' = (z + a') + (2 : 𝕂)⁻¹ • (z * a' - a' * z) +
        bch_cubic_term 𝕂 z a' + bch_quartic_term 𝕂 z a' +
        bch_quintic_term 𝕂 z a' + bch_sextic_term 𝕂 z a' +
        (bch (𝕂 := 𝕂) z a' - (z + a') - (2 : 𝕂)⁻¹ • (z * a' - a' * z) -
         bch_cubic_term 𝕂 z a' - bch_quartic_term 𝕂 z a' -
         bch_quintic_term 𝕂 z a' - bch_sextic_term 𝕂 z a')
    abel
  -- z·a' - a'·z = (a'+b)·a' - a'·(a'+b) + W·a' - a'·W (split via z = (a'+b) + W).
  have hzcom : z * a' - a' * z = (a' + b) * a' - a' * (a' + b) +
      ((z - (a' + b)) * a' - a' * (z - (a' + b))) := by noncomm_ring
  -- W = z - (a'+b) = ½[a',b] + C₃ + C₄ + C₅ + C₆ + R₁_sept (from R₁_sept def).
  have hW_eq : z - (a' + b) =
      (2 : 𝕂)⁻¹ • (a' * b - b * a') + bch_cubic_term 𝕂 a' b +
        bch_quartic_term 𝕂 a' b + bch_quintic_term 𝕂 a' b +
        bch_sextic_term 𝕂 a' b + R₁_sept := by
    show z - (a' + b) =
        (2 : 𝕂)⁻¹ • (a' * b - b * a') + bch_cubic_term 𝕂 a' b +
        bch_quartic_term 𝕂 a' b + bch_quintic_term 𝕂 a' b +
        bch_sextic_term 𝕂 a' b +
        (z - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a') -
         bch_cubic_term 𝕂 a' b - bch_quartic_term 𝕂 a' b -
         bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b)
    abel
  -- z = (a'+b) + W.
  have hz_eq : z = a' + b + (2 : 𝕂)⁻¹ • (a' * b - b * a') + bch_cubic_term 𝕂 a' b +
      bch_quartic_term 𝕂 a' b + bch_quintic_term 𝕂 a' b +
      bch_sextic_term 𝕂 a' b + R₁_sept := by
    rw [show z = (z - (a' + b)) + (a' + b) from by abel, hW_eq]; abel
  -- Quartic identity: ½[C₃(a',b), a'] + C₄(a',b) - (1/96)·[b, DC_a] + C₄(a'+b, a') = 0.
  have hQI := symmetric_bch_quartic_identity (𝕂 := 𝕂) a b
  -- Show the goal (using the bch_inner = z substitution + alt-forms).
  show bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) - (a + b) -
      (bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
       bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) -
       (16 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)) -
      (bch_quintic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
       bch_quintic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) +
       symmetric_bch_quintic_correction_poly 𝕂 a b) = _
  have hbch_inner : bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b = z := rfl
  rw [hbch_inner, hbch_z_a', hzcom, hW_eq]
  -- Use quartic identity to express C₄(a'+b, a') via other terms.
  have hQI_rearr : bch_quartic_term 𝕂 (a' + b) a' =
      -((2 : 𝕂)⁻¹ • (bch_cubic_term 𝕂 a' b * a' - a' * bch_cubic_term 𝕂 a' b)) -
      bch_quartic_term 𝕂 a' b +
      (96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b) := by
    have h := hQI
    have h' : ((2 : 𝕂)⁻¹ • (bch_cubic_term 𝕂 a' b * a' - a' * bch_cubic_term 𝕂 a' b) +
                bch_quartic_term 𝕂 a' b +
                -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
               bch_quartic_term 𝕂 (a' + b) a' = 0 := by
      show _ = _
      convert h using 2
    have hW := eq_neg_of_add_eq_zero_right h'
    rw [hW]; abel
  rw [hQI_rearr]
  nth_rewrite 1 [hz_eq]
  -- Unfold a' to (2:𝕂)⁻¹•a to align all atoms.
  simp only [show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl]
  -- Distribute smul through products and use match_scalars + ring to close.
  simp only [smul_sub, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    add_mul, mul_add, sub_mul, mul_sub]
  match_scalars <;> ring

end SymmetricQuinticAltForm

/-!
## Quintic Taylor bridge for the 3-factor symmetric BCH (B1.c)

`norm_symmetric_bch_quintic_sub_poly_le` asserts that after subtracting both
the cubic polynomial `symmetric_bch_cubic_poly` and the quintic polynomial
`symmetric_bch_quintic_poly`, the residual of `symmetric_bch_cubic` decays
as `O(s⁷)`. By palindromic symmetry of `log(exp(a/2)·exp(b)·exp(a/2))`,
every even-degree Taylor coefficient vanishes — so degrees 2, 4, 6 are all
zero, and the first non-zero residual sits at degree 7.

CAS verification at
`Lean-Trotter/scripts/verify_strangblock_degree7.py` confirms this:
degree-7 has 126 non-zero 7-letter words (over `{a, b}`), while degrees
2, 4, 6 all vanish identically. The `s⁷` bound with constant `10⁹`
dominates the series tail for `s < 1/4`.

### Proof status

**Currently accepted from a scoped Tier-2 axiom**
(`symmetric_bch_quintic_sub_poly_axiom`), analogous to Lean-Trotter's
Tier-2 fallback for the τ⁵-identification axiom. The full Lean proof
requires substantial new infrastructure:

* **Tier 1** (~1–2 days): add `bch_quintic_term a b` and
  `norm_bch_sextic_remainder_le` in `Basic.lean` (analogs of the existing
  `bch_quartic_term` and `norm_bch_quintic_remainder_le`), identifying
  the degree-5 coefficient of `bch(a,b)` and giving an `O(s⁶/(2−exp(s)))`
  tail bound.

* **Tier 2** (~1 week, the hardest): extend the 6-term algebraic
  decomposition of the cubic template
  `norm_symmetric_bch_cubic_sub_poly_le` (`Basic.lean`, ~line 3798) to
  the 8–10-term decomposition of the quintic version. Each extra term
  captures a degree-5 correction that is bounded by commutator algebra
  and the sextic remainder. CAS pipeline at
  `Lean-Trotter/scripts/compute_bch_prefactors.py` (extended to degree 7)
  discovers the decomposition mechanically.

* **Tier 3** (~1 day): triangle-inequality assembly of the 8–10 per-term
  `O(s⁷)` bounds, analogous to the cubic template's `5×10⁶ + 5000 + …`
  constant chain.

The axiom is introduced `private` so only the public
`norm_symmetric_bch_quintic_sub_poly_le` theorem appears in the API.
Downstream consumers — the `strangBlock_log` wrapper in `Palindromic.lean`
(B1.d) and the symbolic 5-factor composition in `Suzuki5Quintic.lean` (B2) —
depend only on the theorem, not on the underlying axiom.
-/

section QuinticTaylorBridge

variable {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
  [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### T2-F7e Phase E (parent discharge): Group C+D sub-axiom

The Phase D `symmetric_bch_quintic_extended_hdecomp` decomposes the residual
`sym_bch_cubic - sym_E₃ - sym_E₅` into 13 sub-pieces in 4 groups (A, B, C, D).
Group A (3 sub-pieces) and Group B (2 sub-pieces) are bounded directly via
Phase A's `norm_bch_inner_septic_remainder_le` /
`norm_bch_outer_septic_remainder_le`, the existing `bch_sextic_term`
Lipschitz bound (`norm_bch_sextic_term_diff_le`), and elementary commutator
estimates (Phase E.1 inline below).

Groups C and D (4+4 = 8 sub-pieces) cancel ALGEBRAICALLY at degrees 5 and 6
via the Phase B identity (`symmetric_bch_quintic_deg5_cancellation_pure_identity`)
and Phase C identity (`symmetric_bch_quintic_deg6_cancellation_pure_identity`)
respectively, leaving a deg-7+ residual. The bound on this residual is
captured in the **Group C+D sub-axiom** below — a stepping stone awaiting
the explicit Phase E.2 discharge (CLAUDE.md).

This sub-axiom is strictly weaker than the original parent axiom: it bounds
ONLY the combined Group C+D contribution (8 of 13 sub-pieces), not the full
residual. Phase A handles Group A; Phase E.1 inline handles Group B; this
sub-axiom handles Groups C+D. -/

/-! **Phase E.2 stepping-stone REPLACED** — the previous `private axiom
symmetric_bch_quintic_group_CD_axiom` (10⁸·s⁷ on 8 Group C+D pieces) has
been REPLACED with the proved theorem `symmetric_bch_quintic_group_CD_le`
(below), which derives the 10⁸·s⁷ bound from:
- `norm_R_T5_sept_le` (proved, ≤ 7·10⁶·s⁷)
- `norm_R_T6_sept_le` (proved, ≤ 10⁶·s⁷)
- `symmetric_bch_quintic_C5_diff_residual_le` (focused theorem, ≤ 5·10⁶·s⁷)

The remaining `C5_diff_residual` axiom is much smaller in scope (1 piece
instead of 8, 5·10⁶·s⁷ vs 10⁸·s⁷ constant, and isolates only the C₅
linearization residual). The constant 5·10⁶ is tightly tracking the
realistic Lipschitz piece bound (M⁴·‖WRest6‖ ≈ 1.9·10⁶·s⁷ where
M ≤ 4.22·s, ‖WRest6‖ ≤ 6000·s³ — the latter dominated by Phase A's
1.5·10⁶·s⁷ inner septic remainder bound). -/

/-! ### Group C+D 3-residual algebraic identity (Phase E.2 step 1)

The Phase E.2 discharge proceeds in two stages:
1. **Algebraic identity**: rewrite `Group C + Group D` as a sum of 3 explicit
   deg-7+ residuals using the Phase B and Phase C cancellation identities.
2. **Analytic bounds**: bound each residual by `K·s⁷` via the Lipschitz
   infrastructure (`norm_bch_*_term_diff_le`).

This section completes step 1. The residuals are:
- `R_T5_sept` = T₅ - ΔC₃_lin(V₃) - ΔC₃_quad(V₂) - T5_d6_op
- `R_T6_sept` = T₆ - ΔC₄_lin(V₂) - T6_d6_op
- `C5_diff_residual` = (C₅(z,a') - C₅(a'+b,a')) - ΔC₅_lin

The algebraic identity follows from:
- Phase B: ΔC₃_lin(V₃) + ΔC₃_quad(V₂) + ΔC₄_lin(V₂) + ½·[C₄(a',b),a'] = correction
- Phase C: T5_d6_op + T6_d6_op + ½·[C₅(a',b),a'] + C₆(a',b) + C₆(a'+b,a') + ΔC₅_lin = 0

Adding `(½·[C₄,a'] - correction) = -(ΔC₃_lin(V₃) + ΔC₃_quad(V₂) + ΔC₄_lin(V₂))`
and `(½·[C₅,a'] + C₆(a',b) + C₆(a'+b,a')) = -(T5_d6_op + T6_d6_op + ΔC₅_lin)`
to the C₅-diff piece gives the 3-residual rearrangement.
-/

set_option maxHeartbeats 4000000 in
private theorem group_CD_eq_three_residuals
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let V₄ : 𝔸 := bch_quartic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    let DC_a : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a
    -- LHS: Group C + Group D (8 pieces).
    (bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
       -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
    (bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') +
    (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b) +
    -symmetric_bch_quintic_correction_poly 𝕂 a b +
    (2 : 𝕂)⁻¹ • (bch_quintic_term 𝕂 a' b * a' - a' * bch_quintic_term 𝕂 a' b) +
    bch_sextic_term 𝕂 a' b +
    bch_sextic_term 𝕂 (a' + b) a' +
    (bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a')
    =
    -- RHS: R_T5_sept + R_T6_sept + C5_diff_residual.
    -- R_T5_sept = T₅ - ΔC₃_lin(V₃) - ΔC₃_quad(V₂) - T5_d6_op
    ((bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
        -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) -
     -- ΔC₃_lin(V₃, x, a')
     ((12 : 𝕂)⁻¹ • (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) +
      (12 : 𝕂)⁻¹ • (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) +
      (12 : 𝕂)⁻¹ • (a' * (a' * V₃ - V₃ * a') - (a' * V₃ - V₃ * a') * a')) -
     -- ΔC₃_quad(V₂, x, a')
     ((12 : 𝕂)⁻¹ • (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂)) -
     -- T5_d6_op = ΔC₃_lin(V₄) + (1/12)·([V₂,[V₃,a']]+[V₃,[V₂,a']])
     ((12 : 𝕂)⁻¹ • (V₄ * (x * a' - a' * x) - (x * a' - a' * x) * V₄ +
                     x * (V₄ * a' - a' * V₄) - (V₄ * a' - a' * V₄) * x +
                     a' * (a' * V₄ - V₄ * a') - (a' * V₄ - V₄ * a') * a') +
      (12 : 𝕂)⁻¹ • (V₂ * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * V₂ +
                     V₃ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₃))) +
    -- R_T6_sept = T₆ - ΔC₄_lin(V₂) - T6_d6_op
    ((bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') -
     -- ΔC₄_lin(V₂, x, a')
     ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) -
                                (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) -
                                (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) * a')) -
     -- T6_d6_op = ΔC₄_lin(V₃) + ΔC₄_quad(V₂)
     ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) -
                                (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) -
                                (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) -
                                (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) * a'))) +
    -- C5_diff_residual = (C₅(z,a') - C₅(a'+b,a')) - ΔC₅_lin (the 36-monomial polynomial)
    ((bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a') -
     ((-14 / 46080 : 𝕂) • (a * a * a * a * b * b) +
      (46 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (10 / 46080 : 𝕂) • (a * a * a * b * b * a) +
      (28 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (-54 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (-30 / 46080 : 𝕂) • (a * a * b * a * b * a) +
      (-52 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (-12 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (-20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
      (-8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
      (36 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (-32 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (30 / 46080 : 𝕂) • (a * b * a * b * a * a) +
      (128 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
      (32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
      (-10 / 46080 : 𝕂) • (a * b * b * a * a * a) +
      (-32 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (-40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
      (-48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
      (20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
      (32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
      (-36 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (54 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (32 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (-46 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (-128 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (12 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (-32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
      (14 / 46080 : 𝕂) • (b * b * a * a * a * a) +
      (32 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (52 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
      (-28 / 46080 : 𝕂) • (b * b * b * a * a * a) +
      (-32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
      (8 / 46080 : 𝕂) • (b * b * b * b * a * a))) := by
  intro a' z V₂ V₃ V₄ x DC_a
  -- Use Phase B identity (deg-5 cancellation).
  have hB := symmetric_bch_quintic_deg5_cancellation_pure_identity (𝕂 := 𝕂) a b
  -- Use Phase C identity (deg-6 cancellation; both sides equal 0).
  have hC := symmetric_bch_quintic_deg6_cancellation_pure_identity (𝕂 := 𝕂) a b
  -- Both hB and hC have inner let-bindings. Reduce them via show.
  show _ = _
  simp only [show ((2 : 𝕂)⁻¹ • a : 𝔸) = a' from rfl] at hB hC
  -- hB and hC should now match our let-bindings (a', V₂, V₃, V₄ identifications).
  -- The identity is: GOAL_LHS - GOAL_RHS = (LHS_B - RHS_B) + (LHS_C - RHS_C)
  -- = (LHS_B - correction_poly) + (LHS_C - 0), both 0 by hB and hC.
  linear_combination (norm := abel) hB + hC

/-- **Helper (½-smul commutator bound)**: `‖(2:𝕂)⁻¹ • (X*Y - Y*X)‖ ≤ ‖X‖·‖Y‖`.
Used in Phase E.1 to bound `½·[R₁_sept, a']` and `½·[C₆(a',b), a']`. -/
private lemma norm_half_smul_bracket_le {𝕂 : Type*} [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (X Y : 𝔸) :
    ‖(2 : 𝕂)⁻¹ • (X * Y - Y * X)‖ ≤ ‖X‖ * ‖Y‖ := by
  have h2_inv : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hcomm : ‖X * Y - Y * X‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
    calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := by
          rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖X‖ * ‖Y‖ := by ring
  calc ‖(2 : 𝕂)⁻¹ • (X * Y - Y * X)‖
      ≤ ‖(2 : 𝕂)⁻¹‖ * ‖X * Y - Y * X‖ := norm_smul_le _ _
    _ = (2 : ℝ)⁻¹ * ‖X * Y - Y * X‖ := by rw [h2_inv]
    _ ≤ (2 : ℝ)⁻¹ * (2 * ‖X‖ * ‖Y‖) :=
        mul_le_mul_of_nonneg_left hcomm (by norm_num)
    _ = ‖X‖ * ‖Y‖ := by ring

/-! ### T2-F7e Phase E.2 step 2: R_T5_sept algebraic decomposition

The first residual `R_T5_sept = T₅ - ΔC₃_lin(V₃) - ΔC₃_quad(V₂) - T5_d6_op`
(from `group_CD_eq_three_residuals` above) decomposes structurally as a sum
of L-form (linear-in-W) and Q-form (quadratic-in-W) operator pieces:

```
R_T5_sept = (1/12) · L_C3(a'+b, WHigh, a') + (1/12) · Q_residual
```

where:
- `WHigh := V₅ + V₆ + R₁_sept` (deg-5+ part of W after V₂, V₃, V₄ extracted)
- `WMid := V₄ + V₅ + V₆ + R₁_sept`
- `WRestSept := V₃ + V₄ + V₅ + V₆ + R₁_sept`
- `Q_residual := Q(V₂, WMid) + Q(WMid, V₂) + Q(WRestSept, WRestSept)`
  (the deg-7+ cross terms in the bilinear expansion of Q_C3(W, a'))

The L_C3 and Q_C3 templates match the cubic template's `L_W` and `Q_W` shapes
(see `Basic.lean`'s `norm_symmetric_bch_cubic_sub_poly_le`); the bilinear
extension is via `bch_cubic_term_LQ_decomp` (`Basic.lean`).

The proof uses:
- `bch_cubic_term_LQ_decomp` to split bch_cubic_term(z, a') - bch_cubic_term((a'+b), a')
  into L+Q form with W = z - (a'+b) = V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept (by
  R₁_sept's definition).
- `match_scalars <;> ring` after distributing smul/mul/add and unfolding V₂, x,
  a', WHigh, WMid, WRestSept (keeping V₃, V₄, V₅, V₆, R₁_sept atomic).

The cancellation `(12)⁻¹·L_V₂ + (96)⁻¹·(b·DC_a - DC_a·b) = 0` (cubic identity)
fires automatically via the polynomial reduction. -/

set_option maxHeartbeats 64000000 in
private theorem R_T5_sept_decomp_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let V₄ : 𝔸 := bch_quartic_term 𝕂 a' b
    let V₅ : 𝔸 := bch_quintic_term 𝕂 a' b
    let V₆ : 𝔸 := bch_sextic_term 𝕂 a' b
    let R₁_sept : 𝔸 := z - (a' + b) - V₂ - V₃ - V₄ - V₅ - V₆
    let WHigh : 𝔸 := V₅ + V₆ + R₁_sept
    let WMid : 𝔸 := V₄ + V₅ + V₆ + R₁_sept
    let WRestSept : 𝔸 := V₃ + V₄ + V₅ + V₆ + R₁_sept
    let x : 𝔸 := a' + b
    let DC_a : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a
    -- LHS: R_T5_sept = T₅ - ΔC₃_lin(V₃) - ΔC₃_quad(V₂) - T5_d6_op
    ((bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
       -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) -
     -- ΔC₃_lin(V₃, x, a')
     ((12 : 𝕂)⁻¹ • (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) +
      (12 : 𝕂)⁻¹ • (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) +
      (12 : 𝕂)⁻¹ • (a' * (a' * V₃ - V₃ * a') - (a' * V₃ - V₃ * a') * a')) -
     -- ΔC₃_quad(V₂)
     ((12 : 𝕂)⁻¹ • (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂)) -
     -- T5_d6_op = ΔC₃_lin(V₄) + (1/12)·([V₂,[V₃,a']]+[V₃,[V₂,a']])
     ((12 : 𝕂)⁻¹ • (V₄ * (x * a' - a' * x) - (x * a' - a' * x) * V₄ +
                     x * (V₄ * a' - a' * V₄) - (V₄ * a' - a' * V₄) * x +
                     a' * (a' * V₄ - V₄ * a') - (a' * V₄ - V₄ * a') * a') +
      (12 : 𝕂)⁻¹ • (V₂ * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * V₂ +
                     V₃ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₃)))
    =
    -- RHS: (12)⁻¹·L_C3(a'+b, WHigh, a') + (12)⁻¹·Q_residual
    -- L_C3 template (matches cubic template's L_W shape).
    (12 : 𝕂)⁻¹ • (
      x * WHigh * a' + WHigh * x * a' - x * a' * WHigh - x * a' * WHigh -
      WHigh * a' * x - WHigh * a' * x +
      a' * x * WHigh + a' * WHigh * x + a' * a' * WHigh -
      a' * WHigh * a' - a' * WHigh * a' + WHigh * a' * a') +
    -- Q_residual = Q(V₂, WMid) + Q(WMid, V₂) + Q(WRestSept, WRestSept)
    -- where Q(X, Y) = X·Y·a' - X·a'·Y - Y·a'·X + a'·X·Y.
    (12 : 𝕂)⁻¹ • (
      -- Q(V₂, WMid)
      V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid +
      -- Q(WMid, V₂)
      WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂ +
      -- Q(WRestSept, WRestSept) = WRestSept²·a' - 2·WRestSept·a'·WRestSept + a'·WRestSept²
      WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
      WRestSept * a' * WRestSept + a' * WRestSept * WRestSept) := by
  intro a' z V₂ V₃ V₄ V₅ V₆ R₁_sept WHigh WMid WRestSept x DC_a
  -- Step 1: z = (a'+b) + (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) by R₁_sept's definition.
  have hz_W : z = (a' + b) + (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) := by
    show z = _
    -- Unfold R₁_sept's let-binding.
    rw [show R₁_sept = z - (a' + b) - V₂ - V₃ - V₄ - V₅ - V₆ from rfl]
    abel
  -- Step 2: Apply LQ decomp at x = a'+b, W = V₂+V₃+V₄+V₅+V₆+R₁_sept, y = a'.
  have hLQ := bch_cubic_term_LQ_decomp (𝕂 := 𝕂) (a' + b)
              (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) a'
  -- hLQ: bch_cubic_term((a'+b)+(V₂+...+R₁_sept), a') - bch_cubic_term((a'+b), a') = ...
  -- After substituting z = (a'+b) + (V₂+...+R₁_sept), this gives
  -- bch_cubic_term(z, a') - bch_cubic_term((a'+b), a') = ...
  -- Convert hLQ to use z:
  rw [show ((a' + b) + (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) : 𝔸) = z from hz_W.symm] at hLQ
  -- Now hLQ : bch_cubic_term(z, a') - bch_cubic_term((a'+b), a') = (12)⁻¹·L_expr + (12)⁻¹·Q_expr
  -- Substitute hLQ into the goal to replace the bch_cubic_term diff.
  rw [hLQ]
  -- Step 3: Goal is now polynomial. Unfold V₂, DC_a, x, a', WHigh, WMid, WRestSept.
  -- Keep V₃, V₄, V₅, V₆, R₁_sept atomic.
  show _ = _
  simp only [show V₂ = ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) from rfl,
             show DC_a = a * (a * b - b * a) - (a * b - b * a) * a from rfl,
             show x = ((2 : 𝕂)⁻¹ • a + b : 𝔸) from rfl,
             show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl,
             show WHigh = V₅ + V₆ + R₁_sept from rfl,
             show WMid = V₄ + V₅ + V₆ + R₁_sept from rfl,
             show WRestSept = V₃ + V₄ + V₅ + V₆ + R₁_sept from rfl]
  -- Distribute smul/mul/add throughout.
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  -- Close via match_scalars + ring.
  match_scalars <;> ring

/-! ### T2-F7e Phase E.2 step 2b: norm bound on R_T5_sept

Uses `R_T5_sept_decomp_eq` to express R_T5_sept = (12)⁻¹·L_C3 + (12)⁻¹·Q_residual,
then bounds each piece by triangle inequality. -/

-- Triple product norm bound: `‖X*Y*Z‖ ≤ ‖X‖·‖Y‖·‖Z‖`. Extracted helper.
private lemma norm_triple_le_aux {𝔸 : Type*} [NormedRing 𝔸] (X Y Z : 𝔸) :
    ‖X * Y * Z‖ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ := by
  calc ‖X * Y * Z‖ ≤ ‖X * Y‖ * ‖Z‖ := norm_mul_le _ _
    _ ≤ (‖X‖ * ‖Y‖) * ‖Z‖ := by gcongr; exact norm_mul_le _ _

-- 4-letter product norm bound: `‖X*Y*Z*W‖ ≤ ‖X‖·‖Y‖·‖Z‖·‖W‖`. Extracted helper.
private lemma norm_quad_le_aux {𝔸 : Type*} [NormedRing 𝔸] (X Y Z W : 𝔸) :
    ‖X * Y * Z * W‖ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ * ‖W‖ := by
  calc ‖X * Y * Z * W‖ ≤ ‖X * Y * Z‖ * ‖W‖ := norm_mul_le _ _
    _ ≤ (‖X‖ * ‖Y‖ * ‖Z‖) * ‖W‖ :=
      mul_le_mul_of_nonneg_right (norm_triple_le_aux X Y Z) (norm_nonneg _)

-- Q-bilinear form 4-term bound: `‖X·Y·a' - X·a'·Y - Y·a'·X + a'·X·Y‖ ≤ 4·‖X‖·‖Y‖·‖a'‖`.
private lemma norm_Q_form_le_aux {𝔸 : Type*} [NormedRing 𝔸] (X Y a' : 𝔸) :
    ‖X * Y * a' - X * a' * Y - Y * a' * X + a' * X * Y‖ ≤
      4 * ‖X‖ * ‖Y‖ * ‖a'‖ := by
  have h1 : ‖X * Y * a'‖ ≤ ‖X‖ * ‖Y‖ * ‖a'‖ := norm_triple_le_aux X Y a'
  have h2 : ‖X * a' * Y‖ ≤ ‖X‖ * ‖Y‖ * ‖a'‖ := by
    calc ‖X * a' * Y‖ ≤ ‖X‖ * ‖a'‖ * ‖Y‖ := norm_triple_le_aux X a' Y
      _ = ‖X‖ * ‖Y‖ * ‖a'‖ := by ring
  have h3 : ‖Y * a' * X‖ ≤ ‖X‖ * ‖Y‖ * ‖a'‖ := by
    calc ‖Y * a' * X‖ ≤ ‖Y‖ * ‖a'‖ * ‖X‖ := norm_triple_le_aux Y a' X
      _ = ‖X‖ * ‖Y‖ * ‖a'‖ := by ring
  have h4 : ‖a' * X * Y‖ ≤ ‖X‖ * ‖Y‖ * ‖a'‖ := by
    calc ‖a' * X * Y‖ ≤ ‖a'‖ * ‖X‖ * ‖Y‖ := norm_triple_le_aux a' X Y
      _ = ‖X‖ * ‖Y‖ * ‖a'‖ := by ring
  have hreorg : X * Y * a' - X * a' * Y - Y * a' * X + a' * X * Y =
                X * Y * a' + (-(X * a' * Y)) + (-(Y * a' * X)) + a' * X * Y := by abel
  rw [hreorg]
  have b3 := norm_add_le (X * Y * a' + (-(X * a' * Y)) + (-(Y * a' * X))) (a' * X * Y)
  have b2 := norm_add_le (X * Y * a' + (-(X * a' * Y))) (-(Y * a' * X))
  have b1 := norm_add_le (X * Y * a') (-(X * a' * Y))
  simp only [norm_neg] at b1 b2 b3
  linarith

set_option maxHeartbeats 1600000 in
private theorem norm_R_T5_sept_le
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let V₄ : 𝔸 := bch_quartic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    let DC_a : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a
    ‖((bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
       -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) -
     ((12 : 𝕂)⁻¹ • (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) +
      (12 : 𝕂)⁻¹ • (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) +
      (12 : 𝕂)⁻¹ • (a' * (a' * V₃ - V₃ * a') - (a' * V₃ - V₃ * a') * a')) -
     ((12 : 𝕂)⁻¹ • (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂)) -
     ((12 : 𝕂)⁻¹ • (V₄ * (x * a' - a' * x) - (x * a' - a' * x) * V₄ +
                     x * (V₄ * a' - a' * V₄) - (V₄ * a' - a' * V₄) * x +
                     a' * (a' * V₄ - V₄ * a') - (a' * V₄ - V₄ * a') * a') +
      (12 : 𝕂)⁻¹ • (V₂ * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * V₂ +
                     V₃ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₃)))‖
    ≤ 7000000 * (‖a‖ + ‖b‖) ^ 7 := by
  intro a' z V₂ V₃ V₄ x DC_a
  -- Setup norms.
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt : s < 1 / 4 := hab
  have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ s / 2 := by
    show ‖(2 : 𝕂)⁻¹ • a‖ ≤ _
    calc ‖(2 : 𝕂)⁻¹ • a‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
      _ ≤ s / 2 := by have := norm_nonneg b; linarith
  have ha'_b_le : ‖a' + b‖ ≤ 3 * s / 2 := by
    calc ‖a' + b‖ ≤ ‖a'‖ + ‖b‖ := norm_add_le _ _
      _ ≤ s / 2 + s := by have := norm_nonneg a; linarith
      _ = 3 * s / 2 := by ring
  -- ‖a'‖ ≤ ‖a‖ (since a' = (1/2)·a and ‖(1/2)‖ = 1/2 ≤ 1).
  have ha'_a : ‖a'‖ ≤ ‖a‖ := by
    show ‖(2 : 𝕂)⁻¹ • a‖ ≤ _
    calc ‖(2 : 𝕂)⁻¹ • a‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
      _ ≤ ‖a‖ := by linarith [norm_nonneg a]
  have hs1_le : ‖a'‖ + ‖b‖ ≤ s := by linarith [ha'_a]
  have hs1_nn : (0 : ℝ) ≤ ‖a'‖ + ‖b‖ := by positivity
  -- ‖V₂‖ ≤ s²/2.
  have hV2_le : ‖V₂‖ ≤ s ^ 2 / 2 := by
    show ‖(2 : 𝕂)⁻¹ • (a' * b - b * a')‖ ≤ _
    have hcomm : ‖a' * b - b * a'‖ ≤ 2 * ‖a'‖ * ‖b‖ := by
      calc ‖a' * b - b * a'‖ ≤ ‖a' * b‖ + ‖b * a'‖ := by
            rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖a'‖ * ‖b‖ + ‖b‖ * ‖a'‖ := by gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖a'‖ * ‖b‖ := by ring
    calc ‖(2 : 𝕂)⁻¹ • (a' * b - b * a')‖
        ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a' * b - b * a'‖ := norm_smul_le _ _
      _ = (2 : ℝ)⁻¹ * ‖a' * b - b * a'‖ := by rw [h_half_norm]
      _ ≤ (2 : ℝ)⁻¹ * (2 * ‖a'‖ * ‖b‖) := by
          apply mul_le_mul_of_nonneg_left hcomm (by norm_num)
      _ = ‖a'‖ * ‖b‖ := by ring
      _ ≤ (s / 2) * s := by
          apply mul_le_mul ha'_le _ (norm_nonneg _) (by linarith)
          have := norm_nonneg a; linarith
      _ = s ^ 2 / 2 := by ring
  -- ‖V₃‖ ≤ s³, ‖V₄‖ ≤ s⁴, ‖V₅‖ ≤ s⁵, ‖V₆‖ ≤ s⁶.
  have hV3_le : ‖V₃‖ ≤ s ^ 3 := by
    show ‖bch_cubic_term 𝕂 a' b‖ ≤ _
    calc ‖bch_cubic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 3 := norm_bch_cubic_term_le a' b
      _ ≤ s ^ 3 := pow_le_pow_left₀ hs1_nn hs1_le 3
  have hV4_le : ‖V₄‖ ≤ s ^ 4 := by
    show ‖bch_quartic_term 𝕂 a' b‖ ≤ _
    calc ‖bch_quartic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 4 := norm_bch_quartic_term_le a' b
      _ ≤ s ^ 4 := pow_le_pow_left₀ hs1_nn hs1_le 4
  have hV5_le : ‖bch_quintic_term 𝕂 a' b‖ ≤ s ^ 5 := by
    calc ‖bch_quintic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 5 := norm_bch_quintic_term_le a' b
      _ ≤ s ^ 5 := pow_le_pow_left₀ hs1_nn hs1_le 5
  have hV6_le : ‖bch_sextic_term 𝕂 a' b‖ ≤ s ^ 6 := by
    calc ‖bch_sextic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 6 := norm_bch_sextic_term_le a' b
      _ ≤ s ^ 6 := pow_le_pow_left₀ hs1_nn hs1_le 6
  have hR1_le : ‖z - (a' + b) - V₂ - V₃ - V₄ -
                  bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b‖ ≤
                1500000 * s ^ 7 :=
    norm_bch_inner_septic_remainder_le (𝕂 := 𝕂) a b hab
  -- Apply algebraic decomposition.
  rw [R_T5_sept_decomp_eq (𝕂 := 𝕂) a b]
  -- Goal: ‖(12)⁻¹·L_C3 + (12)⁻¹·Q_residual‖ ≤ 7·10⁶·s⁷
  -- Set up local names for intermediate expressions.
  set V₅ : 𝔸 := bch_quintic_term 𝕂 a' b with hV5_def
  set V₆ : 𝔸 := bch_sextic_term 𝕂 a' b with hV6_def
  set R₁_sept : 𝔸 := z - (a' + b) - V₂ - V₃ - V₄ - V₅ - V₆ with hR1_def
  set WHigh : 𝔸 := V₅ + V₆ + R₁_sept with hWHigh_def
  set WMid : 𝔸 := V₄ + V₅ + V₆ + R₁_sept with hWMid_def
  set WRestSept : 𝔸 := V₃ + V₄ + V₅ + V₆ + R₁_sept with hWRest_def
  have hWHigh_nn : (0:ℝ) ≤ ‖WHigh‖ := norm_nonneg _
  have hWMid_nn : (0:ℝ) ≤ ‖WMid‖ := norm_nonneg _
  have hWRest_nn : (0:ℝ) ≤ ‖WRestSept‖ := norm_nonneg _
  have hR1_le' : ‖R₁_sept‖ ≤ 1500000 * s ^ 7 := by rw [hR1_def]; exact hR1_le
  -- Pow bounds: s^k ≤ s^j · (1/4)^(k-j) for s ≤ 1/4.
  have hs2_le : s^2 ≤ 1/16 := by nlinarith [hs_lt, hs_nn]
  have hs3_le : s^3 ≤ 1/64 := by nlinarith [hs_lt, hs_nn, sq_nonneg s]
  have hs4_le : s^4 ≤ 1/256 := by nlinarith [hs2_le, sq_nonneg (s^2)]
  have hs5_nn : (0:ℝ) ≤ s^5 := pow_nonneg hs_nn 5
  have hs4_nn : (0:ℝ) ≤ s^4 := pow_nonneg hs_nn 4
  have hs3_nn : (0:ℝ) ≤ s^3 := pow_nonneg hs_nn 3
  have hs6_le_s5 : s^6 ≤ s^5 * (1/4) := by
    have heq : s^6 = s * s^5 := by ring
    rw [heq]; nlinarith [hs5_nn, hs_lt, hs_nn]
  have hs7_le_s5 : s^7 ≤ s^5 * (1/16) := by
    have heq : s^7 = s^2 * s^5 := by ring
    rw [heq]; nlinarith [hs5_nn, hs2_le]
  have hs5_le_s4 : s^5 ≤ s^4 * (1/4) := by
    have heq : s^5 = s * s^4 := by ring
    rw [heq]; nlinarith [hs4_nn, hs_lt, hs_nn]
  have hs6_le_s4 : s^6 ≤ s^4 * (1/16) := by
    have heq : s^6 = s^2 * s^4 := by ring
    rw [heq]; nlinarith [hs4_nn, hs2_le]
  have hs7_le_s4 : s^7 ≤ s^4 * (1/64) := by
    have heq : s^7 = s^3 * s^4 := by ring
    rw [heq]; nlinarith [hs4_nn, hs3_le]
  have hs4_le_s3 : s^4 ≤ s^3 * (1/4) := by
    have heq : s^4 = s * s^3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs_lt, hs_nn]
  have hs5_le_s3 : s^5 ≤ s^3 * (1/16) := by
    have heq : s^5 = s^2 * s^3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs2_le]
  have hs6_le_s3 : s^6 ≤ s^3 * (1/64) := by
    have heq : s^6 = s^3 * s^3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs3_le]
  have hs7_le_s3 : s^7 ≤ s^3 * (1/256) := by
    have heq : s^7 = s^4 * s^3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs4_le]
  -- Bounds on WHigh, WMid, WRestSept.
  have hWHigh_le : ‖WHigh‖ ≤ 100000 * s ^ 5 := by
    have hsum : ‖WHigh‖ ≤ ‖V₅‖ + ‖V₆‖ + ‖R₁_sept‖ := by
      rw [hWHigh_def]
      have h1 := norm_add_le (V₅ + V₆) R₁_sept
      have h2 := norm_add_le V₅ V₆
      linarith
    have hV5 : ‖V₅‖ ≤ s ^ 5 := hV5_le
    have hV6 : ‖V₆‖ ≤ s ^ 6 := hV6_le
    linarith
  have hWMid_le : ‖WMid‖ ≤ 25000 * s ^ 4 := by
    have hsum : ‖WMid‖ ≤ ‖V₄‖ + ‖V₅‖ + ‖V₆‖ + ‖R₁_sept‖ := by
      rw [hWMid_def]
      have h1 := norm_add_le (V₄ + V₅ + V₆) R₁_sept
      have h2 := norm_add_le (V₄ + V₅) V₆
      have h3 := norm_add_le V₄ V₅
      linarith
    have hV5 : ‖V₅‖ ≤ s ^ 5 := hV5_le
    have hV6 : ‖V₆‖ ≤ s ^ 6 := hV6_le
    linarith
  have hWRest_le : ‖WRestSept‖ ≤ 6000 * s ^ 3 := by
    have hsum : ‖WRestSept‖ ≤ ‖V₃‖ + ‖V₄‖ + ‖V₅‖ + ‖V₆‖ + ‖R₁_sept‖ := by
      rw [hWRest_def]
      have h1 := norm_add_le (V₃ + V₄ + V₅ + V₆) R₁_sept
      have h2 := norm_add_le (V₃ + V₄ + V₅) V₆
      have h3 := norm_add_le (V₃ + V₄) V₅
      have h4 := norm_add_le V₃ V₄
      linarith
    have hV5 : ‖V₅‖ ≤ s ^ 5 := hV5_le
    have hV6 : ‖V₆‖ ≤ s ^ 6 := hV6_le
    linarith
  have h12_inv : ‖(12 : 𝕂)⁻¹‖ = (12 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Bound L_C3: 12 sub-terms, each ≤ (3s/2)²·‖WHigh‖.
  have hmax_a' : ‖a'‖ ≤ 3 * s / 2 := by linarith
  have hmax_x : ‖a' + b‖ ≤ 3 * s / 2 := ha'_b_le
  set K_L : ℝ := (3 * s / 2) ^ 2 * ‖WHigh‖ with hK_L_def
  have hK_L_nn : 0 ≤ K_L := by rw [hK_L_def]; positivity
  -- Bound each of the 12 sub-terms of L_C3.
  have hL_term : ∀ X Y W : 𝔸, ‖X‖ ≤ 3*s/2 → ‖Y‖ ≤ 3*s/2 → ‖W‖ = ‖WHigh‖ →
                 ‖X * Y * W‖ ≤ K_L ∧ ‖X * W * Y‖ ≤ K_L ∧ ‖W * X * Y‖ ≤ K_L := by
    intro X Y W hX hY hW
    refine ⟨?_, ?_, ?_⟩
    · calc ‖X * Y * W‖ ≤ ‖X‖ * ‖Y‖ * ‖W‖ := norm_triple_le_aux X Y W
        _ ≤ (3*s/2) * (3*s/2) * ‖W‖ := by gcongr
        _ = (3*s/2)^2 * ‖W‖ := by ring
        _ = K_L := by rw [hK_L_def, hW]
    · calc ‖X * W * Y‖ ≤ ‖X‖ * ‖W‖ * ‖Y‖ := norm_triple_le_aux X W Y
        _ ≤ (3*s/2) * ‖W‖ * (3*s/2) := by gcongr
        _ = (3*s/2)^2 * ‖W‖ := by ring
        _ = K_L := by rw [hK_L_def, hW]
    · calc ‖W * X * Y‖ ≤ ‖W‖ * ‖X‖ * ‖Y‖ := norm_triple_le_aux W X Y
        _ ≤ ‖W‖ * (3*s/2) * (3*s/2) := by gcongr
        _ = (3*s/2)^2 * ‖W‖ := by ring
        _ = K_L := by rw [hK_L_def, hW]
  -- 9 distinct triple-product types in L_C3, each bounded by K_L.
  have e1  : ‖(a'+b) * WHigh * a'‖ ≤ K_L := (hL_term (a'+b) a' WHigh hmax_x hmax_a' rfl).2.1
  have e2  : ‖WHigh * (a'+b) * a'‖ ≤ K_L := (hL_term (a'+b) a' WHigh hmax_x hmax_a' rfl).2.2
  have e3  : ‖(a'+b) * a' * WHigh‖ ≤ K_L := (hL_term (a'+b) a' WHigh hmax_x hmax_a' rfl).1
  have e4  : ‖WHigh * a' * (a'+b)‖ ≤ K_L := (hL_term a' (a'+b) WHigh hmax_a' hmax_x rfl).2.2
  have e5  : ‖a' * (a'+b) * WHigh‖ ≤ K_L := (hL_term a' (a'+b) WHigh hmax_a' hmax_x rfl).1
  have e6  : ‖a' * WHigh * (a'+b)‖ ≤ K_L := (hL_term a' (a'+b) WHigh hmax_a' hmax_x rfl).2.1
  have e7  : ‖a' * a' * WHigh‖ ≤ K_L := (hL_term a' a' WHigh hmax_a' hmax_a' rfl).1
  have e8  : ‖a' * WHigh * a'‖ ≤ K_L := (hL_term a' a' WHigh hmax_a' hmax_a' rfl).2.1
  have e9  : ‖WHigh * a' * a'‖ ≤ K_L := (hL_term a' a' WHigh hmax_a' hmax_a' rfl).2.2
  -- Triangle inequality on the 12 summands of L_C3.
  -- L_C3 = e1 + e2 - 2·e3 - 2·e4 + e5 + e6 + e7 - 2·e8 + e9 (with abuse of notation).
  have hL_norm : ‖((a' + b) * WHigh * a' + WHigh * (a' + b) * a' -
                   (a' + b) * a' * WHigh - (a' + b) * a' * WHigh -
                   WHigh * a' * (a' + b) - WHigh * a' * (a' + b) +
                   a' * (a' + b) * WHigh + a' * WHigh * (a' + b) +
                   a' * a' * WHigh - a' * WHigh * a' - a' * WHigh * a' +
                   WHigh * a' * a')‖ ≤ 12 * K_L := by
    have hreorg :
        (a' + b) * WHigh * a' + WHigh * (a' + b) * a' -
        (a' + b) * a' * WHigh - (a' + b) * a' * WHigh -
        WHigh * a' * (a' + b) - WHigh * a' * (a' + b) +
        a' * (a' + b) * WHigh + a' * WHigh * (a' + b) +
        a' * a' * WHigh - a' * WHigh * a' - a' * WHigh * a' +
        WHigh * a' * a' =
        (a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
        (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
        (-(WHigh * a' * (a' + b))) + (-(WHigh * a' * (a' + b))) +
        a' * (a' + b) * WHigh + a' * WHigh * (a' + b) +
        a' * a' * WHigh + (-(a' * WHigh * a')) + (-(a' * WHigh * a')) +
        WHigh * a' * a' := by abel
    rw [hreorg]
    -- Repeated norm_add_le.
    have a11 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
      (-(WHigh * a' * (a' + b))) + (-(WHigh * a' * (a' + b))) +
      a' * (a' + b) * WHigh + a' * WHigh * (a' + b) +
      a' * a' * WHigh + (-(a' * WHigh * a')) + (-(a' * WHigh * a'))) (WHigh * a' * a')
    have a10 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
      (-(WHigh * a' * (a' + b))) + (-(WHigh * a' * (a' + b))) +
      a' * (a' + b) * WHigh + a' * WHigh * (a' + b) +
      a' * a' * WHigh + (-(a' * WHigh * a'))) (-(a' * WHigh * a'))
    have a9 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
      (-(WHigh * a' * (a' + b))) + (-(WHigh * a' * (a' + b))) +
      a' * (a' + b) * WHigh + a' * WHigh * (a' + b) +
      a' * a' * WHigh) (-(a' * WHigh * a'))
    have a8 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
      (-(WHigh * a' * (a' + b))) + (-(WHigh * a' * (a' + b))) +
      a' * (a' + b) * WHigh + a' * WHigh * (a' + b)) (a' * a' * WHigh)
    have a7 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
      (-(WHigh * a' * (a' + b))) + (-(WHigh * a' * (a' + b))) +
      a' * (a' + b) * WHigh) (a' * WHigh * (a' + b))
    have a6 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
      (-(WHigh * a' * (a' + b))) + (-(WHigh * a' * (a' + b)))) (a' * (a' + b) * WHigh)
    have a5 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh)) +
      (-(WHigh * a' * (a' + b)))) (-(WHigh * a' * (a' + b)))
    have a4 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh)) + (-((a' + b) * a' * WHigh))) (-(WHigh * a' * (a' + b)))
    have a3 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' +
      (-((a' + b) * a' * WHigh))) (-((a' + b) * a' * WHigh))
    have a2 := norm_add_le ((a' + b) * WHigh * a' + WHigh * (a' + b) * a') (-((a' + b) * a' * WHigh))
    have a1 := norm_add_le ((a' + b) * WHigh * a') (WHigh * (a' + b) * a')
    simp only [norm_neg] at a2 a3 a4 a5 a9 a10
    linarith
  -- K_L ≤ ((3s/2)^2 · 100000 · s^5) ≤ ... arithmetic for K_L bound in s^7.
  have hK_L_le : K_L ≤ 225000 * s ^ 7 := by
    rw [hK_L_def]
    have : (3 * s / 2) ^ 2 = 9/4 * s^2 := by ring
    rw [this]
    calc 9/4 * s^2 * ‖WHigh‖ ≤ 9/4 * s^2 * (100000 * s^5) := by
          apply mul_le_mul_of_nonneg_left hWHigh_le (by positivity)
      _ = 225000 * s^7 := by ring
  -- Bound (12)⁻¹·L_C3.
  have hL_final : ‖(12 : 𝕂)⁻¹ • ((a' + b) * WHigh * a' + WHigh * (a' + b) * a' -
                   (a' + b) * a' * WHigh - (a' + b) * a' * WHigh -
                   WHigh * a' * (a' + b) - WHigh * a' * (a' + b) +
                   a' * (a' + b) * WHigh + a' * WHigh * (a' + b) +
                   a' * a' * WHigh - a' * WHigh * a' - a' * WHigh * a' +
                   WHigh * a' * a')‖ ≤ 225000 * s ^ 7 := by
    calc _ ≤ ‖(12 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
      _ = (12 : ℝ)⁻¹ * _ := by rw [h12_inv]
      _ ≤ (12 : ℝ)⁻¹ * (12 * K_L) := by
          apply mul_le_mul_of_nonneg_left hL_norm (by norm_num)
      _ ≤ (12 : ℝ)⁻¹ * (12 * (225000 * s^7)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left hK_L_le (by norm_num)
      _ = 225000 * s ^ 7 := by ring
  -- Bound Q_residual via 3 applications of norm_Q_form_le_aux.
  have hQ1 : ‖V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid‖ ≤
             4 * ‖V₂‖ * ‖WMid‖ * ‖a'‖ := norm_Q_form_le_aux V₂ WMid a'
  have hQ2 : ‖WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂‖ ≤
             4 * ‖WMid‖ * ‖V₂‖ * ‖a'‖ := norm_Q_form_le_aux WMid V₂ a'
  have hQ3 : ‖WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
             WRestSept * a' * WRestSept + a' * WRestSept * WRestSept‖ ≤
             4 * ‖WRestSept‖ * ‖WRestSept‖ * ‖a'‖ := norm_Q_form_le_aux WRestSept WRestSept a'
  -- Convert each Q bound to s⁷ bound.
  have hV2_nn : (0:ℝ) ≤ ‖V₂‖ := norm_nonneg _
  have ha'_nn : (0:ℝ) ≤ ‖a'‖ := norm_nonneg _
  have hQ1_s7 : 4 * ‖V₂‖ * ‖WMid‖ * ‖a'‖ ≤ 25000 * s ^ 7 := by
    calc 4 * ‖V₂‖ * ‖WMid‖ * ‖a'‖
        ≤ 4 * (s^2/2) * (25000 * s^4) * (s/2) := by gcongr
      _ = 25000 * s^7 := by ring
  have hQ2_s7 : 4 * ‖WMid‖ * ‖V₂‖ * ‖a'‖ ≤ 25000 * s ^ 7 := by
    calc 4 * ‖WMid‖ * ‖V₂‖ * ‖a'‖
        ≤ 4 * (25000 * s^4) * (s^2/2) * (s/2) := by gcongr
      _ = 25000 * s^7 := by ring
  have hQ3_s7 : 4 * ‖WRestSept‖ * ‖WRestSept‖ * ‖a'‖ ≤ 72000000 * s ^ 7 := by
    calc 4 * ‖WRestSept‖ * ‖WRestSept‖ * ‖a'‖
        ≤ 4 * (6000 * s^3) * (6000 * s^3) * (s/2) := by gcongr
      _ = 72000000 * s^7 := by ring
  -- Sum the three Q pieces via triangle.
  have hQ_sum : ‖(V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid +
                  (WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂ +
                  (WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
                   WRestSept * a' * WRestSept + a' * WRestSept * WRestSept)))‖ ≤
                 72050000 * s ^ 7 := by
    have h2 := norm_add_le (V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid)
                ((WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂) +
                 (WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
                  WRestSept * a' * WRestSept + a' * WRestSept * WRestSept))
    have h3 := norm_add_le (WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂)
                (WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
                 WRestSept * a' * WRestSept + a' * WRestSept * WRestSept)
    have hbound : ‖V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid‖ ≤ 25000*s^7 := by
      linarith [hQ1, hQ1_s7]
    have hbound2 : ‖WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂‖ ≤ 25000*s^7 := by
      linarith [hQ2, hQ2_s7]
    have hbound3 : ‖WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
                    WRestSept * a' * WRestSept + a' * WRestSept * WRestSept‖ ≤ 72000000*s^7 := by
      linarith [hQ3, hQ3_s7]
    linarith
  -- Bound (12)⁻¹·Q_residual.
  have hQ_final : ‖(12 : 𝕂)⁻¹ • (V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid +
                                  (WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂ +
                                  (WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
                                   WRestSept * a' * WRestSept + a' * WRestSept * WRestSept)))‖ ≤
                  6004167 * s ^ 7 := by
    calc _ ≤ ‖(12 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
      _ = (12 : ℝ)⁻¹ * _ := by rw [h12_inv]
      _ ≤ (12 : ℝ)⁻¹ * (72050000 * s^7) := by
          apply mul_le_mul_of_nonneg_left hQ_sum (by norm_num)
      _ ≤ 6004167 * s^7 := by linarith [hs7_nn]
  -- The goal LHS structure: `(12)⁻¹ • L_expr + (12)⁻¹ • Q_expr`.
  -- Use abel to align Q_expr's parenthesization (left-associated vs right-associated).
  -- Triangle on the goal: ‖L + Q‖ ≤ ‖L‖ + ‖Q‖.
  -- We need Q_expr's parenthesization in the goal to match hQ_final's form.
  -- The decomp's RHS Q part has form:
  -- (V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid +
  --  (WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂) +
  --  ...) — this needs abel-rearrangement to match hQ_sum's form.
  have habs_eq : ((V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid +
                   WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂ +
                   WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
                   WRestSept * a' * WRestSept + a' * WRestSept * WRestSept) : 𝔸) =
                 (V₂ * WMid * a' - V₂ * a' * WMid - WMid * a' * V₂ + a' * V₂ * WMid +
                  (WMid * V₂ * a' - WMid * a' * V₂ - V₂ * a' * WMid + a' * WMid * V₂ +
                  (WRestSept * WRestSept * a' - WRestSept * a' * WRestSept -
                   WRestSept * a' * WRestSept + a' * WRestSept * WRestSept))) := by abel
  rw [habs_eq]
  -- Now goal Q part matches hQ_sum / hQ_final form.
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ 225000 * s ^ 7 + 6004167 * s ^ 7 := add_le_add hL_final hQ_final
    _ = 6229167 * s ^ 7 := by ring
    _ ≤ 7000000 * s ^ 7 := by nlinarith [hs7_nn]

/-! ### T2-F7e Phase E.2 step 3: R_T6_sept algebraic decomposition

The second residual `R_T6_sept = T₆ - ΔC₄_lin(V₂) - T6_d6_op`
(from `group_CD_eq_three_residuals` above) decomposes structurally as a sum
of L-form (linear-in-W) and Q-form (quadratic-in-W) operator pieces:

```
R_T6_sept = (1/24) · L_C4(a'+b, WHigh4, a') + (1/24) · Q_residual4
```

where:
- `WHigh4 := V₄ + V₅ + V₆ + R₁_sept` (deg-4+ part of W after V₂, V₃ extracted)
- `WRest6 := V₃ + V₄ + V₅ + V₆ + R₁_sept` (deg-3+ part of W after V₂ extracted)
- `Q_residual4 := Q_C4(WRest6, a') + Q_bilin(V₂, WRest6, a')`
  collects the deg-7+ cross terms from the bilinear expansion of Q_C4(W, a')
  with W = V₂+WRest6 (since Q_C4(V₂+WRest6, a') = Q_C4(V₂, a') + Q_C4(WRest6, a')
  + Q_bilin(V₂, WRest6, a'); the Q_C4(V₂, a') diagonal piece is the deg-6
  ΔC₄_quad(V₂) term subtracted into T6_d6_op).

The L_C4 and Q_C4 templates match `bch_quartic_term_LQ_decomp` (`Basic.lean`).
The proof uses LQ_decomp at x = a'+b, W = V₂+V₃+V₄+V₅+V₆+R₁_sept (= z - (a'+b)
by R₁_sept's def), then `match_scalars <;> ring` closes the polynomial identity.

The cancellation of the deg-5 leading op ΔC₄_lin(V₂) and the deg-6 leading
ops ΔC₄_lin(V₃) + ΔC₄_quad(V₂) fires automatically via the polynomial reduction. -/

set_option maxHeartbeats 128000000 in
private theorem R_T6_sept_decomp_eq
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let V₄ : 𝔸 := bch_quartic_term 𝕂 a' b
    let V₅ : 𝔸 := bch_quintic_term 𝕂 a' b
    let V₆ : 𝔸 := bch_sextic_term 𝕂 a' b
    let R₁_sept : 𝔸 := z - (a' + b) - V₂ - V₃ - V₄ - V₅ - V₆
    let WHigh4 : 𝔸 := V₄ + V₅ + V₆ + R₁_sept
    let WRest6 : 𝔸 := V₃ + V₄ + V₅ + V₆ + R₁_sept
    let x : 𝔸 := a' + b
    -- LHS: R_T6_sept = T₆ - ΔC₄_lin(V₂) - T6_d6_op
    ((bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') -
     -- ΔC₄_lin(V₂, x, a')
     ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) -
                                (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) -
                                (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) * a')) -
     -- T6_d6_op = ΔC₄_lin(V₃) + ΔC₄_quad(V₂)
     ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) -
                                (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) -
                                (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) -
                                (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) * a')))
    =
    -- RHS: (24)⁻¹·L_C4(x, WHigh4, a') + (24)⁻¹·(Q_C4(WRest6, a') + Q_bilin(V₂, WRest6, a'))
    -- L_C4 template (12 sub-terms with multiplicities ±1).
    (24 : 𝕂)⁻¹ • (
      x * WHigh4 * a' * a' + WHigh4 * x * a' * a' -
      x * a' * WHigh4 * a' - x * a' * WHigh4 * a' -
      WHigh4 * a' * x * a' - WHigh4 * a' * x * a' +
      a' * WHigh4 * a' * x + a' * WHigh4 * a' * x +
      a' * x * a' * WHigh4 + a' * x * a' * WHigh4 -
      a' * a' * x * WHigh4 - a' * a' * WHigh4 * x) +
    -- Q_residual4 = Q_C4(WRest6, a') + Q_bilin(V₂, WRest6, a') (6 + 12 = 18 sub-terms).
    (24 : 𝕂)⁻¹ • (
      -- Q_C4(WRest6, a'): WRest6²·a'·a' - 2·WRest6·a'·WRest6·a' + 2·a'·WRest6·a'·WRest6 - a'·a'·WRest6²
      WRest6 * WRest6 * a' * a' -
      WRest6 * a' * WRest6 * a' - WRest6 * a' * WRest6 * a' +
      a' * WRest6 * a' * WRest6 + a' * WRest6 * a' * WRest6 -
      a' * a' * WRest6 * WRest6 +
      -- Q_bilin(V₂, WRest6, a'): bilinear cross terms; same shape as L_C4 template
      -- (with X=V₂, W=WRest6, Y=a') so a single norm helper covers both.
      V₂ * WRest6 * a' * a' + WRest6 * V₂ * a' * a' -
      V₂ * a' * WRest6 * a' - V₂ * a' * WRest6 * a' -
      WRest6 * a' * V₂ * a' - WRest6 * a' * V₂ * a' +
      a' * WRest6 * a' * V₂ + a' * WRest6 * a' * V₂ +
      a' * V₂ * a' * WRest6 + a' * V₂ * a' * WRest6 -
      a' * a' * V₂ * WRest6 - a' * a' * WRest6 * V₂) := by
  intro a' z V₂ V₃ V₄ V₅ V₆ R₁_sept WHigh4 WRest6 x
  -- Step 1: z = (a'+b) + (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) by R₁_sept's def.
  have hz_W : z = (a' + b) + (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) := by
    show z = _
    rw [show R₁_sept = z - (a' + b) - V₂ - V₃ - V₄ - V₅ - V₆ from rfl]
    abel
  -- Step 2: Apply bch_quartic_term_LQ_decomp at x = a'+b, W = V₂+V₃+V₄+V₅+V₆+R₁_sept, y = a'.
  have hLQ := bch_quartic_term_LQ_decomp (𝕂 := 𝕂) (a' + b)
              (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) a'
  rw [show ((a' + b) + (V₂ + V₃ + V₄ + V₅ + V₆ + R₁_sept) : 𝔸) = z from hz_W.symm] at hLQ
  -- Substitute hLQ to replace bch_quartic_term diff in the goal.
  rw [hLQ]
  -- Step 3: Goal is polynomial. Unfold V₂, x, a', WHigh4, WRest6 (keep V₃, V₄, V₅, V₆, R₁_sept atomic).
  show _ = _
  simp only [show V₂ = ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) from rfl,
             show x = ((2 : 𝕂)⁻¹ • a + b : 𝔸) from rfl,
             show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl,
             show WHigh4 = V₄ + V₅ + V₆ + R₁_sept from rfl,
             show WRest6 = V₃ + V₄ + V₅ + V₆ + R₁_sept from rfl]
  -- Distribute smul/mul/add throughout.
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]
  -- Close via match_scalars + ring.
  match_scalars <;> ring

/-! ### T2-F7e Phase E.2 step 3b: norm bound on R_T6_sept

Uses `R_T6_sept_decomp_eq` to express R_T6_sept = (24)⁻¹·L_C4 + (24)⁻¹·Q_residual4,
then bounds each piece by triangle inequality. -/

-- 12-term L_C4-shape sum bound: each monomial has 1 X, 1 W, 2 Y's, bounded by ‖X‖·‖W‖·‖Y‖²
-- via `norm_quad_le_aux`. Applies to both L_C4 (with X = a'+b, W = WHigh4, Y = a') and
-- Q_bilin (with X = V₂, W = WRest6, Y = a').
private lemma norm_LC4_template_le {𝔸 : Type*} [NormedRing 𝔸] (X W Y : 𝔸) :
    ‖X * W * Y * Y + W * X * Y * Y -
     X * Y * W * Y - X * Y * W * Y -
     W * Y * X * Y - W * Y * X * Y +
     Y * W * Y * X + Y * W * Y * X +
     Y * X * Y * W + Y * X * Y * W -
     Y * Y * X * W - Y * Y * W * X‖ ≤
      12 * (‖X‖ * ‖W‖ * ‖Y‖ ^ 2) := by
  set K := ‖X‖ * ‖W‖ * ‖Y‖ ^ 2 with hK_def
  have hY_sq : ‖Y‖ ^ 2 = ‖Y‖ * ‖Y‖ := sq ‖Y‖
  -- 8 distinct monomial bounds, each ≤ K
  have b1 : ‖X * W * Y * Y‖ ≤ K := by
    calc ‖X * W * Y * Y‖ ≤ ‖X‖ * ‖W‖ * ‖Y‖ * ‖Y‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  have b2 : ‖W * X * Y * Y‖ ≤ K := by
    calc ‖W * X * Y * Y‖ ≤ ‖W‖ * ‖X‖ * ‖Y‖ * ‖Y‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  have b3 : ‖X * Y * W * Y‖ ≤ K := by
    calc ‖X * Y * W * Y‖ ≤ ‖X‖ * ‖Y‖ * ‖W‖ * ‖Y‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  have b4 : ‖W * Y * X * Y‖ ≤ K := by
    calc ‖W * Y * X * Y‖ ≤ ‖W‖ * ‖Y‖ * ‖X‖ * ‖Y‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  have b5 : ‖Y * W * Y * X‖ ≤ K := by
    calc ‖Y * W * Y * X‖ ≤ ‖Y‖ * ‖W‖ * ‖Y‖ * ‖X‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  have b6 : ‖Y * X * Y * W‖ ≤ K := by
    calc ‖Y * X * Y * W‖ ≤ ‖Y‖ * ‖X‖ * ‖Y‖ * ‖W‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  have b7 : ‖Y * Y * X * W‖ ≤ K := by
    calc ‖Y * Y * X * W‖ ≤ ‖Y‖ * ‖Y‖ * ‖X‖ * ‖W‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  have b8 : ‖Y * Y * W * X‖ ≤ K := by
    calc ‖Y * Y * W * X‖ ≤ ‖Y‖ * ‖Y‖ * ‖W‖ * ‖X‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hY_sq]; ring
  -- Re-group as plus-of-negs.
  have hreorg :
      X * W * Y * Y + W * X * Y * Y -
      X * Y * W * Y - X * Y * W * Y -
      W * Y * X * Y - W * Y * X * Y +
      Y * W * Y * X + Y * W * Y * X +
      Y * X * Y * W + Y * X * Y * W -
      Y * Y * X * W - Y * Y * W * X =
      X * W * Y * Y + W * X * Y * Y +
      (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
      (-(W * Y * X * Y)) + (-(W * Y * X * Y)) +
      Y * W * Y * X + Y * W * Y * X +
      Y * X * Y * W + Y * X * Y * W +
      (-(Y * Y * X * W)) + (-(Y * Y * W * X)) := by abel
  rw [hreorg]
  -- 11 norm_add_le steps.
  have h11 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
     (-(W * Y * X * Y)) + (-(W * Y * X * Y)) +
     Y * W * Y * X + Y * W * Y * X +
     Y * X * Y * W + Y * X * Y * W +
     (-(Y * Y * X * W))) (-(Y * Y * W * X))
  have h10 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
     (-(W * Y * X * Y)) + (-(W * Y * X * Y)) +
     Y * W * Y * X + Y * W * Y * X +
     Y * X * Y * W + Y * X * Y * W) (-(Y * Y * X * W))
  have h9 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
     (-(W * Y * X * Y)) + (-(W * Y * X * Y)) +
     Y * W * Y * X + Y * W * Y * X +
     Y * X * Y * W) (Y * X * Y * W)
  have h8 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
     (-(W * Y * X * Y)) + (-(W * Y * X * Y)) +
     Y * W * Y * X + Y * W * Y * X) (Y * X * Y * W)
  have h7 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
     (-(W * Y * X * Y)) + (-(W * Y * X * Y)) +
     Y * W * Y * X) (Y * W * Y * X)
  have h6 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
     (-(W * Y * X * Y)) + (-(W * Y * X * Y))) (Y * W * Y * X)
  have h5 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y)) +
     (-(W * Y * X * Y))) (-(W * Y * X * Y))
  have h4 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y +
     (-(X * Y * W * Y)) + (-(X * Y * W * Y))) (-(W * Y * X * Y))
  have h3 := norm_add_le
    (X * W * Y * Y + W * X * Y * Y + (-(X * Y * W * Y))) (-(X * Y * W * Y))
  have h2 := norm_add_le (X * W * Y * Y + W * X * Y * Y) (-(X * Y * W * Y))
  have h1 := norm_add_le (X * W * Y * Y) (W * X * Y * Y)
  simp only [norm_neg] at h2 h3 h4 h5 h10 h11
  linarith

-- 6-term Q_C4-shape sum bound: each monomial has 2 W's, 2 Y's, bounded by ‖W‖²·‖Y‖²
-- via `norm_quad_le_aux`.
private lemma norm_QC4_template_le {𝔸 : Type*} [NormedRing 𝔸] (W Y : 𝔸) :
    ‖W * W * Y * Y -
     W * Y * W * Y - W * Y * W * Y +
     Y * W * Y * W + Y * W * Y * W -
     Y * Y * W * W‖ ≤
      6 * (‖W‖ ^ 2 * ‖Y‖ ^ 2) := by
  set K := ‖W‖ ^ 2 * ‖Y‖ ^ 2 with hK_def
  have hW_sq : ‖W‖ ^ 2 = ‖W‖ * ‖W‖ := sq ‖W‖
  have hY_sq : ‖Y‖ ^ 2 = ‖Y‖ * ‖Y‖ := sq ‖Y‖
  have b1 : ‖W * W * Y * Y‖ ≤ K := by
    calc ‖W * W * Y * Y‖ ≤ ‖W‖ * ‖W‖ * ‖Y‖ * ‖Y‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hW_sq, hY_sq]; ring
  have b2 : ‖W * Y * W * Y‖ ≤ K := by
    calc ‖W * Y * W * Y‖ ≤ ‖W‖ * ‖Y‖ * ‖W‖ * ‖Y‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hW_sq, hY_sq]; ring
  have b3 : ‖Y * W * Y * W‖ ≤ K := by
    calc ‖Y * W * Y * W‖ ≤ ‖Y‖ * ‖W‖ * ‖Y‖ * ‖W‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hW_sq, hY_sq]; ring
  have b4 : ‖Y * Y * W * W‖ ≤ K := by
    calc ‖Y * Y * W * W‖ ≤ ‖Y‖ * ‖Y‖ * ‖W‖ * ‖W‖ := norm_quad_le_aux _ _ _ _
      _ = K := by rw [hK_def, hW_sq, hY_sq]; ring
  have hreorg :
      W * W * Y * Y -
      W * Y * W * Y - W * Y * W * Y +
      Y * W * Y * W + Y * W * Y * W -
      Y * Y * W * W =
      W * W * Y * Y +
      (-(W * Y * W * Y)) + (-(W * Y * W * Y)) +
      Y * W * Y * W + Y * W * Y * W +
      (-(Y * Y * W * W)) := by abel
  rw [hreorg]
  have h5 := norm_add_le
    (W * W * Y * Y + (-(W * Y * W * Y)) + (-(W * Y * W * Y)) + Y * W * Y * W + Y * W * Y * W)
    (-(Y * Y * W * W))
  have h4 := norm_add_le
    (W * W * Y * Y + (-(W * Y * W * Y)) + (-(W * Y * W * Y)) + Y * W * Y * W) (Y * W * Y * W)
  have h3 := norm_add_le
    (W * W * Y * Y + (-(W * Y * W * Y)) + (-(W * Y * W * Y))) (Y * W * Y * W)
  have h2 := norm_add_le (W * W * Y * Y + (-(W * Y * W * Y))) (-(W * Y * W * Y))
  have h1 := norm_add_le (W * W * Y * Y) (-(W * Y * W * Y))
  simp only [norm_neg] at h1 h2 h3 h5
  linarith

set_option maxHeartbeats 1600000 in
private theorem norm_R_T6_sept_le
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    let V₃ : 𝔸 := bch_cubic_term 𝕂 a' b
    let x : 𝔸 := a' + b
    ‖((bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') -
     ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) -
                                (x * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * x) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) -
                                (V₂ * (x * a' - a' * x) - (x * a' - a' * x) * V₂) * a')) -
     ((0 : 𝔸) - (24 : 𝕂)⁻¹ • (a' * (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) -
                                (x * (V₃ * a' - a' * V₃) - (V₃ * a' - a' * V₃) * x) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) -
                                (V₃ * (x * a' - a' * x) - (x * a' - a' * x) * V₃) * a') -
                (24 : 𝕂)⁻¹ • (a' * (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) -
                                (V₂ * (V₂ * a' - a' * V₂) - (V₂ * a' - a' * V₂) * V₂) * a')))‖
    ≤ 1000000 * (‖a‖ + ‖b‖) ^ 7 := by
  intro a' z V₂ V₃ x
  -- Setup norms (mirrors norm_R_T5_sept_le; no DC_a since (96)⁻¹ doesn't appear here).
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt : s < 1 / 4 := hab
  have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ s / 2 := by
    show ‖(2 : 𝕂)⁻¹ • a‖ ≤ _
    calc ‖(2 : 𝕂)⁻¹ • a‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
      _ ≤ s / 2 := by have := norm_nonneg b; linarith
  have ha'_b_le : ‖a' + b‖ ≤ 3 * s / 2 := by
    calc ‖a' + b‖ ≤ ‖a'‖ + ‖b‖ := norm_add_le _ _
      _ ≤ s / 2 + s := by have := norm_nonneg a; linarith
      _ = 3 * s / 2 := by ring
  have ha'_a : ‖a'‖ ≤ ‖a‖ := by
    show ‖(2 : 𝕂)⁻¹ • a‖ ≤ _
    calc ‖(2 : 𝕂)⁻¹ • a‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
      _ ≤ ‖a‖ := by linarith [norm_nonneg a]
  have hs1_le : ‖a'‖ + ‖b‖ ≤ s := by linarith [ha'_a]
  have hs1_nn : (0 : ℝ) ≤ ‖a'‖ + ‖b‖ := by positivity
  -- ‖V₂‖ ≤ s²/2.
  have hV2_le : ‖V₂‖ ≤ s ^ 2 / 2 := by
    show ‖(2 : 𝕂)⁻¹ • (a' * b - b * a')‖ ≤ _
    have hcomm : ‖a' * b - b * a'‖ ≤ 2 * ‖a'‖ * ‖b‖ := by
      calc ‖a' * b - b * a'‖ ≤ ‖a' * b‖ + ‖b * a'‖ := by
            rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖a'‖ * ‖b‖ + ‖b‖ * ‖a'‖ := by gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖a'‖ * ‖b‖ := by ring
    calc ‖(2 : 𝕂)⁻¹ • (a' * b - b * a')‖
        ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a' * b - b * a'‖ := norm_smul_le _ _
      _ = (2 : ℝ)⁻¹ * ‖a' * b - b * a'‖ := by rw [h_half_norm]
      _ ≤ (2 : ℝ)⁻¹ * (2 * ‖a'‖ * ‖b‖) := by
          apply mul_le_mul_of_nonneg_left hcomm (by norm_num)
      _ = ‖a'‖ * ‖b‖ := by ring
      _ ≤ (s / 2) * s := by
          apply mul_le_mul ha'_le _ (norm_nonneg _) (by linarith)
          have := norm_nonneg a; linarith
      _ = s ^ 2 / 2 := by ring
  -- ‖V₃‖ ≤ s³, and V₄ V₅ V₆ R₁_sept norms.
  have hV3_le : ‖V₃‖ ≤ s ^ 3 := by
    show ‖bch_cubic_term 𝕂 a' b‖ ≤ _
    calc ‖bch_cubic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 3 := norm_bch_cubic_term_le a' b
      _ ≤ s ^ 3 := pow_le_pow_left₀ hs1_nn hs1_le 3
  have hV4_le_explicit : ‖bch_quartic_term 𝕂 a' b‖ ≤ s ^ 4 := by
    calc ‖bch_quartic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 4 := norm_bch_quartic_term_le a' b
      _ ≤ s ^ 4 := pow_le_pow_left₀ hs1_nn hs1_le 4
  have hV5_le_explicit : ‖bch_quintic_term 𝕂 a' b‖ ≤ s ^ 5 := by
    calc ‖bch_quintic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 5 := norm_bch_quintic_term_le a' b
      _ ≤ s ^ 5 := pow_le_pow_left₀ hs1_nn hs1_le 5
  have hV6_le_explicit : ‖bch_sextic_term 𝕂 a' b‖ ≤ s ^ 6 := by
    calc ‖bch_sextic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 6 := norm_bch_sextic_term_le a' b
      _ ≤ s ^ 6 := pow_le_pow_left₀ hs1_nn hs1_le 6
  have hR1_le_explicit : ‖z - (a' + b) - V₂ - V₃ - bch_quartic_term 𝕂 a' b -
                  bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b‖ ≤
                1500000 * s ^ 7 :=
    norm_bch_inner_septic_remainder_le (𝕂 := 𝕂) a b hab
  -- Apply algebraic decomposition.
  rw [R_T6_sept_decomp_eq (𝕂 := 𝕂) a b]
  -- Goal: ‖(24)⁻¹·L_C4 + (24)⁻¹·(Q_C4(WRest6,a') + Q_bilin(V₂,WRest6,a'))‖ ≤ 10⁶·s⁷
  set V₄ : 𝔸 := bch_quartic_term 𝕂 a' b with hV4_def
  set V₅ : 𝔸 := bch_quintic_term 𝕂 a' b with hV5_def
  set V₆ : 𝔸 := bch_sextic_term 𝕂 a' b with hV6_def
  set R₁_sept : 𝔸 := z - (a' + b) - V₂ - V₃ - V₄ - V₅ - V₆ with hR1_def
  set WHigh4 : 𝔸 := V₄ + V₅ + V₆ + R₁_sept with hWHigh4_def
  set WRest6 : 𝔸 := V₃ + V₄ + V₅ + V₆ + R₁_sept with hWRest6_def
  have hV4_le : ‖V₄‖ ≤ s ^ 4 := hV4_le_explicit
  have hV5_le : ‖V₅‖ ≤ s ^ 5 := hV5_le_explicit
  have hV6_le : ‖V₆‖ ≤ s ^ 6 := hV6_le_explicit
  have hR1_le : ‖R₁_sept‖ ≤ 1500000 * s ^ 7 := by rw [hR1_def]; exact hR1_le_explicit
  -- Pow bounds for s ≤ 1/4.
  have hs2_le : s ^ 2 ≤ 1 / 16 := by nlinarith [hs_lt, hs_nn]
  have hs3_le : s ^ 3 ≤ 1 / 64 := by nlinarith [hs_lt, hs_nn, sq_nonneg s]
  have hs4_le : s ^ 4 ≤ 1 / 256 := by nlinarith [hs2_le, sq_nonneg (s ^ 2)]
  have hs3_nn : (0 : ℝ) ≤ s ^ 3 := pow_nonneg hs_nn 3
  have hs4_nn : (0 : ℝ) ≤ s ^ 4 := pow_nonneg hs_nn 4
  have hs5_nn : (0 : ℝ) ≤ s ^ 5 := pow_nonneg hs_nn 5
  have hs6_le_s5 : s ^ 6 ≤ s ^ 5 * (1 / 4) := by
    have heq : s ^ 6 = s * s ^ 5 := by ring
    rw [heq]; nlinarith [hs5_nn, hs_lt, hs_nn]
  have hs7_le_s5 : s ^ 7 ≤ s ^ 5 * (1 / 16) := by
    have heq : s ^ 7 = s ^ 2 * s ^ 5 := by ring
    rw [heq]; nlinarith [hs5_nn, hs2_le]
  have hs5_le_s4 : s ^ 5 ≤ s ^ 4 * (1 / 4) := by
    have heq : s ^ 5 = s * s ^ 4 := by ring
    rw [heq]; nlinarith [hs4_nn, hs_lt, hs_nn]
  have hs6_le_s4 : s ^ 6 ≤ s ^ 4 * (1 / 16) := by
    have heq : s ^ 6 = s ^ 2 * s ^ 4 := by ring
    rw [heq]; nlinarith [hs4_nn, hs2_le]
  have hs7_le_s4 : s ^ 7 ≤ s ^ 4 * (1 / 64) := by
    have heq : s ^ 7 = s ^ 3 * s ^ 4 := by ring
    rw [heq]; nlinarith [hs4_nn, hs3_le]
  have hs4_le_s3 : s ^ 4 ≤ s ^ 3 * (1 / 4) := by
    have heq : s ^ 4 = s * s ^ 3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs_lt, hs_nn]
  have hs5_le_s3 : s ^ 5 ≤ s ^ 3 * (1 / 16) := by
    have heq : s ^ 5 = s ^ 2 * s ^ 3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs2_le]
  have hs6_le_s3 : s ^ 6 ≤ s ^ 3 * (1 / 64) := by
    have heq : s ^ 6 = s ^ 3 * s ^ 3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs3_le]
  have hs7_le_s3 : s ^ 7 ≤ s ^ 3 * (1 / 256) := by
    have heq : s ^ 7 = s ^ 4 * s ^ 3 := by ring
    rw [heq]; nlinarith [hs3_nn, hs4_le]
  have hs8_le_s7 : s ^ 8 ≤ s ^ 7 * (1 / 4) := by
    have heq : s ^ 8 = s * s ^ 7 := by ring
    rw [heq]; nlinarith [hs7_nn, hs_lt, hs_nn]
  -- ‖WHigh4‖ ≤ 25000·s⁴ (deg-4+ part).
  have hWHigh4_le : ‖WHigh4‖ ≤ 25000 * s ^ 4 := by
    have hsum : ‖WHigh4‖ ≤ ‖V₄‖ + ‖V₅‖ + ‖V₆‖ + ‖R₁_sept‖ := by
      rw [hWHigh4_def]
      have h1 := norm_add_le (V₄ + V₅ + V₆) R₁_sept
      have h2 := norm_add_le (V₄ + V₅) V₆
      have h3 := norm_add_le V₄ V₅
      linarith
    linarith
  -- ‖WRest6‖ ≤ 6000·s³ (deg-3+ part).
  have hWRest6_le : ‖WRest6‖ ≤ 6000 * s ^ 3 := by
    have hsum : ‖WRest6‖ ≤ ‖V₃‖ + ‖V₄‖ + ‖V₅‖ + ‖V₆‖ + ‖R₁_sept‖ := by
      rw [hWRest6_def]
      have h1 := norm_add_le (V₃ + V₄ + V₅ + V₆) R₁_sept
      have h2 := norm_add_le (V₃ + V₄ + V₅) V₆
      have h3 := norm_add_le (V₃ + V₄) V₅
      have h4 := norm_add_le V₃ V₄
      linarith
    linarith
  have h24_inv : ‖(24 : 𝕂)⁻¹‖ = (24 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- L_C4 part: 12 terms × ‖x‖·‖WHigh4‖·‖a'‖² each, via norm_LC4_template_le.
  have hL_norm : ‖(a' + b) * WHigh4 * a' * a' + WHigh4 * (a' + b) * a' * a' -
                  (a' + b) * a' * WHigh4 * a' - (a' + b) * a' * WHigh4 * a' -
                  WHigh4 * a' * (a' + b) * a' - WHigh4 * a' * (a' + b) * a' +
                  a' * WHigh4 * a' * (a' + b) + a' * WHigh4 * a' * (a' + b) +
                  a' * (a' + b) * a' * WHigh4 + a' * (a' + b) * a' * WHigh4 -
                  a' * a' * (a' + b) * WHigh4 - a' * a' * WHigh4 * (a' + b)‖ ≤
                 12 * (‖a' + b‖ * ‖WHigh4‖ * ‖a'‖ ^ 2) :=
    norm_LC4_template_le (a' + b) WHigh4 a'
  -- Convert L_C4 sum bound to s⁷.
  have hL_s7 : 12 * (‖a' + b‖ * ‖WHigh4‖ * ‖a'‖ ^ 2) ≤ 200000 * s ^ 7 := by
    have ha'_sq_le : ‖a'‖ ^ 2 ≤ (s / 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ha'_le 2
    have h1 : ‖a' + b‖ * ‖WHigh4‖ * ‖a'‖ ^ 2 ≤ (3 * s / 2) * (25000 * s ^ 4) * ((s / 2) ^ 2) := by
      apply mul_le_mul _ ha'_sq_le (sq_nonneg _) (by positivity)
      apply mul_le_mul ha'_b_le hWHigh4_le (norm_nonneg _) (by linarith)
    calc 12 * (‖a' + b‖ * ‖WHigh4‖ * ‖a'‖ ^ 2)
        ≤ 12 * ((3 * s / 2) * (25000 * s ^ 4) * ((s / 2) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 112500 * s ^ 7 := by ring
      _ ≤ 200000 * s ^ 7 := by nlinarith [hs7_nn]
  have hL_final : ‖(24 : 𝕂)⁻¹ • ((a' + b) * WHigh4 * a' * a' + WHigh4 * (a' + b) * a' * a' -
                  (a' + b) * a' * WHigh4 * a' - (a' + b) * a' * WHigh4 * a' -
                  WHigh4 * a' * (a' + b) * a' - WHigh4 * a' * (a' + b) * a' +
                  a' * WHigh4 * a' * (a' + b) + a' * WHigh4 * a' * (a' + b) +
                  a' * (a' + b) * a' * WHigh4 + a' * (a' + b) * a' * WHigh4 -
                  a' * a' * (a' + b) * WHigh4 - a' * a' * WHigh4 * (a' + b))‖ ≤
                 10000 * s ^ 7 := by
    calc _ ≤ ‖(24 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
      _ = (24 : ℝ)⁻¹ * _ := by rw [h24_inv]
      _ ≤ (24 : ℝ)⁻¹ * (12 * (‖a' + b‖ * ‖WHigh4‖ * ‖a'‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hL_norm (by norm_num)
      _ ≤ (24 : ℝ)⁻¹ * (200000 * s ^ 7) := by
          apply mul_le_mul_of_nonneg_left hL_s7 (by norm_num)
      _ ≤ 10000 * s ^ 7 := by linarith [hs7_nn]
  -- Q_C4(WRest6, a') part: 6 terms × ‖WRest6‖²·‖a'‖² each, via norm_QC4_template_le.
  have hQC4_norm : ‖WRest6 * WRest6 * a' * a' -
                    WRest6 * a' * WRest6 * a' - WRest6 * a' * WRest6 * a' +
                    a' * WRest6 * a' * WRest6 + a' * WRest6 * a' * WRest6 -
                    a' * a' * WRest6 * WRest6‖ ≤
                   6 * (‖WRest6‖ ^ 2 * ‖a'‖ ^ 2) :=
    norm_QC4_template_le WRest6 a'
  have hQC4_s7 : 6 * (‖WRest6‖ ^ 2 * ‖a'‖ ^ 2) ≤ 14000000 * s ^ 7 := by
    have hWR_nn : (0 : ℝ) ≤ ‖WRest6‖ := norm_nonneg _
    have ha'_nn : (0 : ℝ) ≤ ‖a'‖ := norm_nonneg _
    have ha'_sq_le : ‖a'‖ ^ 2 ≤ (s / 2) ^ 2 :=
      pow_le_pow_left₀ ha'_nn ha'_le 2
    have hWR_sq_le : ‖WRest6‖ ^ 2 ≤ (6000 * s ^ 3) ^ 2 :=
      pow_le_pow_left₀ hWR_nn hWRest6_le 2
    have h1 : ‖WRest6‖ ^ 2 * ‖a'‖ ^ 2 ≤ (6000 * s ^ 3) ^ 2 * ((s / 2) ^ 2) :=
      mul_le_mul hWR_sq_le ha'_sq_le (sq_nonneg _) (by positivity)
    calc 6 * (‖WRest6‖ ^ 2 * ‖a'‖ ^ 2)
        ≤ 6 * ((6000 * s ^ 3) ^ 2 * ((s / 2) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 54000000 * s ^ 8 := by ring
      _ ≤ 54000000 * (s ^ 7 * (1 / 4)) := by
          apply mul_le_mul_of_nonneg_left hs8_le_s7 (by norm_num)
      _ = 13500000 * s ^ 7 := by ring
      _ ≤ 14000000 * s ^ 7 := by nlinarith [hs7_nn]
  -- Q_bilin(V₂, WRest6, a') part: 12 terms × ‖V₂‖·‖WRest6‖·‖a'‖² each, via norm_LC4_template_le.
  have hQbilin_norm : ‖V₂ * WRest6 * a' * a' + WRest6 * V₂ * a' * a' -
                       V₂ * a' * WRest6 * a' - V₂ * a' * WRest6 * a' -
                       WRest6 * a' * V₂ * a' - WRest6 * a' * V₂ * a' +
                       a' * WRest6 * a' * V₂ + a' * WRest6 * a' * V₂ +
                       a' * V₂ * a' * WRest6 + a' * V₂ * a' * WRest6 -
                       a' * a' * V₂ * WRest6 - a' * a' * WRest6 * V₂‖ ≤
                      12 * (‖V₂‖ * ‖WRest6‖ * ‖a'‖ ^ 2) :=
    norm_LC4_template_le V₂ WRest6 a'
  have hQbilin_s7 : 12 * (‖V₂‖ * ‖WRest6‖ * ‖a'‖ ^ 2) ≤ 10000 * s ^ 7 := by
    have ha'_sq_le : ‖a'‖ ^ 2 ≤ (s / 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ha'_le 2
    have h1 : ‖V₂‖ * ‖WRest6‖ * ‖a'‖ ^ 2 ≤ (s ^ 2 / 2) * (6000 * s ^ 3) * ((s / 2) ^ 2) := by
      apply mul_le_mul _ ha'_sq_le (sq_nonneg _) (by positivity)
      apply mul_le_mul hV2_le hWRest6_le (norm_nonneg _) (by positivity)
    calc 12 * (‖V₂‖ * ‖WRest6‖ * ‖a'‖ ^ 2)
        ≤ 12 * ((s ^ 2 / 2) * (6000 * s ^ 3) * ((s / 2) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 9000 * s ^ 7 := by ring
      _ ≤ 10000 * s ^ 7 := by nlinarith [hs7_nn]
  -- Combined Q part = Q_C4 + Q_bilin (sum of 18 terms inside one (24)⁻¹ smul).
  -- Bound: ‖Q_C4 + Q_bilin‖ ≤ ‖Q_C4‖ + ‖Q_bilin‖ ≤ 14·10⁶·s⁷ + 10⁴·s⁷.
  have hQ_norm : ‖(WRest6 * WRest6 * a' * a' -
                   WRest6 * a' * WRest6 * a' - WRest6 * a' * WRest6 * a' +
                   a' * WRest6 * a' * WRest6 + a' * WRest6 * a' * WRest6 -
                   a' * a' * WRest6 * WRest6) +
                  (V₂ * WRest6 * a' * a' + WRest6 * V₂ * a' * a' -
                   V₂ * a' * WRest6 * a' - V₂ * a' * WRest6 * a' -
                   WRest6 * a' * V₂ * a' - WRest6 * a' * V₂ * a' +
                   a' * WRest6 * a' * V₂ + a' * WRest6 * a' * V₂ +
                   a' * V₂ * a' * WRest6 + a' * V₂ * a' * WRest6 -
                   a' * a' * V₂ * WRest6 - a' * a' * WRest6 * V₂)‖ ≤
                 14010000 * s ^ 7 := by
    calc _ ≤ _ + _ := norm_add_le _ _
      _ ≤ 6 * (‖WRest6‖ ^ 2 * ‖a'‖ ^ 2) + 12 * (‖V₂‖ * ‖WRest6‖ * ‖a'‖ ^ 2) :=
          add_le_add hQC4_norm hQbilin_norm
      _ ≤ 14000000 * s ^ 7 + 10000 * s ^ 7 := add_le_add hQC4_s7 hQbilin_s7
      _ = 14010000 * s ^ 7 := by ring
  have hQ_final : ‖(24 : 𝕂)⁻¹ • ((WRest6 * WRest6 * a' * a' -
                   WRest6 * a' * WRest6 * a' - WRest6 * a' * WRest6 * a' +
                   a' * WRest6 * a' * WRest6 + a' * WRest6 * a' * WRest6 -
                   a' * a' * WRest6 * WRest6) +
                  (V₂ * WRest6 * a' * a' + WRest6 * V₂ * a' * a' -
                   V₂ * a' * WRest6 * a' - V₂ * a' * WRest6 * a' -
                   WRest6 * a' * V₂ * a' - WRest6 * a' * V₂ * a' +
                   a' * WRest6 * a' * V₂ + a' * WRest6 * a' * V₂ +
                   a' * V₂ * a' * WRest6 + a' * V₂ * a' * WRest6 -
                   a' * a' * V₂ * WRest6 - a' * a' * WRest6 * V₂))‖ ≤
                 600000 * s ^ 7 := by
    calc _ ≤ ‖(24 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
      _ = (24 : ℝ)⁻¹ * _ := by rw [h24_inv]
      _ ≤ (24 : ℝ)⁻¹ * (14010000 * s ^ 7) := by
          apply mul_le_mul_of_nonneg_left hQ_norm (by norm_num)
      _ ≤ 600000 * s ^ 7 := by linarith [hs7_nn]
  -- Re-associate the goal's Q part to match hQ_final's "+" form.
  have habs_eq : ((WRest6 * WRest6 * a' * a' -
                  WRest6 * a' * WRest6 * a' - WRest6 * a' * WRest6 * a' +
                  a' * WRest6 * a' * WRest6 + a' * WRest6 * a' * WRest6 -
                  a' * a' * WRest6 * WRest6 +
                  V₂ * WRest6 * a' * a' + WRest6 * V₂ * a' * a' -
                  V₂ * a' * WRest6 * a' - V₂ * a' * WRest6 * a' -
                  WRest6 * a' * V₂ * a' - WRest6 * a' * V₂ * a' +
                  a' * WRest6 * a' * V₂ + a' * WRest6 * a' * V₂ +
                  a' * V₂ * a' * WRest6 + a' * V₂ * a' * WRest6 -
                  a' * a' * V₂ * WRest6 - a' * a' * WRest6 * V₂) : 𝔸) =
                 ((WRest6 * WRest6 * a' * a' -
                   WRest6 * a' * WRest6 * a' - WRest6 * a' * WRest6 * a' +
                   a' * WRest6 * a' * WRest6 + a' * WRest6 * a' * WRest6 -
                   a' * a' * WRest6 * WRest6) +
                  (V₂ * WRest6 * a' * a' + WRest6 * V₂ * a' * a' -
                   V₂ * a' * WRest6 * a' - V₂ * a' * WRest6 * a' -
                   WRest6 * a' * V₂ * a' - WRest6 * a' * V₂ * a' +
                   a' * WRest6 * a' * V₂ + a' * WRest6 * a' * V₂ +
                   a' * V₂ * a' * WRest6 + a' * V₂ * a' * WRest6 -
                   a' * a' * V₂ * WRest6 - a' * a' * WRest6 * V₂)) := by abel
  rw [habs_eq]
  -- Final triangle: ‖L + Q‖ ≤ ‖L‖ + ‖Q‖ ≤ 10⁴·s⁷ + 6·10⁵·s⁷ = 6.1·10⁵·s⁷ ≤ 10⁶·s⁷.
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ 10000 * s ^ 7 + 600000 * s ^ 7 := add_le_add hL_final hQ_final
    _ = 610000 * s ^ 7 := by ring
    _ ≤ 1000000 * s ^ 7 := by nlinarith [hs7_nn]

/-! ### T2-F7e Phase E.2 step 4: norm bound on C5_diff_residual (partial)

The third residual `C5_diff_residual = (C₅(z,a') - C₅(a'+b,a')) - ΔC₅_lin_explicit`
captures the deg-7+ remainder of the C₅ Taylor expansion in V₂ after subtracting
the explicit deg-6 (linear-in-V₂) leading polynomial.

**Status (partial discharge)**: The algebraic foundation
(`C5_LinResidual_at_V2_eq_polynomial`) is proven, identifying the V₂-Taylor
residual at `z₁ = (a'+b)+V₂` with an explicit deg-7+ polynomial in (a, b).
The full discharge (axiom replacement) is pending the norm bound on this
polynomial — see the section comment below for details. -/

/- ## C5_diff_residual: algebraic foundation (proved) + norm bound (axiom).

The bound `‖C5_diff_residual‖ ≤ 5·10⁶·s⁷` is decomposed as `LipPiece + LinResidual`:

- **LipPiece** = `C₅(z, a') - C₅((a'+b)+V₂, a')`. Bounded directly by
  `BCH.norm_bch_quintic_term_diff_le` with `‖z - ((a'+b)+V₂)‖ = ‖WRest6‖ ≤ 6000·s³`.
  M = ‖z‖+‖(a'+b)+V₂‖+‖a'‖ ≤ 5s, so M⁴·6000·s³ ≤ 4·10⁶·s⁷.

- **LinResidual** = `(C₅((a'+b)+V₂, a') - C₅(a'+b, a')) - ΔC₅_lin_explicit`.
  Equals the explicit deg-7+ polynomial `C5_LinResidual_polynomial 𝕂 a b`
  (CAS-verified at `scripts/compute_C5_diff_LinResidual.py`), as proved by
  `C5_LinResidual_at_V2_eq_polynomial` below.
  Norm bound: ‖C5_LinResidual_polynomial 𝕂 a b‖ ≤ K·s⁷ where K = Σ|coef| ≈ 0.027.

**Status (session 23, fully closed)**:
- ✅ `C5_LinResidual_polynomial` def (205 explicit deg-7+ monomials, denoms in
  {92160, 184320, 368640}).
- ✅ `C5_LinResidual_at_V2_eq_polynomial` algebraic identity (proved via
  `match_scalars + ring`, using 1024M heartbeats).
- ✅ `norm_C5_LinResidual_polynomial_le` (proved theorem; the 205-term triangle
  inequality discharged via the per-degree Finset.sum refactor below).
- ✅ Main theorem `symmetric_bch_quintic_C5_diff_residual_le` (proved theorem;
  combines algebraic identity + LinResidual bound + LipPiece bound).

The algebraic identity is the **core technical contribution** for the discharge —
it isolates the deg-6 cancellation between the linearization of C₅ and
ΔC₅_lin_explicit, leaving only deg-7+ residuals that are easy to bound.

The polynomial-norm bound is discharged via a Finset.sum refactor:
per-degree `linResTerm{7,8,9}` / `linResBound{7,8,9}` functions on `Fin {79,78,48}`,
uniform per-i bound (max coefficient per degree) + `Finset.sum_const`, combined
through triangle inequality. Total ≈ 0.10·s⁷ ≪ 1·s⁷.
-/

-- Explicit deg-7+ polynomial form of LinResidual (CAS-verified, 205 monomials).
-- Common denominator 368640. Used in `LinResidual_eq_polynomial` below.
private noncomputable def C5_LinResidual_polynomial
    (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
    -- Degree 7 (79 terms):
    (-7 / 92160 : 𝕂) • (a * a * a * a * b * a * b) +
    (7 / 92160 : 𝕂) • (a * a * a * a * b * b * a) +
    (30 / 92160 : 𝕂) • (a * a * a * b * a * a * b) +
    (-32 / 92160 : 𝕂) • (a * a * a * b * a * b * a) +
    (14 / 92160 : 𝕂) • (a * a * a * b * a * b * b) +
    (2 / 92160 : 𝕂) • (a * a * a * b * b * a * a) +
    (-14 / 92160 : 𝕂) • (a * a * a * b * b * b * a) +
    (-50 / 92160 : 𝕂) • (a * a * b * a * a * a * b) +
    (60 / 92160 : 𝕂) • (a * a * b * a * a * b * a) +
    (-40 / 92160 : 𝕂) • (a * a * b * a * a * b * b) +
    (-12 / 92160 : 𝕂) • (a * a * b * a * b * a * a) +
    (8 / 92160 : 𝕂) • (a * a * b * a * b * a * b) +
    (30 / 92160 : 𝕂) • (a * a * b * a * b * b * a) +
    (-4 / 92160 : 𝕂) • (a * a * b * a * b * b * b) +
    (2 / 92160 : 𝕂) • (a * a * b * b * a * a * a) +
    (-14 / 92160 : 𝕂) • (a * a * b * b * a * a * b) +
    (20 / 92160 : 𝕂) • (a * a * b * b * a * b * a) +
    (-4 / 92160 : 𝕂) • (a * a * b * b * b * a * a) +
    (4 / 92160 : 𝕂) • (a * a * b * b * b * b * a) +
    (45 / 92160 : 𝕂) • (a * b * a * a * a * a * b) +
    (-80 / 92160 : 𝕂) • (a * b * a * a * a * b * a) +
    (10 / 92160 : 𝕂) • (a * b * a * a * a * b * b) +
    (60 / 92160 : 𝕂) • (a * b * a * a * b * a * a) +
    (44 / 92160 : 𝕂) • (a * b * a * a * b * a * b) +
    (6 / 92160 : 𝕂) • (a * b * a * a * b * b * a) +
    (20 / 92160 : 𝕂) • (a * b * a * a * b * b * b) +
    (-32 / 92160 : 𝕂) • (a * b * a * b * a * a * a) +
    (4 / 92160 : 𝕂) • (a * b * a * b * a * a * b) +
    (-112 / 92160 : 𝕂) • (a * b * a * b * a * b * a) +
    (-28 / 92160 : 𝕂) • (a * b * a * b * a * b * b) +
    (20 / 92160 : 𝕂) • (a * b * a * b * b * a * a) +
    (16 / 92160 : 𝕂) • (a * b * a * b * b * a * b) +
    (-20 / 92160 : 𝕂) • (a * b * a * b * b * b * a) +
    (7 / 92160 : 𝕂) • (a * b * b * a * a * a * a) +
    (6 / 92160 : 𝕂) • (a * b * b * a * a * a * b) +
    (6 / 92160 : 𝕂) • (a * b * b * a * a * b * a) +
    (4 / 92160 : 𝕂) • (a * b * b * a * a * b * b) +
    (30 / 92160 : 𝕂) • (a * b * b * a * b * a * a) +
    (-4 / 92160 : 𝕂) • (a * b * b * a * b * a * b) +
    (24 / 92160 : 𝕂) • (a * b * b * a * b * b * a) +
    (-14 / 92160 : 𝕂) • (a * b * b * b * a * a * a) +
    (4 / 92160 : 𝕂) • (a * b * b * b * a * a * b) +
    (-20 / 92160 : 𝕂) • (a * b * b * b * a * b * a) +
    (4 / 92160 : 𝕂) • (a * b * b * b * b * a * a) +
    (-18 / 92160 : 𝕂) • (b * a * a * a * a * a * b) +
    (45 / 92160 : 𝕂) • (b * a * a * a * a * b * a) +
    (16 / 92160 : 𝕂) • (b * a * a * a * a * b * b) +
    (-50 / 92160 : 𝕂) • (b * a * a * a * b * a * a) +
    (-80 / 92160 : 𝕂) • (b * a * a * a * b * a * b) +
    (6 / 92160 : 𝕂) • (b * a * a * a * b * b * a) +
    (-16 / 92160 : 𝕂) • (b * a * a * a * b * b * b) +
    (30 / 92160 : 𝕂) • (b * a * a * b * a * a * a) +
    (96 / 92160 : 𝕂) • (b * a * a * b * a * a * b) +
    (4 / 92160 : 𝕂) • (b * a * a * b * a * b * a) +
    (40 / 92160 : 𝕂) • (b * a * a * b * a * b * b) +
    (-14 / 92160 : 𝕂) • (b * a * a * b * b * a * a) +
    (-16 / 92160 : 𝕂) • (b * a * a * b * b * a * b) +
    (4 / 92160 : 𝕂) • (b * a * a * b * b * b * a) +
    (-7 / 92160 : 𝕂) • (b * a * b * a * a * a * a) +
    (-80 / 92160 : 𝕂) • (b * a * b * a * a * a * b) +
    (44 / 92160 : 𝕂) • (b * a * b * a * a * b * a) +
    (-40 / 92160 : 𝕂) • (b * a * b * a * a * b * b) +
    (8 / 92160 : 𝕂) • (b * a * b * a * b * a * a) +
    (32 / 92160 : 𝕂) • (b * a * b * a * b * a * b) +
    (-4 / 92160 : 𝕂) • (b * a * b * a * b * b * a) +
    (-16 / 92160 : 𝕂) • (b * a * b * b * a * a * b) +
    (16 / 92160 : 𝕂) • (b * a * b * b * a * b * a) +
    (16 / 92160 : 𝕂) • (b * b * a * a * a * a * b) +
    (10 / 92160 : 𝕂) • (b * b * a * a * a * b * a) +
    (24 / 92160 : 𝕂) • (b * b * a * a * a * b * b) +
    (-40 / 92160 : 𝕂) • (b * b * a * a * b * a * a) +
    (-40 / 92160 : 𝕂) • (b * b * a * a * b * a * b) +
    (4 / 92160 : 𝕂) • (b * b * a * a * b * b * a) +
    (14 / 92160 : 𝕂) • (b * b * a * b * a * a * a) +
    (40 / 92160 : 𝕂) • (b * b * a * b * a * a * b) +
    (-28 / 92160 : 𝕂) • (b * b * a * b * a * b * a) +
    (-16 / 92160 : 𝕂) • (b * b * b * a * a * a * b) +
    (20 / 92160 : 𝕂) • (b * b * b * a * a * b * a) +
    (-4 / 92160 : 𝕂) • (b * b * b * a * b * a * a) +
    -- Degree 8 (78 terms):
    (7 / 184320 : 𝕂) • (a * a * a * b * a * b * a * b) +
    (-7 / 184320 : 𝕂) • (a * a * a * b * a * b * b * a) +
    (-7 / 184320 : 𝕂) • (a * a * a * b * b * a * a * b) +
    (7 / 184320 : 𝕂) • (a * a * a * b * b * a * b * a) +
    (-20 / 184320 : 𝕂) • (a * a * b * a * a * b * a * b) +
    (20 / 184320 : 𝕂) • (a * a * b * a * a * b * b * a) +
    (17 / 184320 : 𝕂) • (a * a * b * a * b * a * a * b) +
    (-15 / 184320 : 𝕂) • (a * a * b * a * b * a * b * a) +
    (-2 / 184320 : 𝕂) • (a * a * b * a * b * a * b * b) +
    (-2 / 184320 : 𝕂) • (a * a * b * a * b * b * a * a) +
    (2 / 184320 : 𝕂) • (a * a * b * a * b * b * b * a) +
    (3 / 184320 : 𝕂) • (a * a * b * b * a * a * a * b) +
    (-5 / 184320 : 𝕂) • (a * a * b * b * a * a * b * a) +
    (2 / 184320 : 𝕂) • (a * a * b * b * a * a * b * b) +
    (2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * a) +
    (-2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * b) +
    (2 / 184320 : 𝕂) • (a * a * b * b * b * a * a * b) +
    (-2 / 184320 : 𝕂) • (a * a * b * b * b * a * b * a) +
    (5 / 184320 : 𝕂) • (a * b * a * a * a * b * a * b) +
    (-5 / 184320 : 𝕂) • (a * b * a * a * a * b * b * a) +
    (30 / 184320 : 𝕂) • (a * b * a * a * b * a * a * b) +
    (-35 / 184320 : 𝕂) • (a * b * a * a * b * a * b * a) +
    (10 / 184320 : 𝕂) • (a * b * a * a * b * a * b * b) +
    (5 / 184320 : 𝕂) • (a * b * a * a * b * b * a * a) +
    (-10 / 184320 : 𝕂) • (a * b * a * a * b * b * b * a) +
    (-43 / 184320 : 𝕂) • (a * b * a * b * a * a * a * b) +
    (35 / 184320 : 𝕂) • (a * b * a * b * a * a * b * a) +
    (-22 / 184320 : 𝕂) • (a * b * a * b * a * a * b * b) +
    (15 / 184320 : 𝕂) • (a * b * a * b * a * b * a * a) +
    (16 / 184320 : 𝕂) • (a * b * a * b * a * b * a * b) +
    (12 / 184320 : 𝕂) • (a * b * a * b * a * b * b * a) +
    (-7 / 184320 : 𝕂) • (a * b * a * b * b * a * a * a) +
    (-8 / 184320 : 𝕂) • (a * b * a * b * b * a * a * b) +
    (2 / 184320 : 𝕂) • (a * b * a * b * b * b * a * a) +
    (8 / 184320 : 𝕂) • (a * b * b * a * a * a * a * b) +
    (5 / 184320 : 𝕂) • (a * b * b * a * a * a * b * a) +
    (12 / 184320 : 𝕂) • (a * b * b * a * a * a * b * b) +
    (-20 / 184320 : 𝕂) • (a * b * b * a * a * b * a * a) +
    (-18 / 184320 : 𝕂) • (a * b * b * a * a * b * a * b) +
    (7 / 184320 : 𝕂) • (a * b * b * a * b * a * a * a) +
    (18 / 184320 : 𝕂) • (a * b * b * a * b * a * a * b) +
    (-12 / 184320 : 𝕂) • (a * b * b * a * b * a * b * a) +
    (-8 / 184320 : 𝕂) • (a * b * b * b * a * a * a * b) +
    (10 / 184320 : 𝕂) • (a * b * b * b * a * a * b * a) +
    (-2 / 184320 : 𝕂) • (a * b * b * b * a * b * a * a) +
    (8 / 184320 : 𝕂) • (b * a * a * a * a * b * a * b) +
    (-8 / 184320 : 𝕂) • (b * a * a * a * a * b * b * a) +
    (-40 / 184320 : 𝕂) • (b * a * a * a * b * a * a * b) +
    (43 / 184320 : 𝕂) • (b * a * a * a * b * a * b * a) +
    (-8 / 184320 : 𝕂) • (b * a * a * a * b * a * b * b) +
    (-3 / 184320 : 𝕂) • (b * a * a * a * b * b * a * a) +
    (8 / 184320 : 𝕂) • (b * a * a * a * b * b * b * a) +
    (40 / 184320 : 𝕂) • (b * a * a * b * a * a * a * b) +
    (-30 / 184320 : 𝕂) • (b * a * a * b * a * a * b * a) +
    (20 / 184320 : 𝕂) • (b * a * a * b * a * a * b * b) +
    (-17 / 184320 : 𝕂) • (b * a * a * b * a * b * a * a) +
    (-8 / 184320 : 𝕂) • (b * a * a * b * a * b * a * b) +
    (-18 / 184320 : 𝕂) • (b * a * a * b * a * b * b * a) +
    (7 / 184320 : 𝕂) • (b * a * a * b * b * a * a * a) +
    (8 / 184320 : 𝕂) • (b * a * a * b * b * a * b * a) +
    (-2 / 184320 : 𝕂) • (b * a * a * b * b * b * a * a) +
    (-8 / 184320 : 𝕂) • (b * a * b * a * a * a * a * b) +
    (-5 / 184320 : 𝕂) • (b * a * b * a * a * a * b * a) +
    (-12 / 184320 : 𝕂) • (b * a * b * a * a * a * b * b) +
    (20 / 184320 : 𝕂) • (b * a * b * a * a * b * a * a) +
    (18 / 184320 : 𝕂) • (b * a * b * a * a * b * b * a) +
    (-7 / 184320 : 𝕂) • (b * a * b * a * b * a * a * a) +
    (8 / 184320 : 𝕂) • (b * a * b * a * b * a * a * b) +
    (-16 / 184320 : 𝕂) • (b * a * b * a * b * a * b * a) +
    (2 / 184320 : 𝕂) • (b * a * b * a * b * b * a * a) +
    (12 / 184320 : 𝕂) • (b * b * a * a * a * b * a * b) +
    (-12 / 184320 : 𝕂) • (b * b * a * a * a * b * b * a) +
    (-20 / 184320 : 𝕂) • (b * b * a * a * b * a * a * b) +
    (22 / 184320 : 𝕂) • (b * b * a * a * b * a * b * a) +
    (-2 / 184320 : 𝕂) • (b * b * a * a * b * b * a * a) +
    (8 / 184320 : 𝕂) • (b * b * a * b * a * a * a * b) +
    (-10 / 184320 : 𝕂) • (b * b * a * b * a * a * b * a) +
    (2 / 184320 : 𝕂) • (b * b * a * b * a * b * a * a) +
    -- Degree 9 (48 terms):
    (-1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * a * b) +
    (1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * b * a) +
    (1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * a * b) +
    (-1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * b * a) +
    (1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * a * b) +
    (-1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * b * a) +
    (-1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * a * b) +
    (1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * b * a) +
    (5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * a * b) +
    (-5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * b * a) +
    (-5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * a * b) +
    (5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * b * a) +
    (-11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * a * b) +
    (11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * b * a) +
    (15 / 368640 : 𝕂) • (a * b * a * b * a * b * a * a * b) +
    (-16 / 368640 : 𝕂) • (a * b * a * b * a * b * a * b * a) +
    (1 / 368640 : 𝕂) • (a * b * a * b * a * b * b * a * a) +
    (-4 / 368640 : 𝕂) • (a * b * a * b * b * a * a * a * b) +
    (5 / 368640 : 𝕂) • (a * b * a * b * b * a * a * b * a) +
    (-1 / 368640 : 𝕂) • (a * b * a * b * b * a * b * a * a) +
    (6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * a * b) +
    (-6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * b * a) +
    (-10 / 368640 : 𝕂) • (a * b * b * a * a * b * a * a * b) +
    (11 / 368640 : 𝕂) • (a * b * b * a * a * b * a * b * a) +
    (-1 / 368640 : 𝕂) • (a * b * b * a * a * b * b * a * a) +
    (4 / 368640 : 𝕂) • (a * b * b * a * b * a * a * a * b) +
    (-5 / 368640 : 𝕂) • (a * b * b * a * b * a * a * b * a) +
    (1 / 368640 : 𝕂) • (a * b * b * a * b * a * b * a * a) +
    (-4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * a * b) +
    (4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * b * a) +
    (4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * a * b) +
    (-4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * b * a) +
    (10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * a * b) +
    (-10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * b * a) +
    (-14 / 368640 : 𝕂) • (b * a * a * b * a * b * a * a * b) +
    (15 / 368640 : 𝕂) • (b * a * a * b * a * b * a * b * a) +
    (-1 / 368640 : 𝕂) • (b * a * a * b * a * b * b * a * a) +
    (4 / 368640 : 𝕂) • (b * a * a * b * b * a * a * a * b) +
    (-5 / 368640 : 𝕂) • (b * a * a * b * b * a * a * b * a) +
    (1 / 368640 : 𝕂) • (b * a * a * b * b * a * b * a * a) +
    (-6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * a * b) +
    (6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * b * a) +
    (10 / 368640 : 𝕂) • (b * a * b * a * a * b * a * a * b) +
    (-11 / 368640 : 𝕂) • (b * a * b * a * a * b * a * b * a) +
    (1 / 368640 : 𝕂) • (b * a * b * a * a * b * b * a * a) +
    (-4 / 368640 : 𝕂) • (b * a * b * a * b * a * a * a * b) +
    (5 / 368640 : 𝕂) • (b * a * b * a * b * a * a * b * a) +
    (-1 / 368640 : 𝕂) • (b * a * b * a * b * a * b * a * a)

-- Algebraic identity: at z₁ = (a'+b)+V₂ where V₂ = ½·[a',b], a' = a/2,
-- the C5 Taylor difference minus the explicit linear-in-V₂ leading polynomial
-- equals the explicit deg-7+ residual polynomial `C5_LinResidual_polynomial`.
-- Pure polynomial identity in (a, b). Proved by `match_scalars + ring`.
set_option maxHeartbeats 1024000000 in
private theorem C5_LinResidual_at_V2_eq_polynomial
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    (bch_quintic_term 𝕂 ((a' + b) + V₂) a' - bch_quintic_term 𝕂 (a' + b) a') -
     ((-14 / 46080 : 𝕂) • (a * a * a * a * b * b) +
      (46 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (10 / 46080 : 𝕂) • (a * a * a * b * b * a) +
      (28 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (-54 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (-30 / 46080 : 𝕂) • (a * a * b * a * b * a) +
      (-52 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (-12 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (-20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
      (-8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
      (36 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (-32 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (30 / 46080 : 𝕂) • (a * b * a * b * a * a) +
      (128 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
      (32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
      (-10 / 46080 : 𝕂) • (a * b * b * a * a * a) +
      (-32 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (-40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
      (-48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
      (20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
      (32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
      (-36 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (54 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (32 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (-46 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (-128 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (12 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (-32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
      (14 / 46080 : 𝕂) • (b * b * a * a * a * a) +
      (32 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (52 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
      (-28 / 46080 : 𝕂) • (b * b * b * a * a * a) +
      (-32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
      (8 / 46080 : 𝕂) • (b * b * b * b * a * a)) =
    C5_LinResidual_polynomial 𝕂 a b := by
  intro a' V₂
  -- Unfold all definitions to get a polynomial identity in (a, b).
  show _ = _
  unfold C5_LinResidual_polynomial bch_quintic_term bch_quintic_group_1
    bch_quintic_group_4 bch_quintic_group_6 bch_quintic_group_24
  simp only [show V₂ = ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) from rfl,
             show a' = ((2 : 𝕂)⁻¹ • a : 𝔸) from rfl]
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc,
    neg_mul, mul_neg, neg_neg, sub_neg_eq_add, neg_smul, smul_neg]
  match_scalars <;> ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Helper (deg-7)**: `‖c • (l₁·…·l7)‖ ≤ cb · s^7` if `‖c‖ ≤ cb` and each `‖lᵢ‖ ≤ s`. -/
private lemma deg7_smul_word_le
    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)
    (l1 l2 l3 l4 l5 l6 l7 : 𝔸) (s : ℝ)
    (h1 : ‖l1‖ ≤ s) (h2 : ‖l2‖ ≤ s) (h3 : ‖l3‖ ≤ s) (h4 : ‖l4‖ ≤ s) (h5 : ‖l5‖ ≤ s) (h6 : ‖l6‖ ≤ s) (h7 : ‖l7‖ ≤ s)
    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :
    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7)‖ ≤ cb * s ^ 7 := by
  calc ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7)‖
      ≤ ‖c‖ * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖ := norm_smul_le _ _
    _ ≤ cb * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖) :=
        mul_le_mul_of_nonneg_left (norm_7prod_le _ _ _ _ _ _ _) hcb
    _ ≤ cb * (s * s * s * s * s * s * s) := by
        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr
    _ = cb * s ^ 7 := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Helper (deg-8)**: `‖c • (l₁·…·l8)‖ ≤ cb · s^8` if `‖c‖ ≤ cb` and each `‖lᵢ‖ ≤ s`. -/
private lemma deg8_smul_word_le
    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)
    (l1 l2 l3 l4 l5 l6 l7 l8 : 𝔸) (s : ℝ)
    (h1 : ‖l1‖ ≤ s) (h2 : ‖l2‖ ≤ s) (h3 : ‖l3‖ ≤ s) (h4 : ‖l4‖ ≤ s) (h5 : ‖l5‖ ≤ s) (h6 : ‖l6‖ ≤ s) (h7 : ‖l7‖ ≤ s) (h8 : ‖l8‖ ≤ s)
    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :
    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8)‖ ≤ cb * s ^ 8 := by
  calc ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8)‖
      ≤ ‖c‖ * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8‖ := norm_smul_le _ _
    _ ≤ cb * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖ * ‖l8‖) :=
        mul_le_mul_of_nonneg_left (norm_8prod_le _ _ _ _ _ _ _ _) hcb
    _ ≤ cb * (s * s * s * s * s * s * s * s) := by
        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr
    _ = cb * s ^ 8 := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Helper (deg-9)**: `‖c • (l₁·…·l9)‖ ≤ cb · s^9` if `‖c‖ ≤ cb` and each `‖lᵢ‖ ≤ s`. -/
private lemma deg9_smul_word_le
    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)
    (l1 l2 l3 l4 l5 l6 l7 l8 l9 : 𝔸) (s : ℝ)
    (h1 : ‖l1‖ ≤ s) (h2 : ‖l2‖ ≤ s) (h3 : ‖l3‖ ≤ s) (h4 : ‖l4‖ ≤ s) (h5 : ‖l5‖ ≤ s) (h6 : ‖l6‖ ≤ s) (h7 : ‖l7‖ ≤ s) (h8 : ‖l8‖ ≤ s) (h9 : ‖l9‖ ≤ s)
    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :
    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8 * l9)‖ ≤ cb * s ^ 9 := by
  calc ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8 * l9)‖
      ≤ ‖c‖ * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8 * l9‖ := norm_smul_le _ _
    _ ≤ cb * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8 * l9‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖ * ‖l8‖ * ‖l9‖) :=
        mul_le_mul_of_nonneg_left (norm_9prod_le _ _ _ _ _ _ _ _ _) hcb
    _ ≤ cb * (s * s * s * s * s * s * s * s * s) := by
        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr
    _ = cb * s ^ 9 := by ring

/-- Per-index family: the 79 deg-7 terms of `C5_LinResidual_polynomial`. -/
private noncomputable def linResTerm7 (a b : 𝔸) : Fin 79 → 𝔸
  | ⟨0, _⟩ => (-7 / 92160 : 𝕂) • (a * a * a * a * b * a * b)
  | ⟨1, _⟩ => (7 / 92160 : 𝕂) • (a * a * a * a * b * b * a)
  | ⟨2, _⟩ => (30 / 92160 : 𝕂) • (a * a * a * b * a * a * b)
  | ⟨3, _⟩ => (-32 / 92160 : 𝕂) • (a * a * a * b * a * b * a)
  | ⟨4, _⟩ => (14 / 92160 : 𝕂) • (a * a * a * b * a * b * b)
  | ⟨5, _⟩ => (2 / 92160 : 𝕂) • (a * a * a * b * b * a * a)
  | ⟨6, _⟩ => (-14 / 92160 : 𝕂) • (a * a * a * b * b * b * a)
  | ⟨7, _⟩ => (-50 / 92160 : 𝕂) • (a * a * b * a * a * a * b)
  | ⟨8, _⟩ => (60 / 92160 : 𝕂) • (a * a * b * a * a * b * a)
  | ⟨9, _⟩ => (-40 / 92160 : 𝕂) • (a * a * b * a * a * b * b)
  | ⟨10, _⟩ => (-12 / 92160 : 𝕂) • (a * a * b * a * b * a * a)
  | ⟨11, _⟩ => (8 / 92160 : 𝕂) • (a * a * b * a * b * a * b)
  | ⟨12, _⟩ => (30 / 92160 : 𝕂) • (a * a * b * a * b * b * a)
  | ⟨13, _⟩ => (-4 / 92160 : 𝕂) • (a * a * b * a * b * b * b)
  | ⟨14, _⟩ => (2 / 92160 : 𝕂) • (a * a * b * b * a * a * a)
  | ⟨15, _⟩ => (-14 / 92160 : 𝕂) • (a * a * b * b * a * a * b)
  | ⟨16, _⟩ => (20 / 92160 : 𝕂) • (a * a * b * b * a * b * a)
  | ⟨17, _⟩ => (-4 / 92160 : 𝕂) • (a * a * b * b * b * a * a)
  | ⟨18, _⟩ => (4 / 92160 : 𝕂) • (a * a * b * b * b * b * a)
  | ⟨19, _⟩ => (45 / 92160 : 𝕂) • (a * b * a * a * a * a * b)
  | ⟨20, _⟩ => (-80 / 92160 : 𝕂) • (a * b * a * a * a * b * a)
  | ⟨21, _⟩ => (10 / 92160 : 𝕂) • (a * b * a * a * a * b * b)
  | ⟨22, _⟩ => (60 / 92160 : 𝕂) • (a * b * a * a * b * a * a)
  | ⟨23, _⟩ => (44 / 92160 : 𝕂) • (a * b * a * a * b * a * b)
  | ⟨24, _⟩ => (6 / 92160 : 𝕂) • (a * b * a * a * b * b * a)
  | ⟨25, _⟩ => (20 / 92160 : 𝕂) • (a * b * a * a * b * b * b)
  | ⟨26, _⟩ => (-32 / 92160 : 𝕂) • (a * b * a * b * a * a * a)
  | ⟨27, _⟩ => (4 / 92160 : 𝕂) • (a * b * a * b * a * a * b)
  | ⟨28, _⟩ => (-112 / 92160 : 𝕂) • (a * b * a * b * a * b * a)
  | ⟨29, _⟩ => (-28 / 92160 : 𝕂) • (a * b * a * b * a * b * b)
  | ⟨30, _⟩ => (20 / 92160 : 𝕂) • (a * b * a * b * b * a * a)
  | ⟨31, _⟩ => (16 / 92160 : 𝕂) • (a * b * a * b * b * a * b)
  | ⟨32, _⟩ => (-20 / 92160 : 𝕂) • (a * b * a * b * b * b * a)
  | ⟨33, _⟩ => (7 / 92160 : 𝕂) • (a * b * b * a * a * a * a)
  | ⟨34, _⟩ => (6 / 92160 : 𝕂) • (a * b * b * a * a * a * b)
  | ⟨35, _⟩ => (6 / 92160 : 𝕂) • (a * b * b * a * a * b * a)
  | ⟨36, _⟩ => (4 / 92160 : 𝕂) • (a * b * b * a * a * b * b)
  | ⟨37, _⟩ => (30 / 92160 : 𝕂) • (a * b * b * a * b * a * a)
  | ⟨38, _⟩ => (-4 / 92160 : 𝕂) • (a * b * b * a * b * a * b)
  | ⟨39, _⟩ => (24 / 92160 : 𝕂) • (a * b * b * a * b * b * a)
  | ⟨40, _⟩ => (-14 / 92160 : 𝕂) • (a * b * b * b * a * a * a)
  | ⟨41, _⟩ => (4 / 92160 : 𝕂) • (a * b * b * b * a * a * b)
  | ⟨42, _⟩ => (-20 / 92160 : 𝕂) • (a * b * b * b * a * b * a)
  | ⟨43, _⟩ => (4 / 92160 : 𝕂) • (a * b * b * b * b * a * a)
  | ⟨44, _⟩ => (-18 / 92160 : 𝕂) • (b * a * a * a * a * a * b)
  | ⟨45, _⟩ => (45 / 92160 : 𝕂) • (b * a * a * a * a * b * a)
  | ⟨46, _⟩ => (16 / 92160 : 𝕂) • (b * a * a * a * a * b * b)
  | ⟨47, _⟩ => (-50 / 92160 : 𝕂) • (b * a * a * a * b * a * a)
  | ⟨48, _⟩ => (-80 / 92160 : 𝕂) • (b * a * a * a * b * a * b)
  | ⟨49, _⟩ => (6 / 92160 : 𝕂) • (b * a * a * a * b * b * a)
  | ⟨50, _⟩ => (-16 / 92160 : 𝕂) • (b * a * a * a * b * b * b)
  | ⟨51, _⟩ => (30 / 92160 : 𝕂) • (b * a * a * b * a * a * a)
  | ⟨52, _⟩ => (96 / 92160 : 𝕂) • (b * a * a * b * a * a * b)
  | ⟨53, _⟩ => (4 / 92160 : 𝕂) • (b * a * a * b * a * b * a)
  | ⟨54, _⟩ => (40 / 92160 : 𝕂) • (b * a * a * b * a * b * b)
  | ⟨55, _⟩ => (-14 / 92160 : 𝕂) • (b * a * a * b * b * a * a)
  | ⟨56, _⟩ => (-16 / 92160 : 𝕂) • (b * a * a * b * b * a * b)
  | ⟨57, _⟩ => (4 / 92160 : 𝕂) • (b * a * a * b * b * b * a)
  | ⟨58, _⟩ => (-7 / 92160 : 𝕂) • (b * a * b * a * a * a * a)
  | ⟨59, _⟩ => (-80 / 92160 : 𝕂) • (b * a * b * a * a * a * b)
  | ⟨60, _⟩ => (44 / 92160 : 𝕂) • (b * a * b * a * a * b * a)
  | ⟨61, _⟩ => (-40 / 92160 : 𝕂) • (b * a * b * a * a * b * b)
  | ⟨62, _⟩ => (8 / 92160 : 𝕂) • (b * a * b * a * b * a * a)
  | ⟨63, _⟩ => (32 / 92160 : 𝕂) • (b * a * b * a * b * a * b)
  | ⟨64, _⟩ => (-4 / 92160 : 𝕂) • (b * a * b * a * b * b * a)
  | ⟨65, _⟩ => (-16 / 92160 : 𝕂) • (b * a * b * b * a * a * b)
  | ⟨66, _⟩ => (16 / 92160 : 𝕂) • (b * a * b * b * a * b * a)
  | ⟨67, _⟩ => (16 / 92160 : 𝕂) • (b * b * a * a * a * a * b)
  | ⟨68, _⟩ => (10 / 92160 : 𝕂) • (b * b * a * a * a * b * a)
  | ⟨69, _⟩ => (24 / 92160 : 𝕂) • (b * b * a * a * a * b * b)
  | ⟨70, _⟩ => (-40 / 92160 : 𝕂) • (b * b * a * a * b * a * a)
  | ⟨71, _⟩ => (-40 / 92160 : 𝕂) • (b * b * a * a * b * a * b)
  | ⟨72, _⟩ => (4 / 92160 : 𝕂) • (b * b * a * a * b * b * a)
  | ⟨73, _⟩ => (14 / 92160 : 𝕂) • (b * b * a * b * a * a * a)
  | ⟨74, _⟩ => (40 / 92160 : 𝕂) • (b * b * a * b * a * a * b)
  | ⟨75, _⟩ => (-28 / 92160 : 𝕂) • (b * b * a * b * a * b * a)
  | ⟨76, _⟩ => (-16 / 92160 : 𝕂) • (b * b * b * a * a * a * b)
  | ⟨77, _⟩ => (20 / 92160 : 𝕂) • (b * b * b * a * a * b * a)
  | ⟨78, _⟩ => (-4 / 92160 : 𝕂) • (b * b * b * a * b * a * a)
  | ⟨_ + 79, h⟩ => absurd h (by omega)

/-- Per-index family: the 78 deg-8 terms of `C5_LinResidual_polynomial`. -/
private noncomputable def linResTerm8 (a b : 𝔸) : Fin 78 → 𝔸
  | ⟨0, _⟩ => (7 / 184320 : 𝕂) • (a * a * a * b * a * b * a * b)
  | ⟨1, _⟩ => (-7 / 184320 : 𝕂) • (a * a * a * b * a * b * b * a)
  | ⟨2, _⟩ => (-7 / 184320 : 𝕂) • (a * a * a * b * b * a * a * b)
  | ⟨3, _⟩ => (7 / 184320 : 𝕂) • (a * a * a * b * b * a * b * a)
  | ⟨4, _⟩ => (-20 / 184320 : 𝕂) • (a * a * b * a * a * b * a * b)
  | ⟨5, _⟩ => (20 / 184320 : 𝕂) • (a * a * b * a * a * b * b * a)
  | ⟨6, _⟩ => (17 / 184320 : 𝕂) • (a * a * b * a * b * a * a * b)
  | ⟨7, _⟩ => (-15 / 184320 : 𝕂) • (a * a * b * a * b * a * b * a)
  | ⟨8, _⟩ => (-2 / 184320 : 𝕂) • (a * a * b * a * b * a * b * b)
  | ⟨9, _⟩ => (-2 / 184320 : 𝕂) • (a * a * b * a * b * b * a * a)
  | ⟨10, _⟩ => (2 / 184320 : 𝕂) • (a * a * b * a * b * b * b * a)
  | ⟨11, _⟩ => (3 / 184320 : 𝕂) • (a * a * b * b * a * a * a * b)
  | ⟨12, _⟩ => (-5 / 184320 : 𝕂) • (a * a * b * b * a * a * b * a)
  | ⟨13, _⟩ => (2 / 184320 : 𝕂) • (a * a * b * b * a * a * b * b)
  | ⟨14, _⟩ => (2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * a)
  | ⟨15, _⟩ => (-2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * b)
  | ⟨16, _⟩ => (2 / 184320 : 𝕂) • (a * a * b * b * b * a * a * b)
  | ⟨17, _⟩ => (-2 / 184320 : 𝕂) • (a * a * b * b * b * a * b * a)
  | ⟨18, _⟩ => (5 / 184320 : 𝕂) • (a * b * a * a * a * b * a * b)
  | ⟨19, _⟩ => (-5 / 184320 : 𝕂) • (a * b * a * a * a * b * b * a)
  | ⟨20, _⟩ => (30 / 184320 : 𝕂) • (a * b * a * a * b * a * a * b)
  | ⟨21, _⟩ => (-35 / 184320 : 𝕂) • (a * b * a * a * b * a * b * a)
  | ⟨22, _⟩ => (10 / 184320 : 𝕂) • (a * b * a * a * b * a * b * b)
  | ⟨23, _⟩ => (5 / 184320 : 𝕂) • (a * b * a * a * b * b * a * a)
  | ⟨24, _⟩ => (-10 / 184320 : 𝕂) • (a * b * a * a * b * b * b * a)
  | ⟨25, _⟩ => (-43 / 184320 : 𝕂) • (a * b * a * b * a * a * a * b)
  | ⟨26, _⟩ => (35 / 184320 : 𝕂) • (a * b * a * b * a * a * b * a)
  | ⟨27, _⟩ => (-22 / 184320 : 𝕂) • (a * b * a * b * a * a * b * b)
  | ⟨28, _⟩ => (15 / 184320 : 𝕂) • (a * b * a * b * a * b * a * a)
  | ⟨29, _⟩ => (16 / 184320 : 𝕂) • (a * b * a * b * a * b * a * b)
  | ⟨30, _⟩ => (12 / 184320 : 𝕂) • (a * b * a * b * a * b * b * a)
  | ⟨31, _⟩ => (-7 / 184320 : 𝕂) • (a * b * a * b * b * a * a * a)
  | ⟨32, _⟩ => (-8 / 184320 : 𝕂) • (a * b * a * b * b * a * a * b)
  | ⟨33, _⟩ => (2 / 184320 : 𝕂) • (a * b * a * b * b * b * a * a)
  | ⟨34, _⟩ => (8 / 184320 : 𝕂) • (a * b * b * a * a * a * a * b)
  | ⟨35, _⟩ => (5 / 184320 : 𝕂) • (a * b * b * a * a * a * b * a)
  | ⟨36, _⟩ => (12 / 184320 : 𝕂) • (a * b * b * a * a * a * b * b)
  | ⟨37, _⟩ => (-20 / 184320 : 𝕂) • (a * b * b * a * a * b * a * a)
  | ⟨38, _⟩ => (-18 / 184320 : 𝕂) • (a * b * b * a * a * b * a * b)
  | ⟨39, _⟩ => (7 / 184320 : 𝕂) • (a * b * b * a * b * a * a * a)
  | ⟨40, _⟩ => (18 / 184320 : 𝕂) • (a * b * b * a * b * a * a * b)
  | ⟨41, _⟩ => (-12 / 184320 : 𝕂) • (a * b * b * a * b * a * b * a)
  | ⟨42, _⟩ => (-8 / 184320 : 𝕂) • (a * b * b * b * a * a * a * b)
  | ⟨43, _⟩ => (10 / 184320 : 𝕂) • (a * b * b * b * a * a * b * a)
  | ⟨44, _⟩ => (-2 / 184320 : 𝕂) • (a * b * b * b * a * b * a * a)
  | ⟨45, _⟩ => (8 / 184320 : 𝕂) • (b * a * a * a * a * b * a * b)
  | ⟨46, _⟩ => (-8 / 184320 : 𝕂) • (b * a * a * a * a * b * b * a)
  | ⟨47, _⟩ => (-40 / 184320 : 𝕂) • (b * a * a * a * b * a * a * b)
  | ⟨48, _⟩ => (43 / 184320 : 𝕂) • (b * a * a * a * b * a * b * a)
  | ⟨49, _⟩ => (-8 / 184320 : 𝕂) • (b * a * a * a * b * a * b * b)
  | ⟨50, _⟩ => (-3 / 184320 : 𝕂) • (b * a * a * a * b * b * a * a)
  | ⟨51, _⟩ => (8 / 184320 : 𝕂) • (b * a * a * a * b * b * b * a)
  | ⟨52, _⟩ => (40 / 184320 : 𝕂) • (b * a * a * b * a * a * a * b)
  | ⟨53, _⟩ => (-30 / 184320 : 𝕂) • (b * a * a * b * a * a * b * a)
  | ⟨54, _⟩ => (20 / 184320 : 𝕂) • (b * a * a * b * a * a * b * b)
  | ⟨55, _⟩ => (-17 / 184320 : 𝕂) • (b * a * a * b * a * b * a * a)
  | ⟨56, _⟩ => (-8 / 184320 : 𝕂) • (b * a * a * b * a * b * a * b)
  | ⟨57, _⟩ => (-18 / 184320 : 𝕂) • (b * a * a * b * a * b * b * a)
  | ⟨58, _⟩ => (7 / 184320 : 𝕂) • (b * a * a * b * b * a * a * a)
  | ⟨59, _⟩ => (8 / 184320 : 𝕂) • (b * a * a * b * b * a * b * a)
  | ⟨60, _⟩ => (-2 / 184320 : 𝕂) • (b * a * a * b * b * b * a * a)
  | ⟨61, _⟩ => (-8 / 184320 : 𝕂) • (b * a * b * a * a * a * a * b)
  | ⟨62, _⟩ => (-5 / 184320 : 𝕂) • (b * a * b * a * a * a * b * a)
  | ⟨63, _⟩ => (-12 / 184320 : 𝕂) • (b * a * b * a * a * a * b * b)
  | ⟨64, _⟩ => (20 / 184320 : 𝕂) • (b * a * b * a * a * b * a * a)
  | ⟨65, _⟩ => (18 / 184320 : 𝕂) • (b * a * b * a * a * b * b * a)
  | ⟨66, _⟩ => (-7 / 184320 : 𝕂) • (b * a * b * a * b * a * a * a)
  | ⟨67, _⟩ => (8 / 184320 : 𝕂) • (b * a * b * a * b * a * a * b)
  | ⟨68, _⟩ => (-16 / 184320 : 𝕂) • (b * a * b * a * b * a * b * a)
  | ⟨69, _⟩ => (2 / 184320 : 𝕂) • (b * a * b * a * b * b * a * a)
  | ⟨70, _⟩ => (12 / 184320 : 𝕂) • (b * b * a * a * a * b * a * b)
  | ⟨71, _⟩ => (-12 / 184320 : 𝕂) • (b * b * a * a * a * b * b * a)
  | ⟨72, _⟩ => (-20 / 184320 : 𝕂) • (b * b * a * a * b * a * a * b)
  | ⟨73, _⟩ => (22 / 184320 : 𝕂) • (b * b * a * a * b * a * b * a)
  | ⟨74, _⟩ => (-2 / 184320 : 𝕂) • (b * b * a * a * b * b * a * a)
  | ⟨75, _⟩ => (8 / 184320 : 𝕂) • (b * b * a * b * a * a * a * b)
  | ⟨76, _⟩ => (-10 / 184320 : 𝕂) • (b * b * a * b * a * a * b * a)
  | ⟨77, _⟩ => (2 / 184320 : 𝕂) • (b * b * a * b * a * b * a * a)
  | ⟨_ + 78, h⟩ => absurd h (by omega)

/-- Per-index family: the 48 deg-9 terms of `C5_LinResidual_polynomial`. -/
private noncomputable def linResTerm9 (a b : 𝔸) : Fin 48 → 𝔸
  | ⟨0, _⟩ => (-1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * a * b)
  | ⟨1, _⟩ => (1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * b * a)
  | ⟨2, _⟩ => (1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * a * b)
  | ⟨3, _⟩ => (-1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * b * a)
  | ⟨4, _⟩ => (1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * a * b)
  | ⟨5, _⟩ => (-1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * b * a)
  | ⟨6, _⟩ => (-1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * a * b)
  | ⟨7, _⟩ => (1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * b * a)
  | ⟨8, _⟩ => (5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * a * b)
  | ⟨9, _⟩ => (-5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * b * a)
  | ⟨10, _⟩ => (-5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * a * b)
  | ⟨11, _⟩ => (5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * b * a)
  | ⟨12, _⟩ => (-11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * a * b)
  | ⟨13, _⟩ => (11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * b * a)
  | ⟨14, _⟩ => (15 / 368640 : 𝕂) • (a * b * a * b * a * b * a * a * b)
  | ⟨15, _⟩ => (-16 / 368640 : 𝕂) • (a * b * a * b * a * b * a * b * a)
  | ⟨16, _⟩ => (1 / 368640 : 𝕂) • (a * b * a * b * a * b * b * a * a)
  | ⟨17, _⟩ => (-4 / 368640 : 𝕂) • (a * b * a * b * b * a * a * a * b)
  | ⟨18, _⟩ => (5 / 368640 : 𝕂) • (a * b * a * b * b * a * a * b * a)
  | ⟨19, _⟩ => (-1 / 368640 : 𝕂) • (a * b * a * b * b * a * b * a * a)
  | ⟨20, _⟩ => (6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * a * b)
  | ⟨21, _⟩ => (-6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * b * a)
  | ⟨22, _⟩ => (-10 / 368640 : 𝕂) • (a * b * b * a * a * b * a * a * b)
  | ⟨23, _⟩ => (11 / 368640 : 𝕂) • (a * b * b * a * a * b * a * b * a)
  | ⟨24, _⟩ => (-1 / 368640 : 𝕂) • (a * b * b * a * a * b * b * a * a)
  | ⟨25, _⟩ => (4 / 368640 : 𝕂) • (a * b * b * a * b * a * a * a * b)
  | ⟨26, _⟩ => (-5 / 368640 : 𝕂) • (a * b * b * a * b * a * a * b * a)
  | ⟨27, _⟩ => (1 / 368640 : 𝕂) • (a * b * b * a * b * a * b * a * a)
  | ⟨28, _⟩ => (-4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * a * b)
  | ⟨29, _⟩ => (4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * b * a)
  | ⟨30, _⟩ => (4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * a * b)
  | ⟨31, _⟩ => (-4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * b * a)
  | ⟨32, _⟩ => (10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * a * b)
  | ⟨33, _⟩ => (-10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * b * a)
  | ⟨34, _⟩ => (-14 / 368640 : 𝕂) • (b * a * a * b * a * b * a * a * b)
  | ⟨35, _⟩ => (15 / 368640 : 𝕂) • (b * a * a * b * a * b * a * b * a)
  | ⟨36, _⟩ => (-1 / 368640 : 𝕂) • (b * a * a * b * a * b * b * a * a)
  | ⟨37, _⟩ => (4 / 368640 : 𝕂) • (b * a * a * b * b * a * a * a * b)
  | ⟨38, _⟩ => (-5 / 368640 : 𝕂) • (b * a * a * b * b * a * a * b * a)
  | ⟨39, _⟩ => (1 / 368640 : 𝕂) • (b * a * a * b * b * a * b * a * a)
  | ⟨40, _⟩ => (-6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * a * b)
  | ⟨41, _⟩ => (6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * b * a)
  | ⟨42, _⟩ => (10 / 368640 : 𝕂) • (b * a * b * a * a * b * a * a * b)
  | ⟨43, _⟩ => (-11 / 368640 : 𝕂) • (b * a * b * a * a * b * a * b * a)
  | ⟨44, _⟩ => (1 / 368640 : 𝕂) • (b * a * b * a * a * b * b * a * a)
  | ⟨45, _⟩ => (-4 / 368640 : 𝕂) • (b * a * b * a * b * a * a * a * b)
  | ⟨46, _⟩ => (5 / 368640 : 𝕂) • (b * a * b * a * b * a * a * b * a)
  | ⟨47, _⟩ => (-1 / 368640 : 𝕂) • (b * a * b * a * b * a * b * a * a)
  | ⟨_ + 48, h⟩ => absurd h (by omega)

/-- Per-index upper bound on `‖linResTerm7 i‖`. -/
private noncomputable def linResBound7 (s : ℝ) : Fin 79 → ℝ
  | ⟨0, _⟩ => (7 / 92160 : ℝ) * s ^ 7
  | ⟨1, _⟩ => (7 / 92160 : ℝ) * s ^ 7
  | ⟨2, _⟩ => (30 / 92160 : ℝ) * s ^ 7
  | ⟨3, _⟩ => (32 / 92160 : ℝ) * s ^ 7
  | ⟨4, _⟩ => (14 / 92160 : ℝ) * s ^ 7
  | ⟨5, _⟩ => (2 / 92160 : ℝ) * s ^ 7
  | ⟨6, _⟩ => (14 / 92160 : ℝ) * s ^ 7
  | ⟨7, _⟩ => (50 / 92160 : ℝ) * s ^ 7
  | ⟨8, _⟩ => (60 / 92160 : ℝ) * s ^ 7
  | ⟨9, _⟩ => (40 / 92160 : ℝ) * s ^ 7
  | ⟨10, _⟩ => (12 / 92160 : ℝ) * s ^ 7
  | ⟨11, _⟩ => (8 / 92160 : ℝ) * s ^ 7
  | ⟨12, _⟩ => (30 / 92160 : ℝ) * s ^ 7
  | ⟨13, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨14, _⟩ => (2 / 92160 : ℝ) * s ^ 7
  | ⟨15, _⟩ => (14 / 92160 : ℝ) * s ^ 7
  | ⟨16, _⟩ => (20 / 92160 : ℝ) * s ^ 7
  | ⟨17, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨18, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨19, _⟩ => (45 / 92160 : ℝ) * s ^ 7
  | ⟨20, _⟩ => (80 / 92160 : ℝ) * s ^ 7
  | ⟨21, _⟩ => (10 / 92160 : ℝ) * s ^ 7
  | ⟨22, _⟩ => (60 / 92160 : ℝ) * s ^ 7
  | ⟨23, _⟩ => (44 / 92160 : ℝ) * s ^ 7
  | ⟨24, _⟩ => (6 / 92160 : ℝ) * s ^ 7
  | ⟨25, _⟩ => (20 / 92160 : ℝ) * s ^ 7
  | ⟨26, _⟩ => (32 / 92160 : ℝ) * s ^ 7
  | ⟨27, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨28, _⟩ => (112 / 92160 : ℝ) * s ^ 7
  | ⟨29, _⟩ => (28 / 92160 : ℝ) * s ^ 7
  | ⟨30, _⟩ => (20 / 92160 : ℝ) * s ^ 7
  | ⟨31, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨32, _⟩ => (20 / 92160 : ℝ) * s ^ 7
  | ⟨33, _⟩ => (7 / 92160 : ℝ) * s ^ 7
  | ⟨34, _⟩ => (6 / 92160 : ℝ) * s ^ 7
  | ⟨35, _⟩ => (6 / 92160 : ℝ) * s ^ 7
  | ⟨36, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨37, _⟩ => (30 / 92160 : ℝ) * s ^ 7
  | ⟨38, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨39, _⟩ => (24 / 92160 : ℝ) * s ^ 7
  | ⟨40, _⟩ => (14 / 92160 : ℝ) * s ^ 7
  | ⟨41, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨42, _⟩ => (20 / 92160 : ℝ) * s ^ 7
  | ⟨43, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨44, _⟩ => (18 / 92160 : ℝ) * s ^ 7
  | ⟨45, _⟩ => (45 / 92160 : ℝ) * s ^ 7
  | ⟨46, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨47, _⟩ => (50 / 92160 : ℝ) * s ^ 7
  | ⟨48, _⟩ => (80 / 92160 : ℝ) * s ^ 7
  | ⟨49, _⟩ => (6 / 92160 : ℝ) * s ^ 7
  | ⟨50, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨51, _⟩ => (30 / 92160 : ℝ) * s ^ 7
  | ⟨52, _⟩ => (96 / 92160 : ℝ) * s ^ 7
  | ⟨53, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨54, _⟩ => (40 / 92160 : ℝ) * s ^ 7
  | ⟨55, _⟩ => (14 / 92160 : ℝ) * s ^ 7
  | ⟨56, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨57, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨58, _⟩ => (7 / 92160 : ℝ) * s ^ 7
  | ⟨59, _⟩ => (80 / 92160 : ℝ) * s ^ 7
  | ⟨60, _⟩ => (44 / 92160 : ℝ) * s ^ 7
  | ⟨61, _⟩ => (40 / 92160 : ℝ) * s ^ 7
  | ⟨62, _⟩ => (8 / 92160 : ℝ) * s ^ 7
  | ⟨63, _⟩ => (32 / 92160 : ℝ) * s ^ 7
  | ⟨64, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨65, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨66, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨67, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨68, _⟩ => (10 / 92160 : ℝ) * s ^ 7
  | ⟨69, _⟩ => (24 / 92160 : ℝ) * s ^ 7
  | ⟨70, _⟩ => (40 / 92160 : ℝ) * s ^ 7
  | ⟨71, _⟩ => (40 / 92160 : ℝ) * s ^ 7
  | ⟨72, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨73, _⟩ => (14 / 92160 : ℝ) * s ^ 7
  | ⟨74, _⟩ => (40 / 92160 : ℝ) * s ^ 7
  | ⟨75, _⟩ => (28 / 92160 : ℝ) * s ^ 7
  | ⟨76, _⟩ => (16 / 92160 : ℝ) * s ^ 7
  | ⟨77, _⟩ => (20 / 92160 : ℝ) * s ^ 7
  | ⟨78, _⟩ => (4 / 92160 : ℝ) * s ^ 7
  | ⟨_ + 79, h⟩ => absurd h (by omega)

/-- Per-index upper bound on `‖linResTerm8 i‖`. -/
private noncomputable def linResBound8 (s : ℝ) : Fin 78 → ℝ
  | ⟨0, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨1, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨2, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨3, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨4, _⟩ => (20 / 184320 : ℝ) * s ^ 8
  | ⟨5, _⟩ => (20 / 184320 : ℝ) * s ^ 8
  | ⟨6, _⟩ => (17 / 184320 : ℝ) * s ^ 8
  | ⟨7, _⟩ => (15 / 184320 : ℝ) * s ^ 8
  | ⟨8, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨9, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨10, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨11, _⟩ => (3 / 184320 : ℝ) * s ^ 8
  | ⟨12, _⟩ => (5 / 184320 : ℝ) * s ^ 8
  | ⟨13, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨14, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨15, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨16, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨17, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨18, _⟩ => (5 / 184320 : ℝ) * s ^ 8
  | ⟨19, _⟩ => (5 / 184320 : ℝ) * s ^ 8
  | ⟨20, _⟩ => (30 / 184320 : ℝ) * s ^ 8
  | ⟨21, _⟩ => (35 / 184320 : ℝ) * s ^ 8
  | ⟨22, _⟩ => (10 / 184320 : ℝ) * s ^ 8
  | ⟨23, _⟩ => (5 / 184320 : ℝ) * s ^ 8
  | ⟨24, _⟩ => (10 / 184320 : ℝ) * s ^ 8
  | ⟨25, _⟩ => (43 / 184320 : ℝ) * s ^ 8
  | ⟨26, _⟩ => (35 / 184320 : ℝ) * s ^ 8
  | ⟨27, _⟩ => (22 / 184320 : ℝ) * s ^ 8
  | ⟨28, _⟩ => (15 / 184320 : ℝ) * s ^ 8
  | ⟨29, _⟩ => (16 / 184320 : ℝ) * s ^ 8
  | ⟨30, _⟩ => (12 / 184320 : ℝ) * s ^ 8
  | ⟨31, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨32, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨33, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨34, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨35, _⟩ => (5 / 184320 : ℝ) * s ^ 8
  | ⟨36, _⟩ => (12 / 184320 : ℝ) * s ^ 8
  | ⟨37, _⟩ => (20 / 184320 : ℝ) * s ^ 8
  | ⟨38, _⟩ => (18 / 184320 : ℝ) * s ^ 8
  | ⟨39, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨40, _⟩ => (18 / 184320 : ℝ) * s ^ 8
  | ⟨41, _⟩ => (12 / 184320 : ℝ) * s ^ 8
  | ⟨42, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨43, _⟩ => (10 / 184320 : ℝ) * s ^ 8
  | ⟨44, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨45, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨46, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨47, _⟩ => (40 / 184320 : ℝ) * s ^ 8
  | ⟨48, _⟩ => (43 / 184320 : ℝ) * s ^ 8
  | ⟨49, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨50, _⟩ => (3 / 184320 : ℝ) * s ^ 8
  | ⟨51, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨52, _⟩ => (40 / 184320 : ℝ) * s ^ 8
  | ⟨53, _⟩ => (30 / 184320 : ℝ) * s ^ 8
  | ⟨54, _⟩ => (20 / 184320 : ℝ) * s ^ 8
  | ⟨55, _⟩ => (17 / 184320 : ℝ) * s ^ 8
  | ⟨56, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨57, _⟩ => (18 / 184320 : ℝ) * s ^ 8
  | ⟨58, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨59, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨60, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨61, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨62, _⟩ => (5 / 184320 : ℝ) * s ^ 8
  | ⟨63, _⟩ => (12 / 184320 : ℝ) * s ^ 8
  | ⟨64, _⟩ => (20 / 184320 : ℝ) * s ^ 8
  | ⟨65, _⟩ => (18 / 184320 : ℝ) * s ^ 8
  | ⟨66, _⟩ => (7 / 184320 : ℝ) * s ^ 8
  | ⟨67, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨68, _⟩ => (16 / 184320 : ℝ) * s ^ 8
  | ⟨69, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨70, _⟩ => (12 / 184320 : ℝ) * s ^ 8
  | ⟨71, _⟩ => (12 / 184320 : ℝ) * s ^ 8
  | ⟨72, _⟩ => (20 / 184320 : ℝ) * s ^ 8
  | ⟨73, _⟩ => (22 / 184320 : ℝ) * s ^ 8
  | ⟨74, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨75, _⟩ => (8 / 184320 : ℝ) * s ^ 8
  | ⟨76, _⟩ => (10 / 184320 : ℝ) * s ^ 8
  | ⟨77, _⟩ => (2 / 184320 : ℝ) * s ^ 8
  | ⟨_ + 78, h⟩ => absurd h (by omega)

/-- Per-index upper bound on `‖linResTerm9 i‖`. -/
private noncomputable def linResBound9 (s : ℝ) : Fin 48 → ℝ
  | ⟨0, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨1, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨2, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨3, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨4, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨5, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨6, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨7, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨8, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨9, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨10, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨11, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨12, _⟩ => (11 / 368640 : ℝ) * s ^ 9
  | ⟨13, _⟩ => (11 / 368640 : ℝ) * s ^ 9
  | ⟨14, _⟩ => (15 / 368640 : ℝ) * s ^ 9
  | ⟨15, _⟩ => (16 / 368640 : ℝ) * s ^ 9
  | ⟨16, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨17, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨18, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨19, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨20, _⟩ => (6 / 368640 : ℝ) * s ^ 9
  | ⟨21, _⟩ => (6 / 368640 : ℝ) * s ^ 9
  | ⟨22, _⟩ => (10 / 368640 : ℝ) * s ^ 9
  | ⟨23, _⟩ => (11 / 368640 : ℝ) * s ^ 9
  | ⟨24, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨25, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨26, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨27, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨28, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨29, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨30, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨31, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨32, _⟩ => (10 / 368640 : ℝ) * s ^ 9
  | ⟨33, _⟩ => (10 / 368640 : ℝ) * s ^ 9
  | ⟨34, _⟩ => (14 / 368640 : ℝ) * s ^ 9
  | ⟨35, _⟩ => (15 / 368640 : ℝ) * s ^ 9
  | ⟨36, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨37, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨38, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨39, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨40, _⟩ => (6 / 368640 : ℝ) * s ^ 9
  | ⟨41, _⟩ => (6 / 368640 : ℝ) * s ^ 9
  | ⟨42, _⟩ => (10 / 368640 : ℝ) * s ^ 9
  | ⟨43, _⟩ => (11 / 368640 : ℝ) * s ^ 9
  | ⟨44, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨45, _⟩ => (4 / 368640 : ℝ) * s ^ 9
  | ⟨46, _⟩ => (5 / 368640 : ℝ) * s ^ 9
  | ⟨47, _⟩ => (1 / 368640 : ℝ) * s ^ 9
  | ⟨_ + 48, h⟩ => absurd h (by omega)

/-- Sum form of the deg-7 part of `C5_LinResidual_polynomial`. -/
private noncomputable def C5_LinResidual_deg7 (a b : 𝔸) : 𝔸 :=
  (-7 / 92160 : 𝕂) • (a * a * a * a * b * a * b) +
  (7 / 92160 : 𝕂) • (a * a * a * a * b * b * a) +
  (30 / 92160 : 𝕂) • (a * a * a * b * a * a * b) +
  (-32 / 92160 : 𝕂) • (a * a * a * b * a * b * a) +
  (14 / 92160 : 𝕂) • (a * a * a * b * a * b * b) +
  (2 / 92160 : 𝕂) • (a * a * a * b * b * a * a) +
  (-14 / 92160 : 𝕂) • (a * a * a * b * b * b * a) +
  (-50 / 92160 : 𝕂) • (a * a * b * a * a * a * b) +
  (60 / 92160 : 𝕂) • (a * a * b * a * a * b * a) +
  (-40 / 92160 : 𝕂) • (a * a * b * a * a * b * b) +
  (-12 / 92160 : 𝕂) • (a * a * b * a * b * a * a) +
  (8 / 92160 : 𝕂) • (a * a * b * a * b * a * b) +
  (30 / 92160 : 𝕂) • (a * a * b * a * b * b * a) +
  (-4 / 92160 : 𝕂) • (a * a * b * a * b * b * b) +
  (2 / 92160 : 𝕂) • (a * a * b * b * a * a * a) +
  (-14 / 92160 : 𝕂) • (a * a * b * b * a * a * b) +
  (20 / 92160 : 𝕂) • (a * a * b * b * a * b * a) +
  (-4 / 92160 : 𝕂) • (a * a * b * b * b * a * a) +
  (4 / 92160 : 𝕂) • (a * a * b * b * b * b * a) +
  (45 / 92160 : 𝕂) • (a * b * a * a * a * a * b) +
  (-80 / 92160 : 𝕂) • (a * b * a * a * a * b * a) +
  (10 / 92160 : 𝕂) • (a * b * a * a * a * b * b) +
  (60 / 92160 : 𝕂) • (a * b * a * a * b * a * a) +
  (44 / 92160 : 𝕂) • (a * b * a * a * b * a * b) +
  (6 / 92160 : 𝕂) • (a * b * a * a * b * b * a) +
  (20 / 92160 : 𝕂) • (a * b * a * a * b * b * b) +
  (-32 / 92160 : 𝕂) • (a * b * a * b * a * a * a) +
  (4 / 92160 : 𝕂) • (a * b * a * b * a * a * b) +
  (-112 / 92160 : 𝕂) • (a * b * a * b * a * b * a) +
  (-28 / 92160 : 𝕂) • (a * b * a * b * a * b * b) +
  (20 / 92160 : 𝕂) • (a * b * a * b * b * a * a) +
  (16 / 92160 : 𝕂) • (a * b * a * b * b * a * b) +
  (-20 / 92160 : 𝕂) • (a * b * a * b * b * b * a) +
  (7 / 92160 : 𝕂) • (a * b * b * a * a * a * a) +
  (6 / 92160 : 𝕂) • (a * b * b * a * a * a * b) +
  (6 / 92160 : 𝕂) • (a * b * b * a * a * b * a) +
  (4 / 92160 : 𝕂) • (a * b * b * a * a * b * b) +
  (30 / 92160 : 𝕂) • (a * b * b * a * b * a * a) +
  (-4 / 92160 : 𝕂) • (a * b * b * a * b * a * b) +
  (24 / 92160 : 𝕂) • (a * b * b * a * b * b * a) +
  (-14 / 92160 : 𝕂) • (a * b * b * b * a * a * a) +
  (4 / 92160 : 𝕂) • (a * b * b * b * a * a * b) +
  (-20 / 92160 : 𝕂) • (a * b * b * b * a * b * a) +
  (4 / 92160 : 𝕂) • (a * b * b * b * b * a * a) +
  (-18 / 92160 : 𝕂) • (b * a * a * a * a * a * b) +
  (45 / 92160 : 𝕂) • (b * a * a * a * a * b * a) +
  (16 / 92160 : 𝕂) • (b * a * a * a * a * b * b) +
  (-50 / 92160 : 𝕂) • (b * a * a * a * b * a * a) +
  (-80 / 92160 : 𝕂) • (b * a * a * a * b * a * b) +
  (6 / 92160 : 𝕂) • (b * a * a * a * b * b * a) +
  (-16 / 92160 : 𝕂) • (b * a * a * a * b * b * b) +
  (30 / 92160 : 𝕂) • (b * a * a * b * a * a * a) +
  (96 / 92160 : 𝕂) • (b * a * a * b * a * a * b) +
  (4 / 92160 : 𝕂) • (b * a * a * b * a * b * a) +
  (40 / 92160 : 𝕂) • (b * a * a * b * a * b * b) +
  (-14 / 92160 : 𝕂) • (b * a * a * b * b * a * a) +
  (-16 / 92160 : 𝕂) • (b * a * a * b * b * a * b) +
  (4 / 92160 : 𝕂) • (b * a * a * b * b * b * a) +
  (-7 / 92160 : 𝕂) • (b * a * b * a * a * a * a) +
  (-80 / 92160 : 𝕂) • (b * a * b * a * a * a * b) +
  (44 / 92160 : 𝕂) • (b * a * b * a * a * b * a) +
  (-40 / 92160 : 𝕂) • (b * a * b * a * a * b * b) +
  (8 / 92160 : 𝕂) • (b * a * b * a * b * a * a) +
  (32 / 92160 : 𝕂) • (b * a * b * a * b * a * b) +
  (-4 / 92160 : 𝕂) • (b * a * b * a * b * b * a) +
  (-16 / 92160 : 𝕂) • (b * a * b * b * a * a * b) +
  (16 / 92160 : 𝕂) • (b * a * b * b * a * b * a) +
  (16 / 92160 : 𝕂) • (b * b * a * a * a * a * b) +
  (10 / 92160 : 𝕂) • (b * b * a * a * a * b * a) +
  (24 / 92160 : 𝕂) • (b * b * a * a * a * b * b) +
  (-40 / 92160 : 𝕂) • (b * b * a * a * b * a * a) +
  (-40 / 92160 : 𝕂) • (b * b * a * a * b * a * b) +
  (4 / 92160 : 𝕂) • (b * b * a * a * b * b * a) +
  (14 / 92160 : 𝕂) • (b * b * a * b * a * a * a) +
  (40 / 92160 : 𝕂) • (b * b * a * b * a * a * b) +
  (-28 / 92160 : 𝕂) • (b * b * a * b * a * b * a) +
  (-16 / 92160 : 𝕂) • (b * b * b * a * a * a * b) +
  (20 / 92160 : 𝕂) • (b * b * b * a * a * b * a) +
  (-4 / 92160 : 𝕂) • (b * b * b * a * b * a * a)

/-- Sum form of the deg-8 part of `C5_LinResidual_polynomial`. -/
private noncomputable def C5_LinResidual_deg8 (a b : 𝔸) : 𝔸 :=
  (7 / 184320 : 𝕂) • (a * a * a * b * a * b * a * b) +
  (-7 / 184320 : 𝕂) • (a * a * a * b * a * b * b * a) +
  (-7 / 184320 : 𝕂) • (a * a * a * b * b * a * a * b) +
  (7 / 184320 : 𝕂) • (a * a * a * b * b * a * b * a) +
  (-20 / 184320 : 𝕂) • (a * a * b * a * a * b * a * b) +
  (20 / 184320 : 𝕂) • (a * a * b * a * a * b * b * a) +
  (17 / 184320 : 𝕂) • (a * a * b * a * b * a * a * b) +
  (-15 / 184320 : 𝕂) • (a * a * b * a * b * a * b * a) +
  (-2 / 184320 : 𝕂) • (a * a * b * a * b * a * b * b) +
  (-2 / 184320 : 𝕂) • (a * a * b * a * b * b * a * a) +
  (2 / 184320 : 𝕂) • (a * a * b * a * b * b * b * a) +
  (3 / 184320 : 𝕂) • (a * a * b * b * a * a * a * b) +
  (-5 / 184320 : 𝕂) • (a * a * b * b * a * a * b * a) +
  (2 / 184320 : 𝕂) • (a * a * b * b * a * a * b * b) +
  (2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * a) +
  (-2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * b) +
  (2 / 184320 : 𝕂) • (a * a * b * b * b * a * a * b) +
  (-2 / 184320 : 𝕂) • (a * a * b * b * b * a * b * a) +
  (5 / 184320 : 𝕂) • (a * b * a * a * a * b * a * b) +
  (-5 / 184320 : 𝕂) • (a * b * a * a * a * b * b * a) +
  (30 / 184320 : 𝕂) • (a * b * a * a * b * a * a * b) +
  (-35 / 184320 : 𝕂) • (a * b * a * a * b * a * b * a) +
  (10 / 184320 : 𝕂) • (a * b * a * a * b * a * b * b) +
  (5 / 184320 : 𝕂) • (a * b * a * a * b * b * a * a) +
  (-10 / 184320 : 𝕂) • (a * b * a * a * b * b * b * a) +
  (-43 / 184320 : 𝕂) • (a * b * a * b * a * a * a * b) +
  (35 / 184320 : 𝕂) • (a * b * a * b * a * a * b * a) +
  (-22 / 184320 : 𝕂) • (a * b * a * b * a * a * b * b) +
  (15 / 184320 : 𝕂) • (a * b * a * b * a * b * a * a) +
  (16 / 184320 : 𝕂) • (a * b * a * b * a * b * a * b) +
  (12 / 184320 : 𝕂) • (a * b * a * b * a * b * b * a) +
  (-7 / 184320 : 𝕂) • (a * b * a * b * b * a * a * a) +
  (-8 / 184320 : 𝕂) • (a * b * a * b * b * a * a * b) +
  (2 / 184320 : 𝕂) • (a * b * a * b * b * b * a * a) +
  (8 / 184320 : 𝕂) • (a * b * b * a * a * a * a * b) +
  (5 / 184320 : 𝕂) • (a * b * b * a * a * a * b * a) +
  (12 / 184320 : 𝕂) • (a * b * b * a * a * a * b * b) +
  (-20 / 184320 : 𝕂) • (a * b * b * a * a * b * a * a) +
  (-18 / 184320 : 𝕂) • (a * b * b * a * a * b * a * b) +
  (7 / 184320 : 𝕂) • (a * b * b * a * b * a * a * a) +
  (18 / 184320 : 𝕂) • (a * b * b * a * b * a * a * b) +
  (-12 / 184320 : 𝕂) • (a * b * b * a * b * a * b * a) +
  (-8 / 184320 : 𝕂) • (a * b * b * b * a * a * a * b) +
  (10 / 184320 : 𝕂) • (a * b * b * b * a * a * b * a) +
  (-2 / 184320 : 𝕂) • (a * b * b * b * a * b * a * a) +
  (8 / 184320 : 𝕂) • (b * a * a * a * a * b * a * b) +
  (-8 / 184320 : 𝕂) • (b * a * a * a * a * b * b * a) +
  (-40 / 184320 : 𝕂) • (b * a * a * a * b * a * a * b) +
  (43 / 184320 : 𝕂) • (b * a * a * a * b * a * b * a) +
  (-8 / 184320 : 𝕂) • (b * a * a * a * b * a * b * b) +
  (-3 / 184320 : 𝕂) • (b * a * a * a * b * b * a * a) +
  (8 / 184320 : 𝕂) • (b * a * a * a * b * b * b * a) +
  (40 / 184320 : 𝕂) • (b * a * a * b * a * a * a * b) +
  (-30 / 184320 : 𝕂) • (b * a * a * b * a * a * b * a) +
  (20 / 184320 : 𝕂) • (b * a * a * b * a * a * b * b) +
  (-17 / 184320 : 𝕂) • (b * a * a * b * a * b * a * a) +
  (-8 / 184320 : 𝕂) • (b * a * a * b * a * b * a * b) +
  (-18 / 184320 : 𝕂) • (b * a * a * b * a * b * b * a) +
  (7 / 184320 : 𝕂) • (b * a * a * b * b * a * a * a) +
  (8 / 184320 : 𝕂) • (b * a * a * b * b * a * b * a) +
  (-2 / 184320 : 𝕂) • (b * a * a * b * b * b * a * a) +
  (-8 / 184320 : 𝕂) • (b * a * b * a * a * a * a * b) +
  (-5 / 184320 : 𝕂) • (b * a * b * a * a * a * b * a) +
  (-12 / 184320 : 𝕂) • (b * a * b * a * a * a * b * b) +
  (20 / 184320 : 𝕂) • (b * a * b * a * a * b * a * a) +
  (18 / 184320 : 𝕂) • (b * a * b * a * a * b * b * a) +
  (-7 / 184320 : 𝕂) • (b * a * b * a * b * a * a * a) +
  (8 / 184320 : 𝕂) • (b * a * b * a * b * a * a * b) +
  (-16 / 184320 : 𝕂) • (b * a * b * a * b * a * b * a) +
  (2 / 184320 : 𝕂) • (b * a * b * a * b * b * a * a) +
  (12 / 184320 : 𝕂) • (b * b * a * a * a * b * a * b) +
  (-12 / 184320 : 𝕂) • (b * b * a * a * a * b * b * a) +
  (-20 / 184320 : 𝕂) • (b * b * a * a * b * a * a * b) +
  (22 / 184320 : 𝕂) • (b * b * a * a * b * a * b * a) +
  (-2 / 184320 : 𝕂) • (b * b * a * a * b * b * a * a) +
  (8 / 184320 : 𝕂) • (b * b * a * b * a * a * a * b) +
  (-10 / 184320 : 𝕂) • (b * b * a * b * a * a * b * a) +
  (2 / 184320 : 𝕂) • (b * b * a * b * a * b * a * a)

/-- Sum form of the deg-9 part of `C5_LinResidual_polynomial`. -/
private noncomputable def C5_LinResidual_deg9 (a b : 𝔸) : 𝔸 :=
  (-1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * a * b) +
  (1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * b * a) +
  (1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * a * b) +
  (-1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * b * a) +
  (1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * a * b) +
  (-1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * b * a) +
  (-1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * a * b) +
  (1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * b * a) +
  (5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * a * b) +
  (-5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * b * a) +
  (-5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * a * b) +
  (5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * b * a) +
  (-11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * a * b) +
  (11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * b * a) +
  (15 / 368640 : 𝕂) • (a * b * a * b * a * b * a * a * b) +
  (-16 / 368640 : 𝕂) • (a * b * a * b * a * b * a * b * a) +
  (1 / 368640 : 𝕂) • (a * b * a * b * a * b * b * a * a) +
  (-4 / 368640 : 𝕂) • (a * b * a * b * b * a * a * a * b) +
  (5 / 368640 : 𝕂) • (a * b * a * b * b * a * a * b * a) +
  (-1 / 368640 : 𝕂) • (a * b * a * b * b * a * b * a * a) +
  (6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * a * b) +
  (-6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * b * a) +
  (-10 / 368640 : 𝕂) • (a * b * b * a * a * b * a * a * b) +
  (11 / 368640 : 𝕂) • (a * b * b * a * a * b * a * b * a) +
  (-1 / 368640 : 𝕂) • (a * b * b * a * a * b * b * a * a) +
  (4 / 368640 : 𝕂) • (a * b * b * a * b * a * a * a * b) +
  (-5 / 368640 : 𝕂) • (a * b * b * a * b * a * a * b * a) +
  (1 / 368640 : 𝕂) • (a * b * b * a * b * a * b * a * a) +
  (-4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * a * b) +
  (4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * b * a) +
  (4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * a * b) +
  (-4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * b * a) +
  (10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * a * b) +
  (-10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * b * a) +
  (-14 / 368640 : 𝕂) • (b * a * a * b * a * b * a * a * b) +
  (15 / 368640 : 𝕂) • (b * a * a * b * a * b * a * b * a) +
  (-1 / 368640 : 𝕂) • (b * a * a * b * a * b * b * a * a) +
  (4 / 368640 : 𝕂) • (b * a * a * b * b * a * a * a * b) +
  (-5 / 368640 : 𝕂) • (b * a * a * b * b * a * a * b * a) +
  (1 / 368640 : 𝕂) • (b * a * a * b * b * a * b * a * a) +
  (-6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * a * b) +
  (6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * b * a) +
  (10 / 368640 : 𝕂) • (b * a * b * a * a * b * a * a * b) +
  (-11 / 368640 : 𝕂) • (b * a * b * a * a * b * a * b * a) +
  (1 / 368640 : 𝕂) • (b * a * b * a * a * b * b * a * a) +
  (-4 / 368640 : 𝕂) • (b * a * b * a * b * a * a * a * b) +
  (5 / 368640 : 𝕂) • (b * a * b * a * b * a * a * b * a) +
  (-1 / 368640 : 𝕂) • (b * a * b * a * b * a * b * a * a)

-- Decomposition of the polynomial into its per-degree parts.
set_option maxHeartbeats 32000000 in
private lemma C5_LinResidual_polynomial_eq_parts (a b : 𝔸) :
    C5_LinResidual_polynomial 𝕂 a b =
      C5_LinResidual_deg7 (𝕂 := 𝕂) a b + C5_LinResidual_deg8 (𝕂 := 𝕂) a b + C5_LinResidual_deg9 (𝕂 := 𝕂) a b := by
  unfold C5_LinResidual_polynomial C5_LinResidual_deg7 C5_LinResidual_deg8 C5_LinResidual_deg9
  abel

-- The deg-7 part expressed as a `Finset.sum`.
set_option maxHeartbeats 15800000 in
private lemma C5_LinResidual_deg7_eq_sum (a b : 𝔸) :
    C5_LinResidual_deg7 (𝕂 := 𝕂) a b = ∑ i : Fin 79, linResTerm7 (𝕂 := 𝕂) a b i := by
  unfold C5_LinResidual_deg7
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, linResTerm7, add_zero]
  abel

-- The deg-8 part expressed as a `Finset.sum`.
set_option maxHeartbeats 15600000 in
private lemma C5_LinResidual_deg8_eq_sum (a b : 𝔸) :
    C5_LinResidual_deg8 (𝕂 := 𝕂) a b = ∑ i : Fin 78, linResTerm8 (𝕂 := 𝕂) a b i := by
  unfold C5_LinResidual_deg8
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, linResTerm8, add_zero]
  abel

-- The deg-9 part expressed as a `Finset.sum`.
set_option maxHeartbeats 9600000 in
private lemma C5_LinResidual_deg9_eq_sum (a b : 𝔸) :
    C5_LinResidual_deg9 (𝕂 := 𝕂) a b = ∑ i : Fin 48, linResTerm9 (𝕂 := 𝕂) a b i := by
  unfold C5_LinResidual_deg9
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, linResTerm9, add_zero]
  abel

-- Per-index norm bound for `linResTerm7`.
set_option maxHeartbeats 16000000 in
private lemma linResTerm7_norm_le
    (a b : 𝔸) (s : ℝ) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :
    ∀ i : Fin 79, ‖linResTerm7 (𝕂 := 𝕂) a b i‖ ≤ linResBound7 s i := fun i =>
  match i with
  | ⟨0, _⟩ =>
    show ‖(-7 / 92160 : 𝕂) • (a * a * a * a * b * a * b)‖ ≤ (7 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-7 / 92160 : 𝕂) (7 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a a b a b s ha ha ha ha hb ha hb (by positivity) hs
  | ⟨1, _⟩ =>
    show ‖(7 / 92160 : 𝕂) • (a * a * a * a * b * b * a)‖ ≤ (7 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (7 / 92160 : 𝕂) (7 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a a b b a s ha ha ha ha hb hb ha (by positivity) hs
  | ⟨2, _⟩ =>
    show ‖(30 / 92160 : 𝕂) • (a * a * a * b * a * a * b)‖ ≤ (30 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (30 / 92160 : 𝕂) (30 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b a a b s ha ha ha hb ha ha hb (by positivity) hs
  | ⟨3, _⟩ =>
    show ‖(-32 / 92160 : 𝕂) • (a * a * a * b * a * b * a)‖ ≤ (32 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-32 / 92160 : 𝕂) (32 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b a b a s ha ha ha hb ha hb ha (by positivity) hs
  | ⟨4, _⟩ =>
    show ‖(14 / 92160 : 𝕂) • (a * a * a * b * a * b * b)‖ ≤ (14 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (14 / 92160 : 𝕂) (14 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b a b b s ha ha ha hb ha hb hb (by positivity) hs
  | ⟨5, _⟩ =>
    show ‖(2 / 92160 : 𝕂) • (a * a * a * b * b * a * a)‖ ≤ (2 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (2 / 92160 : 𝕂) (2 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b b a a s ha ha ha hb hb ha ha (by positivity) hs
  | ⟨6, _⟩ =>
    show ‖(-14 / 92160 : 𝕂) • (a * a * a * b * b * b * a)‖ ≤ (14 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-14 / 92160 : 𝕂) (14 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b b b a s ha ha ha hb hb hb ha (by positivity) hs
  | ⟨7, _⟩ =>
    show ‖(-50 / 92160 : 𝕂) • (a * a * b * a * a * a * b)‖ ≤ (50 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-50 / 92160 : 𝕂) (50 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a a a b s ha ha hb ha ha ha hb (by positivity) hs
  | ⟨8, _⟩ =>
    show ‖(60 / 92160 : 𝕂) • (a * a * b * a * a * b * a)‖ ≤ (60 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (60 / 92160 : 𝕂) (60 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a a b a s ha ha hb ha ha hb ha (by positivity) hs
  | ⟨9, _⟩ =>
    show ‖(-40 / 92160 : 𝕂) • (a * a * b * a * a * b * b)‖ ≤ (40 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-40 / 92160 : 𝕂) (40 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a a b b s ha ha hb ha ha hb hb (by positivity) hs
  | ⟨10, _⟩ =>
    show ‖(-12 / 92160 : 𝕂) • (a * a * b * a * b * a * a)‖ ≤ (12 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-12 / 92160 : 𝕂) (12 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b a a s ha ha hb ha hb ha ha (by positivity) hs
  | ⟨11, _⟩ =>
    show ‖(8 / 92160 : 𝕂) • (a * a * b * a * b * a * b)‖ ≤ (8 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (8 / 92160 : 𝕂) (8 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b a b s ha ha hb ha hb ha hb (by positivity) hs
  | ⟨12, _⟩ =>
    show ‖(30 / 92160 : 𝕂) • (a * a * b * a * b * b * a)‖ ≤ (30 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (30 / 92160 : 𝕂) (30 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b b a s ha ha hb ha hb hb ha (by positivity) hs
  | ⟨13, _⟩ =>
    show ‖(-4 / 92160 : 𝕂) • (a * a * b * a * b * b * b)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b b b s ha ha hb ha hb hb hb (by positivity) hs
  | ⟨14, _⟩ =>
    show ‖(2 / 92160 : 𝕂) • (a * a * b * b * a * a * a)‖ ≤ (2 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (2 / 92160 : 𝕂) (2 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a a a s ha ha hb hb ha ha ha (by positivity) hs
  | ⟨15, _⟩ =>
    show ‖(-14 / 92160 : 𝕂) • (a * a * b * b * a * a * b)‖ ≤ (14 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-14 / 92160 : 𝕂) (14 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a a b s ha ha hb hb ha ha hb (by positivity) hs
  | ⟨16, _⟩ =>
    show ‖(20 / 92160 : 𝕂) • (a * a * b * b * a * b * a)‖ ≤ (20 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (20 / 92160 : 𝕂) (20 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a b a s ha ha hb hb ha hb ha (by positivity) hs
  | ⟨17, _⟩ =>
    show ‖(-4 / 92160 : 𝕂) • (a * a * b * b * b * a * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b b a a s ha ha hb hb hb ha ha (by positivity) hs
  | ⟨18, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (a * a * b * b * b * b * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b b b a s ha ha hb hb hb hb ha (by positivity) hs
  | ⟨19, _⟩ =>
    show ‖(45 / 92160 : 𝕂) • (a * b * a * a * a * a * b)‖ ≤ (45 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (45 / 92160 : 𝕂) (45 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a a a b s ha hb ha ha ha ha hb (by positivity) hs
  | ⟨20, _⟩ =>
    show ‖(-80 / 92160 : 𝕂) • (a * b * a * a * a * b * a)‖ ≤ (80 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-80 / 92160 : 𝕂) (80 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a a b a s ha hb ha ha ha hb ha (by positivity) hs
  | ⟨21, _⟩ =>
    show ‖(10 / 92160 : 𝕂) • (a * b * a * a * a * b * b)‖ ≤ (10 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (10 / 92160 : 𝕂) (10 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a a b b s ha hb ha ha ha hb hb (by positivity) hs
  | ⟨22, _⟩ =>
    show ‖(60 / 92160 : 𝕂) • (a * b * a * a * b * a * a)‖ ≤ (60 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (60 / 92160 : 𝕂) (60 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b a a s ha hb ha ha hb ha ha (by positivity) hs
  | ⟨23, _⟩ =>
    show ‖(44 / 92160 : 𝕂) • (a * b * a * a * b * a * b)‖ ≤ (44 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (44 / 92160 : 𝕂) (44 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b a b s ha hb ha ha hb ha hb (by positivity) hs
  | ⟨24, _⟩ =>
    show ‖(6 / 92160 : 𝕂) • (a * b * a * a * b * b * a)‖ ≤ (6 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (6 / 92160 : 𝕂) (6 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b b a s ha hb ha ha hb hb ha (by positivity) hs
  | ⟨25, _⟩ =>
    show ‖(20 / 92160 : 𝕂) • (a * b * a * a * b * b * b)‖ ≤ (20 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (20 / 92160 : 𝕂) (20 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b b b s ha hb ha ha hb hb hb (by positivity) hs
  | ⟨26, _⟩ =>
    show ‖(-32 / 92160 : 𝕂) • (a * b * a * b * a * a * a)‖ ≤ (32 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-32 / 92160 : 𝕂) (32 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a a a s ha hb ha hb ha ha ha (by positivity) hs
  | ⟨27, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (a * b * a * b * a * a * b)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a a b s ha hb ha hb ha ha hb (by positivity) hs
  | ⟨28, _⟩ =>
    show ‖(-112 / 92160 : 𝕂) • (a * b * a * b * a * b * a)‖ ≤ (112 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-112 / 92160 : 𝕂) (112 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b a s ha hb ha hb ha hb ha (by positivity) hs
  | ⟨29, _⟩ =>
    show ‖(-28 / 92160 : 𝕂) • (a * b * a * b * a * b * b)‖ ≤ (28 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-28 / 92160 : 𝕂) (28 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b b s ha hb ha hb ha hb hb (by positivity) hs
  | ⟨30, _⟩ =>
    show ‖(20 / 92160 : 𝕂) • (a * b * a * b * b * a * a)‖ ≤ (20 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (20 / 92160 : 𝕂) (20 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b a a s ha hb ha hb hb ha ha (by positivity) hs
  | ⟨31, _⟩ =>
    show ‖(16 / 92160 : 𝕂) • (a * b * a * b * b * a * b)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b a b s ha hb ha hb hb ha hb (by positivity) hs
  | ⟨32, _⟩ =>
    show ‖(-20 / 92160 : 𝕂) • (a * b * a * b * b * b * a)‖ ≤ (20 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-20 / 92160 : 𝕂) (20 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b b a s ha hb ha hb hb hb ha (by positivity) hs
  | ⟨33, _⟩ =>
    show ‖(7 / 92160 : 𝕂) • (a * b * b * a * a * a * a)‖ ≤ (7 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (7 / 92160 : 𝕂) (7 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a a a s ha hb hb ha ha ha ha (by positivity) hs
  | ⟨34, _⟩ =>
    show ‖(6 / 92160 : 𝕂) • (a * b * b * a * a * a * b)‖ ≤ (6 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (6 / 92160 : 𝕂) (6 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a a b s ha hb hb ha ha ha hb (by positivity) hs
  | ⟨35, _⟩ =>
    show ‖(6 / 92160 : 𝕂) • (a * b * b * a * a * b * a)‖ ≤ (6 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (6 / 92160 : 𝕂) (6 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a b a s ha hb hb ha ha hb ha (by positivity) hs
  | ⟨36, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (a * b * b * a * a * b * b)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a b b s ha hb hb ha ha hb hb (by positivity) hs
  | ⟨37, _⟩ =>
    show ‖(30 / 92160 : 𝕂) • (a * b * b * a * b * a * a)‖ ≤ (30 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (30 / 92160 : 𝕂) (30 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a a s ha hb hb ha hb ha ha (by positivity) hs
  | ⟨38, _⟩ =>
    show ‖(-4 / 92160 : 𝕂) • (a * b * b * a * b * a * b)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a b s ha hb hb ha hb ha hb (by positivity) hs
  | ⟨39, _⟩ =>
    show ‖(24 / 92160 : 𝕂) • (a * b * b * a * b * b * a)‖ ≤ (24 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (24 / 92160 : 𝕂) (24 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b b a s ha hb hb ha hb hb ha (by positivity) hs
  | ⟨40, _⟩ =>
    show ‖(-14 / 92160 : 𝕂) • (a * b * b * b * a * a * a)‖ ≤ (14 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-14 / 92160 : 𝕂) (14 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b b a a a s ha hb hb hb ha ha ha (by positivity) hs
  | ⟨41, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (a * b * b * b * a * a * b)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b b a a b s ha hb hb hb ha ha hb (by positivity) hs
  | ⟨42, _⟩ =>
    show ‖(-20 / 92160 : 𝕂) • (a * b * b * b * a * b * a)‖ ≤ (20 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-20 / 92160 : 𝕂) (20 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b b a b a s ha hb hb hb ha hb ha (by positivity) hs
  | ⟨43, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (a * b * b * b * b * a * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b b b a a s ha hb hb hb hb ha ha (by positivity) hs
  | ⟨44, _⟩ =>
    show ‖(-18 / 92160 : 𝕂) • (b * a * a * a * a * a * b)‖ ≤ (18 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-18 / 92160 : 𝕂) (18 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a a a b s hb ha ha ha ha ha hb (by positivity) hs
  | ⟨45, _⟩ =>
    show ‖(45 / 92160 : 𝕂) • (b * a * a * a * a * b * a)‖ ≤ (45 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (45 / 92160 : 𝕂) (45 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a a b a s hb ha ha ha ha hb ha (by positivity) hs
  | ⟨46, _⟩ =>
    show ‖(16 / 92160 : 𝕂) • (b * a * a * a * a * b * b)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a a b b s hb ha ha ha ha hb hb (by positivity) hs
  | ⟨47, _⟩ =>
    show ‖(-50 / 92160 : 𝕂) • (b * a * a * a * b * a * a)‖ ≤ (50 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-50 / 92160 : 𝕂) (50 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b a a s hb ha ha ha hb ha ha (by positivity) hs
  | ⟨48, _⟩ =>
    show ‖(-80 / 92160 : 𝕂) • (b * a * a * a * b * a * b)‖ ≤ (80 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-80 / 92160 : 𝕂) (80 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b a b s hb ha ha ha hb ha hb (by positivity) hs
  | ⟨49, _⟩ =>
    show ‖(6 / 92160 : 𝕂) • (b * a * a * a * b * b * a)‖ ≤ (6 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (6 / 92160 : 𝕂) (6 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b b a s hb ha ha ha hb hb ha (by positivity) hs
  | ⟨50, _⟩ =>
    show ‖(-16 / 92160 : 𝕂) • (b * a * a * a * b * b * b)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b b b s hb ha ha ha hb hb hb (by positivity) hs
  | ⟨51, _⟩ =>
    show ‖(30 / 92160 : 𝕂) • (b * a * a * b * a * a * a)‖ ≤ (30 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (30 / 92160 : 𝕂) (30 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a a a s hb ha ha hb ha ha ha (by positivity) hs
  | ⟨52, _⟩ =>
    show ‖(96 / 92160 : 𝕂) • (b * a * a * b * a * a * b)‖ ≤ (96 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (96 / 92160 : 𝕂) (96 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a a b s hb ha ha hb ha ha hb (by positivity) hs
  | ⟨53, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (b * a * a * b * a * b * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b a s hb ha ha hb ha hb ha (by positivity) hs
  | ⟨54, _⟩ =>
    show ‖(40 / 92160 : 𝕂) • (b * a * a * b * a * b * b)‖ ≤ (40 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (40 / 92160 : 𝕂) (40 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b b s hb ha ha hb ha hb hb (by positivity) hs
  | ⟨55, _⟩ =>
    show ‖(-14 / 92160 : 𝕂) • (b * a * a * b * b * a * a)‖ ≤ (14 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-14 / 92160 : 𝕂) (14 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b a a s hb ha ha hb hb ha ha (by positivity) hs
  | ⟨56, _⟩ =>
    show ‖(-16 / 92160 : 𝕂) • (b * a * a * b * b * a * b)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b a b s hb ha ha hb hb ha hb (by positivity) hs
  | ⟨57, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (b * a * a * b * b * b * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b b a s hb ha ha hb hb hb ha (by positivity) hs
  | ⟨58, _⟩ =>
    show ‖(-7 / 92160 : 𝕂) • (b * a * b * a * a * a * a)‖ ≤ (7 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-7 / 92160 : 𝕂) (7 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a a a s hb ha hb ha ha ha ha (by positivity) hs
  | ⟨59, _⟩ =>
    show ‖(-80 / 92160 : 𝕂) • (b * a * b * a * a * a * b)‖ ≤ (80 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-80 / 92160 : 𝕂) (80 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a a b s hb ha hb ha ha ha hb (by positivity) hs
  | ⟨60, _⟩ =>
    show ‖(44 / 92160 : 𝕂) • (b * a * b * a * a * b * a)‖ ≤ (44 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (44 / 92160 : 𝕂) (44 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a b a s hb ha hb ha ha hb ha (by positivity) hs
  | ⟨61, _⟩ =>
    show ‖(-40 / 92160 : 𝕂) • (b * a * b * a * a * b * b)‖ ≤ (40 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-40 / 92160 : 𝕂) (40 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a b b s hb ha hb ha ha hb hb (by positivity) hs
  | ⟨62, _⟩ =>
    show ‖(8 / 92160 : 𝕂) • (b * a * b * a * b * a * a)‖ ≤ (8 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (8 / 92160 : 𝕂) (8 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a a s hb ha hb ha hb ha ha (by positivity) hs
  | ⟨63, _⟩ =>
    show ‖(32 / 92160 : 𝕂) • (b * a * b * a * b * a * b)‖ ≤ (32 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (32 / 92160 : 𝕂) (32 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a b s hb ha hb ha hb ha hb (by positivity) hs
  | ⟨64, _⟩ =>
    show ‖(-4 / 92160 : 𝕂) • (b * a * b * a * b * b * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b b a s hb ha hb ha hb hb ha (by positivity) hs
  | ⟨65, _⟩ =>
    show ‖(-16 / 92160 : 𝕂) • (b * a * b * b * a * a * b)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b b a a b s hb ha hb hb ha ha hb (by positivity) hs
  | ⟨66, _⟩ =>
    show ‖(16 / 92160 : 𝕂) • (b * a * b * b * a * b * a)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b b a b a s hb ha hb hb ha hb ha (by positivity) hs
  | ⟨67, _⟩ =>
    show ‖(16 / 92160 : 𝕂) • (b * b * a * a * a * a * b)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a a a b s hb hb ha ha ha ha hb (by positivity) hs
  | ⟨68, _⟩ =>
    show ‖(10 / 92160 : 𝕂) • (b * b * a * a * a * b * a)‖ ≤ (10 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (10 / 92160 : 𝕂) (10 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a a b a s hb hb ha ha ha hb ha (by positivity) hs
  | ⟨69, _⟩ =>
    show ‖(24 / 92160 : 𝕂) • (b * b * a * a * a * b * b)‖ ≤ (24 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (24 / 92160 : 𝕂) (24 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a a b b s hb hb ha ha ha hb hb (by positivity) hs
  | ⟨70, _⟩ =>
    show ‖(-40 / 92160 : 𝕂) • (b * b * a * a * b * a * a)‖ ≤ (40 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-40 / 92160 : 𝕂) (40 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a b a a s hb hb ha ha hb ha ha (by positivity) hs
  | ⟨71, _⟩ =>
    show ‖(-40 / 92160 : 𝕂) • (b * b * a * a * b * a * b)‖ ≤ (40 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-40 / 92160 : 𝕂) (40 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a b a b s hb hb ha ha hb ha hb (by positivity) hs
  | ⟨72, _⟩ =>
    show ‖(4 / 92160 : 𝕂) • (b * b * a * a * b * b * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a b b a s hb hb ha ha hb hb ha (by positivity) hs
  | ⟨73, _⟩ =>
    show ‖(14 / 92160 : 𝕂) • (b * b * a * b * a * a * a)‖ ≤ (14 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (14 / 92160 : 𝕂) (14 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a b a a a s hb hb ha hb ha ha ha (by positivity) hs
  | ⟨74, _⟩ =>
    show ‖(40 / 92160 : 𝕂) • (b * b * a * b * a * a * b)‖ ≤ (40 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (40 / 92160 : 𝕂) (40 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a b a a b s hb hb ha hb ha ha hb (by positivity) hs
  | ⟨75, _⟩ =>
    show ‖(-28 / 92160 : 𝕂) • (b * b * a * b * a * b * a)‖ ≤ (28 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-28 / 92160 : 𝕂) (28 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a b a b a s hb hb ha hb ha hb ha (by positivity) hs
  | ⟨76, _⟩ =>
    show ‖(-16 / 92160 : 𝕂) • (b * b * b * a * a * a * b)‖ ≤ (16 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-16 / 92160 : 𝕂) (16 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b b a a a b s hb hb hb ha ha ha hb (by positivity) hs
  | ⟨77, _⟩ =>
    show ‖(20 / 92160 : 𝕂) • (b * b * b * a * a * b * a)‖ ≤ (20 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (20 / 92160 : 𝕂) (20 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b b a a b a s hb hb hb ha ha hb ha (by positivity) hs
  | ⟨78, _⟩ =>
    show ‖(-4 / 92160 : 𝕂) • (b * b * b * a * b * a * a)‖ ≤ (4 / 92160 : ℝ) * s ^ 7 from
      deg7_smul_word_le (-4 / 92160 : 𝕂) (4 / 92160 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b b a b a a s hb hb hb ha hb ha ha (by positivity) hs
  | ⟨_ + 79, h⟩ => absurd h (by omega)

-- Per-index norm bound for `linResTerm8`.
set_option maxHeartbeats 16000000 in
private lemma linResTerm8_norm_le
    (a b : 𝔸) (s : ℝ) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :
    ∀ i : Fin 78, ‖linResTerm8 (𝕂 := 𝕂) a b i‖ ≤ linResBound8 s i := fun i =>
  match i with
  | ⟨0, _⟩ =>
    show ‖(7 / 184320 : 𝕂) • (a * a * a * b * a * b * a * b)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b a b a b s ha ha ha hb ha hb ha hb (by positivity) hs
  | ⟨1, _⟩ =>
    show ‖(-7 / 184320 : 𝕂) • (a * a * a * b * a * b * b * a)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b a b b a s ha ha ha hb ha hb hb ha (by positivity) hs
  | ⟨2, _⟩ =>
    show ‖(-7 / 184320 : 𝕂) • (a * a * a * b * b * a * a * b)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b b a a b s ha ha ha hb hb ha ha hb (by positivity) hs
  | ⟨3, _⟩ =>
    show ‖(7 / 184320 : 𝕂) • (a * a * a * b * b * a * b * a)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a a b b a b a s ha ha ha hb hb ha hb ha (by positivity) hs
  | ⟨4, _⟩ =>
    show ‖(-20 / 184320 : 𝕂) • (a * a * b * a * a * b * a * b)‖ ≤ (20 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-20 / 184320 : 𝕂) (20 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a a b a b s ha ha hb ha ha hb ha hb (by positivity) hs
  | ⟨5, _⟩ =>
    show ‖(20 / 184320 : 𝕂) • (a * a * b * a * a * b * b * a)‖ ≤ (20 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (20 / 184320 : 𝕂) (20 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a a b b a s ha ha hb ha ha hb hb ha (by positivity) hs
  | ⟨6, _⟩ =>
    show ‖(17 / 184320 : 𝕂) • (a * a * b * a * b * a * a * b)‖ ≤ (17 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (17 / 184320 : 𝕂) (17 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b a a b s ha ha hb ha hb ha ha hb (by positivity) hs
  | ⟨7, _⟩ =>
    show ‖(-15 / 184320 : 𝕂) • (a * a * b * a * b * a * b * a)‖ ≤ (15 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-15 / 184320 : 𝕂) (15 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b a b a s ha ha hb ha hb ha hb ha (by positivity) hs
  | ⟨8, _⟩ =>
    show ‖(-2 / 184320 : 𝕂) • (a * a * b * a * b * a * b * b)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b a b b s ha ha hb ha hb ha hb hb (by positivity) hs
  | ⟨9, _⟩ =>
    show ‖(-2 / 184320 : 𝕂) • (a * a * b * a * b * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b b a a s ha ha hb ha hb hb ha ha (by positivity) hs
  | ⟨10, _⟩ =>
    show ‖(2 / 184320 : 𝕂) • (a * a * b * a * b * b * b * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b b b a s ha ha hb ha hb hb hb ha (by positivity) hs
  | ⟨11, _⟩ =>
    show ‖(3 / 184320 : 𝕂) • (a * a * b * b * a * a * a * b)‖ ≤ (3 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (3 / 184320 : 𝕂) (3 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a a a b s ha ha hb hb ha ha ha hb (by positivity) hs
  | ⟨12, _⟩ =>
    show ‖(-5 / 184320 : 𝕂) • (a * a * b * b * a * a * b * a)‖ ≤ (5 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-5 / 184320 : 𝕂) (5 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a a b a s ha ha hb hb ha ha hb ha (by positivity) hs
  | ⟨13, _⟩ =>
    show ‖(2 / 184320 : 𝕂) • (a * a * b * b * a * a * b * b)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a a b b s ha ha hb hb ha ha hb hb (by positivity) hs
  | ⟨14, _⟩ =>
    show ‖(2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a b a a s ha ha hb hb ha hb ha ha (by positivity) hs
  | ⟨15, _⟩ =>
    show ‖(-2 / 184320 : 𝕂) • (a * a * b * b * a * b * a * b)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a b a b s ha ha hb hb ha hb ha hb (by positivity) hs
  | ⟨16, _⟩ =>
    show ‖(2 / 184320 : 𝕂) • (a * a * b * b * b * a * a * b)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b b a a b s ha ha hb hb hb ha ha hb (by positivity) hs
  | ⟨17, _⟩ =>
    show ‖(-2 / 184320 : 𝕂) • (a * a * b * b * b * a * b * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b b a b a s ha ha hb hb hb ha hb ha (by positivity) hs
  | ⟨18, _⟩ =>
    show ‖(5 / 184320 : 𝕂) • (a * b * a * a * a * b * a * b)‖ ≤ (5 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (5 / 184320 : 𝕂) (5 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a a b a b s ha hb ha ha ha hb ha hb (by positivity) hs
  | ⟨19, _⟩ =>
    show ‖(-5 / 184320 : 𝕂) • (a * b * a * a * a * b * b * a)‖ ≤ (5 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-5 / 184320 : 𝕂) (5 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a a b b a s ha hb ha ha ha hb hb ha (by positivity) hs
  | ⟨20, _⟩ =>
    show ‖(30 / 184320 : 𝕂) • (a * b * a * a * b * a * a * b)‖ ≤ (30 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (30 / 184320 : 𝕂) (30 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b a a b s ha hb ha ha hb ha ha hb (by positivity) hs
  | ⟨21, _⟩ =>
    show ‖(-35 / 184320 : 𝕂) • (a * b * a * a * b * a * b * a)‖ ≤ (35 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-35 / 184320 : 𝕂) (35 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b a b a s ha hb ha ha hb ha hb ha (by positivity) hs
  | ⟨22, _⟩ =>
    show ‖(10 / 184320 : 𝕂) • (a * b * a * a * b * a * b * b)‖ ≤ (10 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (10 / 184320 : 𝕂) (10 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b a b b s ha hb ha ha hb ha hb hb (by positivity) hs
  | ⟨23, _⟩ =>
    show ‖(5 / 184320 : 𝕂) • (a * b * a * a * b * b * a * a)‖ ≤ (5 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (5 / 184320 : 𝕂) (5 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b b a a s ha hb ha ha hb hb ha ha (by positivity) hs
  | ⟨24, _⟩ =>
    show ‖(-10 / 184320 : 𝕂) • (a * b * a * a * b * b * b * a)‖ ≤ (10 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-10 / 184320 : 𝕂) (10 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b b b a s ha hb ha ha hb hb hb ha (by positivity) hs
  | ⟨25, _⟩ =>
    show ‖(-43 / 184320 : 𝕂) • (a * b * a * b * a * a * a * b)‖ ≤ (43 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-43 / 184320 : 𝕂) (43 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a a a b s ha hb ha hb ha ha ha hb (by positivity) hs
  | ⟨26, _⟩ =>
    show ‖(35 / 184320 : 𝕂) • (a * b * a * b * a * a * b * a)‖ ≤ (35 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (35 / 184320 : 𝕂) (35 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a a b a s ha hb ha hb ha ha hb ha (by positivity) hs
  | ⟨27, _⟩ =>
    show ‖(-22 / 184320 : 𝕂) • (a * b * a * b * a * a * b * b)‖ ≤ (22 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-22 / 184320 : 𝕂) (22 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a a b b s ha hb ha hb ha ha hb hb (by positivity) hs
  | ⟨28, _⟩ =>
    show ‖(15 / 184320 : 𝕂) • (a * b * a * b * a * b * a * a)‖ ≤ (15 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (15 / 184320 : 𝕂) (15 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b a a s ha hb ha hb ha hb ha ha (by positivity) hs
  | ⟨29, _⟩ =>
    show ‖(16 / 184320 : 𝕂) • (a * b * a * b * a * b * a * b)‖ ≤ (16 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (16 / 184320 : 𝕂) (16 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b a b s ha hb ha hb ha hb ha hb (by positivity) hs
  | ⟨30, _⟩ =>
    show ‖(12 / 184320 : 𝕂) • (a * b * a * b * a * b * b * a)‖ ≤ (12 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (12 / 184320 : 𝕂) (12 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b b a s ha hb ha hb ha hb hb ha (by positivity) hs
  | ⟨31, _⟩ =>
    show ‖(-7 / 184320 : 𝕂) • (a * b * a * b * b * a * a * a)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b a a a s ha hb ha hb hb ha ha ha (by positivity) hs
  | ⟨32, _⟩ =>
    show ‖(-8 / 184320 : 𝕂) • (a * b * a * b * b * a * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b a a b s ha hb ha hb hb ha ha hb (by positivity) hs
  | ⟨33, _⟩ =>
    show ‖(2 / 184320 : 𝕂) • (a * b * a * b * b * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b b a a s ha hb ha hb hb hb ha ha (by positivity) hs
  | ⟨34, _⟩ =>
    show ‖(8 / 184320 : 𝕂) • (a * b * b * a * a * a * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a a a b s ha hb hb ha ha ha ha hb (by positivity) hs
  | ⟨35, _⟩ =>
    show ‖(5 / 184320 : 𝕂) • (a * b * b * a * a * a * b * a)‖ ≤ (5 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (5 / 184320 : 𝕂) (5 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a a b a s ha hb hb ha ha ha hb ha (by positivity) hs
  | ⟨36, _⟩ =>
    show ‖(12 / 184320 : 𝕂) • (a * b * b * a * a * a * b * b)‖ ≤ (12 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (12 / 184320 : 𝕂) (12 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a a b b s ha hb hb ha ha ha hb hb (by positivity) hs
  | ⟨37, _⟩ =>
    show ‖(-20 / 184320 : 𝕂) • (a * b * b * a * a * b * a * a)‖ ≤ (20 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-20 / 184320 : 𝕂) (20 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a b a a s ha hb hb ha ha hb ha ha (by positivity) hs
  | ⟨38, _⟩ =>
    show ‖(-18 / 184320 : 𝕂) • (a * b * b * a * a * b * a * b)‖ ≤ (18 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-18 / 184320 : 𝕂) (18 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a b a b s ha hb hb ha ha hb ha hb (by positivity) hs
  | ⟨39, _⟩ =>
    show ‖(7 / 184320 : 𝕂) • (a * b * b * a * b * a * a * a)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a a a s ha hb hb ha hb ha ha ha (by positivity) hs
  | ⟨40, _⟩ =>
    show ‖(18 / 184320 : 𝕂) • (a * b * b * a * b * a * a * b)‖ ≤ (18 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (18 / 184320 : 𝕂) (18 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a a b s ha hb hb ha hb ha ha hb (by positivity) hs
  | ⟨41, _⟩ =>
    show ‖(-12 / 184320 : 𝕂) • (a * b * b * a * b * a * b * a)‖ ≤ (12 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-12 / 184320 : 𝕂) (12 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a b a s ha hb hb ha hb ha hb ha (by positivity) hs
  | ⟨42, _⟩ =>
    show ‖(-8 / 184320 : 𝕂) • (a * b * b * b * a * a * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b b a a a b s ha hb hb hb ha ha ha hb (by positivity) hs
  | ⟨43, _⟩ =>
    show ‖(10 / 184320 : 𝕂) • (a * b * b * b * a * a * b * a)‖ ≤ (10 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (10 / 184320 : 𝕂) (10 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b b a a b a s ha hb hb hb ha ha hb ha (by positivity) hs
  | ⟨44, _⟩ =>
    show ‖(-2 / 184320 : 𝕂) • (a * b * b * b * a * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b b a b a a s ha hb hb hb ha hb ha ha (by positivity) hs
  | ⟨45, _⟩ =>
    show ‖(8 / 184320 : 𝕂) • (b * a * a * a * a * b * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a a b a b s hb ha ha ha ha hb ha hb (by positivity) hs
  | ⟨46, _⟩ =>
    show ‖(-8 / 184320 : 𝕂) • (b * a * a * a * a * b * b * a)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a a b b a s hb ha ha ha ha hb hb ha (by positivity) hs
  | ⟨47, _⟩ =>
    show ‖(-40 / 184320 : 𝕂) • (b * a * a * a * b * a * a * b)‖ ≤ (40 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-40 / 184320 : 𝕂) (40 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b a a b s hb ha ha ha hb ha ha hb (by positivity) hs
  | ⟨48, _⟩ =>
    show ‖(43 / 184320 : 𝕂) • (b * a * a * a * b * a * b * a)‖ ≤ (43 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (43 / 184320 : 𝕂) (43 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b a b a s hb ha ha ha hb ha hb ha (by positivity) hs
  | ⟨49, _⟩ =>
    show ‖(-8 / 184320 : 𝕂) • (b * a * a * a * b * a * b * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b a b b s hb ha ha ha hb ha hb hb (by positivity) hs
  | ⟨50, _⟩ =>
    show ‖(-3 / 184320 : 𝕂) • (b * a * a * a * b * b * a * a)‖ ≤ (3 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-3 / 184320 : 𝕂) (3 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b b a a s hb ha ha ha hb hb ha ha (by positivity) hs
  | ⟨51, _⟩ =>
    show ‖(8 / 184320 : 𝕂) • (b * a * a * a * b * b * b * a)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b b b a s hb ha ha ha hb hb hb ha (by positivity) hs
  | ⟨52, _⟩ =>
    show ‖(40 / 184320 : 𝕂) • (b * a * a * b * a * a * a * b)‖ ≤ (40 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (40 / 184320 : 𝕂) (40 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a a a b s hb ha ha hb ha ha ha hb (by positivity) hs
  | ⟨53, _⟩ =>
    show ‖(-30 / 184320 : 𝕂) • (b * a * a * b * a * a * b * a)‖ ≤ (30 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-30 / 184320 : 𝕂) (30 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a a b a s hb ha ha hb ha ha hb ha (by positivity) hs
  | ⟨54, _⟩ =>
    show ‖(20 / 184320 : 𝕂) • (b * a * a * b * a * a * b * b)‖ ≤ (20 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (20 / 184320 : 𝕂) (20 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a a b b s hb ha ha hb ha ha hb hb (by positivity) hs
  | ⟨55, _⟩ =>
    show ‖(-17 / 184320 : 𝕂) • (b * a * a * b * a * b * a * a)‖ ≤ (17 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-17 / 184320 : 𝕂) (17 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b a a s hb ha ha hb ha hb ha ha (by positivity) hs
  | ⟨56, _⟩ =>
    show ‖(-8 / 184320 : 𝕂) • (b * a * a * b * a * b * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b a b s hb ha ha hb ha hb ha hb (by positivity) hs
  | ⟨57, _⟩ =>
    show ‖(-18 / 184320 : 𝕂) • (b * a * a * b * a * b * b * a)‖ ≤ (18 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-18 / 184320 : 𝕂) (18 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b b a s hb ha ha hb ha hb hb ha (by positivity) hs
  | ⟨58, _⟩ =>
    show ‖(7 / 184320 : 𝕂) • (b * a * a * b * b * a * a * a)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b a a a s hb ha ha hb hb ha ha ha (by positivity) hs
  | ⟨59, _⟩ =>
    show ‖(8 / 184320 : 𝕂) • (b * a * a * b * b * a * b * a)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b a b a s hb ha ha hb hb ha hb ha (by positivity) hs
  | ⟨60, _⟩ =>
    show ‖(-2 / 184320 : 𝕂) • (b * a * a * b * b * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b b a a s hb ha ha hb hb hb ha ha (by positivity) hs
  | ⟨61, _⟩ =>
    show ‖(-8 / 184320 : 𝕂) • (b * a * b * a * a * a * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a a a b s hb ha hb ha ha ha ha hb (by positivity) hs
  | ⟨62, _⟩ =>
    show ‖(-5 / 184320 : 𝕂) • (b * a * b * a * a * a * b * a)‖ ≤ (5 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-5 / 184320 : 𝕂) (5 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a a b a s hb ha hb ha ha ha hb ha (by positivity) hs
  | ⟨63, _⟩ =>
    show ‖(-12 / 184320 : 𝕂) • (b * a * b * a * a * a * b * b)‖ ≤ (12 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-12 / 184320 : 𝕂) (12 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a a b b s hb ha hb ha ha ha hb hb (by positivity) hs
  | ⟨64, _⟩ =>
    show ‖(20 / 184320 : 𝕂) • (b * a * b * a * a * b * a * a)‖ ≤ (20 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (20 / 184320 : 𝕂) (20 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a b a a s hb ha hb ha ha hb ha ha (by positivity) hs
  | ⟨65, _⟩ =>
    show ‖(18 / 184320 : 𝕂) • (b * a * b * a * a * b * b * a)‖ ≤ (18 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (18 / 184320 : 𝕂) (18 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a b b a s hb ha hb ha ha hb hb ha (by positivity) hs
  | ⟨66, _⟩ =>
    show ‖(-7 / 184320 : 𝕂) • (b * a * b * a * b * a * a * a)‖ ≤ (7 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-7 / 184320 : 𝕂) (7 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a a a s hb ha hb ha hb ha ha ha (by positivity) hs
  | ⟨67, _⟩ =>
    show ‖(8 / 184320 : 𝕂) • (b * a * b * a * b * a * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a a b s hb ha hb ha hb ha ha hb (by positivity) hs
  | ⟨68, _⟩ =>
    show ‖(-16 / 184320 : 𝕂) • (b * a * b * a * b * a * b * a)‖ ≤ (16 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-16 / 184320 : 𝕂) (16 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a b a s hb ha hb ha hb ha hb ha (by positivity) hs
  | ⟨69, _⟩ =>
    show ‖(2 / 184320 : 𝕂) • (b * a * b * a * b * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b b a a s hb ha hb ha hb hb ha ha (by positivity) hs
  | ⟨70, _⟩ =>
    show ‖(12 / 184320 : 𝕂) • (b * b * a * a * a * b * a * b)‖ ≤ (12 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (12 / 184320 : 𝕂) (12 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a a b a b s hb hb ha ha ha hb ha hb (by positivity) hs
  | ⟨71, _⟩ =>
    show ‖(-12 / 184320 : 𝕂) • (b * b * a * a * a * b * b * a)‖ ≤ (12 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-12 / 184320 : 𝕂) (12 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a a b b a s hb hb ha ha ha hb hb ha (by positivity) hs
  | ⟨72, _⟩ =>
    show ‖(-20 / 184320 : 𝕂) • (b * b * a * a * b * a * a * b)‖ ≤ (20 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-20 / 184320 : 𝕂) (20 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a b a a b s hb hb ha ha hb ha ha hb (by positivity) hs
  | ⟨73, _⟩ =>
    show ‖(22 / 184320 : 𝕂) • (b * b * a * a * b * a * b * a)‖ ≤ (22 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (22 / 184320 : 𝕂) (22 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a b a b a s hb hb ha ha hb ha hb ha (by positivity) hs
  | ⟨74, _⟩ =>
    show ‖(-2 / 184320 : 𝕂) • (b * b * a * a * b * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a a b b a a s hb hb ha ha hb hb ha ha (by positivity) hs
  | ⟨75, _⟩ =>
    show ‖(8 / 184320 : 𝕂) • (b * b * a * b * a * a * a * b)‖ ≤ (8 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (8 / 184320 : 𝕂) (8 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a b a a a b s hb hb ha hb ha ha ha hb (by positivity) hs
  | ⟨76, _⟩ =>
    show ‖(-10 / 184320 : 𝕂) • (b * b * a * b * a * a * b * a)‖ ≤ (10 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (-10 / 184320 : 𝕂) (10 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a b a a b a s hb hb ha hb ha ha hb ha (by positivity) hs
  | ⟨77, _⟩ =>
    show ‖(2 / 184320 : 𝕂) • (b * b * a * b * a * b * a * a)‖ ≤ (2 / 184320 : ℝ) * s ^ 8 from
      deg8_smul_word_le (2 / 184320 : 𝕂) (2 / 184320 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b b a b a b a a s hb hb ha hb ha hb ha ha (by positivity) hs
  | ⟨_ + 78, h⟩ => absurd h (by omega)

-- Per-index norm bound for `linResTerm9`.
set_option maxHeartbeats 16000000 in
private lemma linResTerm9_norm_le
    (a b : 𝔸) (s : ℝ) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :
    ∀ i : Fin 48, ‖linResTerm9 (𝕂 := 𝕂) a b i‖ ≤ linResBound9 s i := fun i =>
  match i with
  | ⟨0, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * a * b)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b a b a b s ha ha hb ha hb ha hb ha hb (by positivity) hs
  | ⟨1, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (a * a * b * a * b * a * b * b * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b a b b a s ha ha hb ha hb ha hb hb ha (by positivity) hs
  | ⟨2, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * a * b)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b b a a b s ha ha hb ha hb hb ha ha hb (by positivity) hs
  | ⟨3, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (a * a * b * a * b * b * a * b * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b a b b a b a s ha ha hb ha hb hb ha hb ha (by positivity) hs
  | ⟨4, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * a * b)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a a b a b s ha ha hb hb ha ha hb ha hb (by positivity) hs
  | ⟨5, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (a * a * b * b * a * a * b * b * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a a b b a s ha ha hb hb ha ha hb hb ha (by positivity) hs
  | ⟨6, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * a * b)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a b a a b s ha ha hb hb ha hb ha ha hb (by positivity) hs
  | ⟨7, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (a * a * b * b * a * b * a * b * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a a b b a b a b a s ha ha hb hb ha hb ha hb ha (by positivity) hs
  | ⟨8, _⟩ =>
    show ‖(5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * a * b)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b a b a b s ha hb ha ha hb ha hb ha hb (by positivity) hs
  | ⟨9, _⟩ =>
    show ‖(-5 / 368640 : 𝕂) • (a * b * a * a * b * a * b * b * a)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b a b b a s ha hb ha ha hb ha hb hb ha (by positivity) hs
  | ⟨10, _⟩ =>
    show ‖(-5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * a * b)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b b a a b s ha hb ha ha hb hb ha ha hb (by positivity) hs
  | ⟨11, _⟩ =>
    show ‖(5 / 368640 : 𝕂) • (a * b * a * a * b * b * a * b * a)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a a b b a b a s ha hb ha ha hb hb ha hb ha (by positivity) hs
  | ⟨12, _⟩ =>
    show ‖(-11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * a * b)‖ ≤ (11 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-11 / 368640 : 𝕂) (11 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a a b a b s ha hb ha hb ha ha hb ha hb (by positivity) hs
  | ⟨13, _⟩ =>
    show ‖(11 / 368640 : 𝕂) • (a * b * a * b * a * a * b * b * a)‖ ≤ (11 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (11 / 368640 : 𝕂) (11 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a a b b a s ha hb ha hb ha ha hb hb ha (by positivity) hs
  | ⟨14, _⟩ =>
    show ‖(15 / 368640 : 𝕂) • (a * b * a * b * a * b * a * a * b)‖ ≤ (15 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (15 / 368640 : 𝕂) (15 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b a a b s ha hb ha hb ha hb ha ha hb (by positivity) hs
  | ⟨15, _⟩ =>
    show ‖(-16 / 368640 : 𝕂) • (a * b * a * b * a * b * a * b * a)‖ ≤ (16 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-16 / 368640 : 𝕂) (16 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b a b a s ha hb ha hb ha hb ha hb ha (by positivity) hs
  | ⟨16, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (a * b * a * b * a * b * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b a b b a a s ha hb ha hb ha hb hb ha ha (by positivity) hs
  | ⟨17, _⟩ =>
    show ‖(-4 / 368640 : 𝕂) • (a * b * a * b * b * a * a * a * b)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b a a a b s ha hb ha hb hb ha ha ha hb (by positivity) hs
  | ⟨18, _⟩ =>
    show ‖(5 / 368640 : 𝕂) • (a * b * a * b * b * a * a * b * a)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b a a b a s ha hb ha hb hb ha ha hb ha (by positivity) hs
  | ⟨19, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (a * b * a * b * b * a * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b a b b a b a a s ha hb ha hb hb ha hb ha ha (by positivity) hs
  | ⟨20, _⟩ =>
    show ‖(6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * a * b)‖ ≤ (6 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (6 / 368640 : 𝕂) (6 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a a b a b s ha hb hb ha ha ha hb ha hb (by positivity) hs
  | ⟨21, _⟩ =>
    show ‖(-6 / 368640 : 𝕂) • (a * b * b * a * a * a * b * b * a)‖ ≤ (6 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-6 / 368640 : 𝕂) (6 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a a b b a s ha hb hb ha ha ha hb hb ha (by positivity) hs
  | ⟨22, _⟩ =>
    show ‖(-10 / 368640 : 𝕂) • (a * b * b * a * a * b * a * a * b)‖ ≤ (10 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-10 / 368640 : 𝕂) (10 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a b a a b s ha hb hb ha ha hb ha ha hb (by positivity) hs
  | ⟨23, _⟩ =>
    show ‖(11 / 368640 : 𝕂) • (a * b * b * a * a * b * a * b * a)‖ ≤ (11 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (11 / 368640 : 𝕂) (11 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a b a b a s ha hb hb ha ha hb ha hb ha (by positivity) hs
  | ⟨24, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (a * b * b * a * a * b * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a a b b a a s ha hb hb ha ha hb hb ha ha (by positivity) hs
  | ⟨25, _⟩ =>
    show ‖(4 / 368640 : 𝕂) • (a * b * b * a * b * a * a * a * b)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a a a b s ha hb hb ha hb ha ha ha hb (by positivity) hs
  | ⟨26, _⟩ =>
    show ‖(-5 / 368640 : 𝕂) • (a * b * b * a * b * a * a * b * a)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a a b a s ha hb hb ha hb ha ha hb ha (by positivity) hs
  | ⟨27, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (a * b * b * a * b * a * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        a b b a b a b a a s ha hb hb ha hb ha hb ha ha (by positivity) hs
  | ⟨28, _⟩ =>
    show ‖(-4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * a * b)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b a b a b s hb ha ha ha hb ha hb ha hb (by positivity) hs
  | ⟨29, _⟩ =>
    show ‖(4 / 368640 : 𝕂) • (b * a * a * a * b * a * b * b * a)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b a b b a s hb ha ha ha hb ha hb hb ha (by positivity) hs
  | ⟨30, _⟩ =>
    show ‖(4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * a * b)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b b a a b s hb ha ha ha hb hb ha ha hb (by positivity) hs
  | ⟨31, _⟩ =>
    show ‖(-4 / 368640 : 𝕂) • (b * a * a * a * b * b * a * b * a)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a a b b a b a s hb ha ha ha hb hb ha hb ha (by positivity) hs
  | ⟨32, _⟩ =>
    show ‖(10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * a * b)‖ ≤ (10 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (10 / 368640 : 𝕂) (10 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a a b a b s hb ha ha hb ha ha hb ha hb (by positivity) hs
  | ⟨33, _⟩ =>
    show ‖(-10 / 368640 : 𝕂) • (b * a * a * b * a * a * b * b * a)‖ ≤ (10 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-10 / 368640 : 𝕂) (10 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a a b b a s hb ha ha hb ha ha hb hb ha (by positivity) hs
  | ⟨34, _⟩ =>
    show ‖(-14 / 368640 : 𝕂) • (b * a * a * b * a * b * a * a * b)‖ ≤ (14 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-14 / 368640 : 𝕂) (14 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b a a b s hb ha ha hb ha hb ha ha hb (by positivity) hs
  | ⟨35, _⟩ =>
    show ‖(15 / 368640 : 𝕂) • (b * a * a * b * a * b * a * b * a)‖ ≤ (15 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (15 / 368640 : 𝕂) (15 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b a b a s hb ha ha hb ha hb ha hb ha (by positivity) hs
  | ⟨36, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (b * a * a * b * a * b * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b a b b a a s hb ha ha hb ha hb hb ha ha (by positivity) hs
  | ⟨37, _⟩ =>
    show ‖(4 / 368640 : 𝕂) • (b * a * a * b * b * a * a * a * b)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b a a a b s hb ha ha hb hb ha ha ha hb (by positivity) hs
  | ⟨38, _⟩ =>
    show ‖(-5 / 368640 : 𝕂) • (b * a * a * b * b * a * a * b * a)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b a a b a s hb ha ha hb hb ha ha hb ha (by positivity) hs
  | ⟨39, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (b * a * a * b * b * a * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a a b b a b a a s hb ha ha hb hb ha hb ha ha (by positivity) hs
  | ⟨40, _⟩ =>
    show ‖(-6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * a * b)‖ ≤ (6 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-6 / 368640 : 𝕂) (6 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a a b a b s hb ha hb ha ha ha hb ha hb (by positivity) hs
  | ⟨41, _⟩ =>
    show ‖(6 / 368640 : 𝕂) • (b * a * b * a * a * a * b * b * a)‖ ≤ (6 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (6 / 368640 : 𝕂) (6 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a a b b a s hb ha hb ha ha ha hb hb ha (by positivity) hs
  | ⟨42, _⟩ =>
    show ‖(10 / 368640 : 𝕂) • (b * a * b * a * a * b * a * a * b)‖ ≤ (10 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (10 / 368640 : 𝕂) (10 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a b a a b s hb ha hb ha ha hb ha ha hb (by positivity) hs
  | ⟨43, _⟩ =>
    show ‖(-11 / 368640 : 𝕂) • (b * a * b * a * a * b * a * b * a)‖ ≤ (11 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-11 / 368640 : 𝕂) (11 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a b a b a s hb ha hb ha ha hb ha hb ha (by positivity) hs
  | ⟨44, _⟩ =>
    show ‖(1 / 368640 : 𝕂) • (b * a * b * a * a * b * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a a b b a a s hb ha hb ha ha hb hb ha ha (by positivity) hs
  | ⟨45, _⟩ =>
    show ‖(-4 / 368640 : 𝕂) • (b * a * b * a * b * a * a * a * b)‖ ≤ (4 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-4 / 368640 : 𝕂) (4 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a a a b s hb ha hb ha hb ha ha ha hb (by positivity) hs
  | ⟨46, _⟩ =>
    show ‖(5 / 368640 : 𝕂) • (b * a * b * a * b * a * a * b * a)‖ ≤ (5 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (5 / 368640 : 𝕂) (5 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a a b a s hb ha hb ha hb ha ha hb ha (by positivity) hs
  | ⟨47, _⟩ =>
    show ‖(-1 / 368640 : 𝕂) • (b * a * b * a * b * a * b * a * a)‖ ≤ (1 / 368640 : ℝ) * s ^ 9 from
      deg9_smul_word_le (-1 / 368640 : 𝕂) (1 / 368640 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat])
        b a b a b a b a a s hb ha hb ha hb ha hb ha ha (by positivity) hs
  | ⟨_ + 48, h⟩ => absurd h (by omega)

-- Sum of deg-7 bounds: ∑ ≤ 79·112/92160 · s^7 = 8848/92160 · s^7.
-- Uses uniform per-i bound (max coefficient) + Finset.sum_const.
set_option maxHeartbeats 15800000 in
private lemma sum_linResBound7_le (s : ℝ) (hs : 0 ≤ s) :
    ∑ i : Fin 79, linResBound7 s i ≤ (8848 / 92160 : ℝ) * s ^ 7 := by
  have hs_pow_nn : 0 ≤ s ^ 7 := pow_nonneg hs 7
  have h_unif : ∀ i : Fin 79, linResBound7 s i ≤ (112 / 92160 : ℝ) * s ^ 7 := fun i =>
    match i with
    | ⟨0, _⟩ => by
      show (7 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨1, _⟩ => by
      show (7 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨2, _⟩ => by
      show (30 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨3, _⟩ => by
      show (32 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨4, _⟩ => by
      show (14 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨5, _⟩ => by
      show (2 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨6, _⟩ => by
      show (14 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨7, _⟩ => by
      show (50 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨8, _⟩ => by
      show (60 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨9, _⟩ => by
      show (40 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨10, _⟩ => by
      show (12 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨11, _⟩ => by
      show (8 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨12, _⟩ => by
      show (30 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨13, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨14, _⟩ => by
      show (2 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨15, _⟩ => by
      show (14 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨16, _⟩ => by
      show (20 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨17, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨18, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨19, _⟩ => by
      show (45 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨20, _⟩ => by
      show (80 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨21, _⟩ => by
      show (10 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨22, _⟩ => by
      show (60 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨23, _⟩ => by
      show (44 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨24, _⟩ => by
      show (6 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨25, _⟩ => by
      show (20 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨26, _⟩ => by
      show (32 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨27, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨28, _⟩ => by
      show (112 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨29, _⟩ => by
      show (28 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨30, _⟩ => by
      show (20 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨31, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨32, _⟩ => by
      show (20 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨33, _⟩ => by
      show (7 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨34, _⟩ => by
      show (6 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨35, _⟩ => by
      show (6 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨36, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨37, _⟩ => by
      show (30 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨38, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨39, _⟩ => by
      show (24 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨40, _⟩ => by
      show (14 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨41, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨42, _⟩ => by
      show (20 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨43, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨44, _⟩ => by
      show (18 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨45, _⟩ => by
      show (45 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨46, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨47, _⟩ => by
      show (50 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨48, _⟩ => by
      show (80 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨49, _⟩ => by
      show (6 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨50, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨51, _⟩ => by
      show (30 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨52, _⟩ => by
      show (96 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨53, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨54, _⟩ => by
      show (40 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨55, _⟩ => by
      show (14 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨56, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨57, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨58, _⟩ => by
      show (7 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨59, _⟩ => by
      show (80 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨60, _⟩ => by
      show (44 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨61, _⟩ => by
      show (40 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨62, _⟩ => by
      show (8 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨63, _⟩ => by
      show (32 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨64, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨65, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨66, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨67, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨68, _⟩ => by
      show (10 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨69, _⟩ => by
      show (24 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨70, _⟩ => by
      show (40 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨71, _⟩ => by
      show (40 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨72, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨73, _⟩ => by
      show (14 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨74, _⟩ => by
      show (40 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨75, _⟩ => by
      show (28 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨76, _⟩ => by
      show (16 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨77, _⟩ => by
      show (20 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨78, _⟩ => by
      show (4 / 92160 : ℝ) * s ^ 7 ≤ (112 / 92160 : ℝ) * s ^ 7
      nlinarith [hs_pow_nn]
    | ⟨_ + 79, h⟩ => absurd h (by omega)
  calc ∑ i : Fin 79, linResBound7 s i
      ≤ ∑ _i : Fin 79, (112 / 92160 : ℝ) * s ^ 7 := Finset.sum_le_sum (fun i _ => h_unif i)
    _ = 79 * ((112 / 92160 : ℝ) * s ^ 7) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = (8848 / 92160 : ℝ) * s ^ 7 := by ring

-- Sum of deg-8 bounds: ∑ ≤ 78·43/184320 · s^8 = 3354/184320 · s^8.
-- Uses uniform per-i bound (max coefficient) + Finset.sum_const.
set_option maxHeartbeats 15600000 in
private lemma sum_linResBound8_le (s : ℝ) (hs : 0 ≤ s) :
    ∑ i : Fin 78, linResBound8 s i ≤ (3354 / 184320 : ℝ) * s ^ 8 := by
  have hs_pow_nn : 0 ≤ s ^ 8 := pow_nonneg hs 8
  have h_unif : ∀ i : Fin 78, linResBound8 s i ≤ (43 / 184320 : ℝ) * s ^ 8 := fun i =>
    match i with
    | ⟨0, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨1, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨2, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨3, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨4, _⟩ => by
      show (20 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨5, _⟩ => by
      show (20 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨6, _⟩ => by
      show (17 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨7, _⟩ => by
      show (15 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨8, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨9, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨10, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨11, _⟩ => by
      show (3 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨12, _⟩ => by
      show (5 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨13, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨14, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨15, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨16, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨17, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨18, _⟩ => by
      show (5 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨19, _⟩ => by
      show (5 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨20, _⟩ => by
      show (30 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨21, _⟩ => by
      show (35 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨22, _⟩ => by
      show (10 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨23, _⟩ => by
      show (5 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨24, _⟩ => by
      show (10 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨25, _⟩ => by
      show (43 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨26, _⟩ => by
      show (35 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨27, _⟩ => by
      show (22 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨28, _⟩ => by
      show (15 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨29, _⟩ => by
      show (16 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨30, _⟩ => by
      show (12 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨31, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨32, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨33, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨34, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨35, _⟩ => by
      show (5 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨36, _⟩ => by
      show (12 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨37, _⟩ => by
      show (20 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨38, _⟩ => by
      show (18 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨39, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨40, _⟩ => by
      show (18 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨41, _⟩ => by
      show (12 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨42, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨43, _⟩ => by
      show (10 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨44, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨45, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨46, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨47, _⟩ => by
      show (40 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨48, _⟩ => by
      show (43 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨49, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨50, _⟩ => by
      show (3 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨51, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨52, _⟩ => by
      show (40 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨53, _⟩ => by
      show (30 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨54, _⟩ => by
      show (20 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨55, _⟩ => by
      show (17 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨56, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨57, _⟩ => by
      show (18 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨58, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨59, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨60, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨61, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨62, _⟩ => by
      show (5 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨63, _⟩ => by
      show (12 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨64, _⟩ => by
      show (20 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨65, _⟩ => by
      show (18 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨66, _⟩ => by
      show (7 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨67, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨68, _⟩ => by
      show (16 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨69, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨70, _⟩ => by
      show (12 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨71, _⟩ => by
      show (12 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨72, _⟩ => by
      show (20 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨73, _⟩ => by
      show (22 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨74, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨75, _⟩ => by
      show (8 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨76, _⟩ => by
      show (10 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨77, _⟩ => by
      show (2 / 184320 : ℝ) * s ^ 8 ≤ (43 / 184320 : ℝ) * s ^ 8
      nlinarith [hs_pow_nn]
    | ⟨_ + 78, h⟩ => absurd h (by omega)
  calc ∑ i : Fin 78, linResBound8 s i
      ≤ ∑ _i : Fin 78, (43 / 184320 : ℝ) * s ^ 8 := Finset.sum_le_sum (fun i _ => h_unif i)
    _ = 78 * ((43 / 184320 : ℝ) * s ^ 8) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = (3354 / 184320 : ℝ) * s ^ 8 := by ring

-- Sum of deg-9 bounds: ∑ ≤ 48·16/368640 · s^9 = 768/368640 · s^9.
-- Uses uniform per-i bound (max coefficient) + Finset.sum_const.
set_option maxHeartbeats 9600000 in
private lemma sum_linResBound9_le (s : ℝ) (hs : 0 ≤ s) :
    ∑ i : Fin 48, linResBound9 s i ≤ (768 / 368640 : ℝ) * s ^ 9 := by
  have hs_pow_nn : 0 ≤ s ^ 9 := pow_nonneg hs 9
  have h_unif : ∀ i : Fin 48, linResBound9 s i ≤ (16 / 368640 : ℝ) * s ^ 9 := fun i =>
    match i with
    | ⟨0, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨1, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨2, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨3, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨4, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨5, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨6, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨7, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨8, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨9, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨10, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨11, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨12, _⟩ => by
      show (11 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨13, _⟩ => by
      show (11 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨14, _⟩ => by
      show (15 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨15, _⟩ => by
      show (16 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨16, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨17, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨18, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨19, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨20, _⟩ => by
      show (6 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨21, _⟩ => by
      show (6 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨22, _⟩ => by
      show (10 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨23, _⟩ => by
      show (11 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨24, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨25, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨26, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨27, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨28, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨29, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨30, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨31, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨32, _⟩ => by
      show (10 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨33, _⟩ => by
      show (10 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨34, _⟩ => by
      show (14 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨35, _⟩ => by
      show (15 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨36, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨37, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨38, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨39, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨40, _⟩ => by
      show (6 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨41, _⟩ => by
      show (6 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨42, _⟩ => by
      show (10 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨43, _⟩ => by
      show (11 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨44, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨45, _⟩ => by
      show (4 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨46, _⟩ => by
      show (5 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨47, _⟩ => by
      show (1 / 368640 : ℝ) * s ^ 9 ≤ (16 / 368640 : ℝ) * s ^ 9
      nlinarith [hs_pow_nn]
    | ⟨_ + 48, h⟩ => absurd h (by omega)
  calc ∑ i : Fin 48, linResBound9 s i
      ≤ ∑ _i : Fin 48, (16 / 368640 : ℝ) * s ^ 9 := Finset.sum_le_sum (fun i _ => h_unif i)
    _ = 48 * ((16 / 368640 : ℝ) * s ^ 9) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = (768 / 368640 : ℝ) * s ^ 9 := by ring

-- **The polynomial bound** (replaces the previous private axiom).
set_option maxHeartbeats 16000000 in
private theorem norm_C5_LinResidual_polynomial_le
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖C5_LinResidual_polynomial 𝕂 a b‖ ≤ 1 * (‖a‖ + ‖b‖) ^ 7 := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have ha : ‖a‖ ≤ s := by linarith [norm_nonneg b]
  have hb : ‖b‖ ≤ s := by linarith [norm_nonneg a]
  have hs_lt : s < 1 / 4 := hab
  have hs7_nn : 0 ≤ s ^ 7 := pow_nonneg hs_nn 7
  -- Per-degree norm bounds.
  have hdeg7 : ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b‖ ≤ (8848 / 92160 : ℝ) * s ^ 7 := by
    rw [C5_LinResidual_deg7_eq_sum]
    calc ‖∑ i, linResTerm7 (𝕂 := 𝕂) a b i‖
        ≤ ∑ i, ‖linResTerm7 (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, linResBound7 s i :=
          Finset.sum_le_sum (fun i _ => linResTerm7_norm_le a b s ha hb hs_nn i)
      _ ≤ (8848 / 92160 : ℝ) * s ^ 7 := sum_linResBound7_le s hs_nn
  have hdeg8 : ‖C5_LinResidual_deg8 (𝕂 := 𝕂) a b‖ ≤ (3354 / 184320 : ℝ) * s ^ 8 := by
    rw [C5_LinResidual_deg8_eq_sum]
    calc ‖∑ i, linResTerm8 (𝕂 := 𝕂) a b i‖
        ≤ ∑ i, ‖linResTerm8 (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, linResBound8 s i :=
          Finset.sum_le_sum (fun i _ => linResTerm8_norm_le a b s ha hb hs_nn i)
      _ ≤ (3354 / 184320 : ℝ) * s ^ 8 := sum_linResBound8_le s hs_nn
  have hdeg9 : ‖C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖ ≤ (768 / 368640 : ℝ) * s ^ 9 := by
    rw [C5_LinResidual_deg9_eq_sum]
    calc ‖∑ i, linResTerm9 (𝕂 := 𝕂) a b i‖
        ≤ ∑ i, ‖linResTerm9 (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, linResBound9 s i :=
          Finset.sum_le_sum (fun i _ => linResTerm9_norm_le a b s ha hb hs_nn i)
      _ ≤ (768 / 368640 : ℝ) * s ^ 9 := sum_linResBound9_le s hs_nn
  -- Polynomial degrees relative to s^7 (for s ≤ 1/4).
  have hs8 : s ^ 8 ≤ s ^ 7 * (1/4) := by
    have heq : s^8 = s^7 * s := by ring
    rw [heq]; nlinarith [hs7_nn]
  have hs9 : s ^ 9 ≤ s ^ 7 * (1/16) := by
    have heq : s^9 = s^7 * (s*s) := by ring
    rw [heq]; nlinarith [hs7_nn, sq_nonneg s]
  -- Triangle inequality on the per-degree decomposition.
  rw [C5_LinResidual_polynomial_eq_parts]
  calc ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b + C5_LinResidual_deg8 (𝕂 := 𝕂) a b + C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖
      ≤ ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b + C5_LinResidual_deg8 (𝕂 := 𝕂) a b‖ + ‖C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖ := norm_add_le _ _
    _ ≤ ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b‖ + ‖C5_LinResidual_deg8 (𝕂 := 𝕂) a b‖ + ‖C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖ := by
        linarith [norm_add_le (C5_LinResidual_deg7 (𝕂 := 𝕂) a b) (C5_LinResidual_deg8 (𝕂 := 𝕂) a b),
                   norm_nonneg (C5_LinResidual_deg9 (𝕂 := 𝕂) a b)]
    _ ≤ (8848 / 92160 : ℝ) * s ^ 7 + (3354 / 184320 : ℝ) * s ^ 8 + (768 / 368640 : ℝ) * s ^ 9 := by
        linarith [hdeg7, hdeg8, hdeg9]
    _ ≤ 1 * s ^ 7 := by nlinarith [hs7_nn, hs8, hs9]

-- Helper: norm bound on the V₂ commutator.
-- ‖V₂‖ = ‖(2:𝕂)⁻¹·(a'·b - b·a')‖ ≤ ‖a'‖·‖b‖ ≤ s²/2.

set_option maxHeartbeats 4000000 in
private theorem symmetric_bch_quintic_C5_diff_residual_le
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    -- C5_diff_residual = (C₅(z, a') - C₅(a'+b, a')) - ΔC₅_lin_explicit.
    ‖((bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a') -
     ((-14 / 46080 : 𝕂) • (a * a * a * a * b * b) +
      (46 / 46080 : 𝕂) • (a * a * a * b * a * b) +
      (10 / 46080 : 𝕂) • (a * a * a * b * b * a) +
      (28 / 46080 : 𝕂) • (a * a * a * b * b * b) +
      (-54 / 46080 : 𝕂) • (a * a * b * a * a * b) +
      (-30 / 46080 : 𝕂) • (a * a * b * a * b * a) +
      (-52 / 46080 : 𝕂) • (a * a * b * a * b * b) +
      (-12 / 46080 : 𝕂) • (a * a * b * b * a * b) +
      (-20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
      (-8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
      (36 / 46080 : 𝕂) • (a * b * a * a * a * b) +
      (-32 / 46080 : 𝕂) • (a * b * a * a * b * b) +
      (30 / 46080 : 𝕂) • (a * b * a * b * a * a) +
      (128 / 46080 : 𝕂) • (a * b * a * b * a * b) +
      (40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
      (32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
      (-10 / 46080 : 𝕂) • (a * b * b * a * a * a) +
      (-32 / 46080 : 𝕂) • (a * b * b * a * a * b) +
      (-40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
      (-48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
      (20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
      (32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
      (-36 / 46080 : 𝕂) • (b * a * a * a * b * a) +
      (54 / 46080 : 𝕂) • (b * a * a * b * a * a) +
      (32 / 46080 : 𝕂) • (b * a * a * b * b * a) +
      (-46 / 46080 : 𝕂) • (b * a * b * a * a * a) +
      (-128 / 46080 : 𝕂) • (b * a * b * a * b * a) +
      (12 / 46080 : 𝕂) • (b * a * b * b * a * a) +
      (-32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
      (14 / 46080 : 𝕂) • (b * b * a * a * a * a) +
      (32 / 46080 : 𝕂) • (b * b * a * a * b * a) +
      (52 / 46080 : 𝕂) • (b * b * a * b * a * a) +
      (48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
      (-28 / 46080 : 𝕂) • (b * b * b * a * a * a) +
      (-32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
      (8 / 46080 : 𝕂) • (b * b * b * b * a * a)))‖ ≤
      5000000 * (‖a‖ + ‖b‖) ^ 7 := by
  intro a' z
  -- Setup norms
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt : s < 1 / 4 := hab
  have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ s / 2 := by
    show ‖(2 : 𝕂)⁻¹ • a‖ ≤ _
    calc ‖(2 : 𝕂)⁻¹ • a‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
      _ ≤ s / 2 := by have := norm_nonneg b; linarith
  have ha'_b_le : ‖a' + b‖ ≤ 3 * s / 2 := by
    calc ‖a' + b‖ ≤ ‖a'‖ + ‖b‖ := norm_add_le _ _
      _ ≤ s / 2 + s := by have := norm_nonneg a; linarith
      _ = 3 * s / 2 := by ring
  have ha'_a : ‖a'‖ ≤ ‖a‖ := by
    show ‖(2 : 𝕂)⁻¹ • a‖ ≤ _
    calc ‖(2 : 𝕂)⁻¹ • a‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
      _ ≤ ‖a‖ := by linarith [norm_nonneg a]
  have hs1_le : ‖a'‖ + ‖b‖ ≤ s := by linarith [ha'_a]
  have hs1_nn : (0 : ℝ) ≤ ‖a'‖ + ‖b‖ := by positivity
  -- ‖V₂‖ ≤ s²/2.
  set V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a') with hV2_def
  have hV2_le : ‖V₂‖ ≤ s ^ 2 / 2 := by
    rw [hV2_def]
    have hcomm : ‖a' * b - b * a'‖ ≤ 2 * ‖a'‖ * ‖b‖ := by
      calc ‖a' * b - b * a'‖ ≤ ‖a' * b‖ + ‖b * a'‖ := by
            rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖a'‖ * ‖b‖ + ‖b‖ * ‖a'‖ := by gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖a'‖ * ‖b‖ := by ring
    calc ‖(2 : 𝕂)⁻¹ • (a' * b - b * a')‖
        ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a' * b - b * a'‖ := norm_smul_le _ _
      _ = (2 : ℝ)⁻¹ * ‖a' * b - b * a'‖ := by rw [h_half_norm]
      _ ≤ (2 : ℝ)⁻¹ * (2 * ‖a'‖ * ‖b‖) := by
          apply mul_le_mul_of_nonneg_left hcomm (by norm_num)
      _ = ‖a'‖ * ‖b‖ := by ring
      _ ≤ (s / 2) * s := by
          apply mul_le_mul ha'_le _ (norm_nonneg _) (by linarith)
          have := norm_nonneg a; linarith
      _ = s ^ 2 / 2 := by ring
  -- Norms of V₃, V₄, V₅, V₆.
  have hV3_le : ‖bch_cubic_term 𝕂 a' b‖ ≤ s ^ 3 := by
    calc ‖bch_cubic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 3 := norm_bch_cubic_term_le a' b
      _ ≤ s ^ 3 := pow_le_pow_left₀ hs1_nn hs1_le 3
  have hV4_le : ‖bch_quartic_term 𝕂 a' b‖ ≤ s ^ 4 := by
    calc ‖bch_quartic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 4 := norm_bch_quartic_term_le a' b
      _ ≤ s ^ 4 := pow_le_pow_left₀ hs1_nn hs1_le 4
  have hV5_le : ‖bch_quintic_term 𝕂 a' b‖ ≤ s ^ 5 := by
    calc ‖bch_quintic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 5 := norm_bch_quintic_term_le a' b
      _ ≤ s ^ 5 := pow_le_pow_left₀ hs1_nn hs1_le 5
  have hV6_le : ‖bch_sextic_term 𝕂 a' b‖ ≤ s ^ 6 := by
    calc ‖bch_sextic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 6 := norm_bch_sextic_term_le a' b
      _ ≤ s ^ 6 := pow_le_pow_left₀ hs1_nn hs1_le 6
  -- R1_sept = z - (a'+b) - V₂ - V₃ - V₄ - V₅ - V₆.
  have hR1_le : ‖z - (a' + b) - V₂ - bch_cubic_term 𝕂 a' b -
                  bch_quartic_term 𝕂 a' b -
                  bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b‖ ≤
                1500000 * s ^ 7 :=
    norm_bch_inner_septic_remainder_le (𝕂 := 𝕂) a b hab
  -- Bounds for power of s.
  have hs2_le : s^2 ≤ 1/16 := by nlinarith [hs_lt, hs_nn]
  have hs3_le : s^3 ≤ 1/64 := by nlinarith [hs_lt, hs_nn, sq_nonneg s]
  have hs4_le : s^4 ≤ 1/256 := by nlinarith [hs2_le, sq_nonneg (s^2)]
  have hs5_nn : (0:ℝ) ≤ s^5 := pow_nonneg hs_nn 5
  have hs4_nn : (0:ℝ) ≤ s^4 := pow_nonneg hs_nn 4
  have hs3_nn : (0:ℝ) ≤ s^3 := pow_nonneg hs_nn 3
  -- Form WRest6 = V₃+V₄+V₅+V₆+R1_sept (= z - (a'+b) - V₂).
  set z₁ : 𝔸 := (a' + b) + V₂ with hz1_def
  -- ‖z - z₁‖ = ‖V₃ + V₄ + V₅ + V₆ + R1_sept‖ ≤ 6000·s³.
  have hWRest_le : ‖z - z₁‖ ≤ 6000 * s ^ 3 := by
    have hsplit : z - z₁ = bch_cubic_term 𝕂 a' b + bch_quartic_term 𝕂 a' b +
                          bch_quintic_term 𝕂 a' b + bch_sextic_term 𝕂 a' b +
                          (z - (a' + b) - V₂ - bch_cubic_term 𝕂 a' b -
                           bch_quartic_term 𝕂 a' b -
                           bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b) := by
      rw [hz1_def]; abel
    rw [hsplit]
    have h1 := norm_add_le (bch_cubic_term 𝕂 a' b + bch_quartic_term 𝕂 a' b +
                            bch_quintic_term 𝕂 a' b + bch_sextic_term 𝕂 a' b)
                           (z - (a' + b) - V₂ - bch_cubic_term 𝕂 a' b -
                            bch_quartic_term 𝕂 a' b -
                            bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b)
    have h2 := norm_add_le (bch_cubic_term 𝕂 a' b + bch_quartic_term 𝕂 a' b +
                            bch_quintic_term 𝕂 a' b)
                           (bch_sextic_term 𝕂 a' b)
    have h3 := norm_add_le (bch_cubic_term 𝕂 a' b + bch_quartic_term 𝕂 a' b)
                           (bch_quintic_term 𝕂 a' b)
    have h4 := norm_add_le (bch_cubic_term 𝕂 a' b)
                           (bch_quartic_term 𝕂 a' b)
    have hs5_le_s3 : s^5 ≤ s^3 * (1/16) := by
      have heq : s^5 = s^2 * s^3 := by ring
      rw [heq]; nlinarith [hs3_nn, hs2_le]
    have hs6_le_s3 : s^6 ≤ s^3 * (1/64) := by
      have heq : s^6 = s^3 * s^3 := by ring
      rw [heq]; nlinarith [hs3_nn, hs3_le]
    have hs7_le_s3 : s^7 ≤ s^3 * (1/256) := by
      have heq : s^7 = s^4 * s^3 := by ring
      rw [heq]; nlinarith [hs3_nn, hs4_le]
    have hs4_le_s3 : s^4 ≤ s^3 * (1/4) := by
      have heq : s^4 = s * s^3 := by ring
      rw [heq]; nlinarith [hs3_nn, hs_lt, hs_nn]
    nlinarith [h1, h2, h3, h4, hV3_le, hV4_le, hV5_le, hV6_le, hR1_le,
               hs3_nn, hs4_le_s3, hs5_le_s3, hs6_le_s3, hs7_le_s3]
  -- Bound M = ‖z‖ + ‖z₁‖ + ‖a'‖ ≤ 5s.
  have hln2 : (1 : ℝ) / 4 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    linarith [real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1:ℝ)/4 < 5/6)]
  have hs1_lt_log2 : ‖a'‖ + ‖b‖ < Real.log 2 := by linarith
  have hexp_s₁_lt : Real.exp (‖a'‖ + ‖b‖) < 2 := by
    calc _ < Real.exp (Real.log 2) := Real.exp_strictMono hs1_lt_log2
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom₁ : 0 < 2 - Real.exp (‖a'‖ + ‖b‖) := by linarith
  have hexp_le : Real.exp (‖a'‖ + ‖b‖) ≤ 1 + (‖a'‖ + ‖b‖) + (‖a'‖ + ‖b‖) ^ 2 := by
    nlinarith [real_exp_third_order_le_cube hs1_nn (by linarith : ‖a'‖ + ‖b‖ < 5/6)]
  have hdenom_lb : (11 : ℝ) / 16 ≤ 2 - Real.exp (‖a'‖ + ‖b‖) := by nlinarith
  have hW_le : ‖z - (a' + b)‖ ≤ 3 * (‖a'‖ + ‖b‖)^2 / (2 - Real.exp (‖a'‖ + ‖b‖)) :=
    norm_bch_sub_add_le (𝕂 := 𝕂) a' b hs1_lt_log2
  have hz_mult : ‖z‖ ≤ 23/11 * s := by
    have h1 : 3 * (‖a'‖ + ‖b‖)^2 / (2 - Real.exp (‖a'‖ + ‖b‖)) ≤ 12 * s / 11 := by
      rw [div_le_iff₀ hdenom₁]
      nlinarith [hdenom_lb, hs1_nn, sq_nonneg (‖a'‖ + ‖b‖), hs1_le, hs_nn,
        mul_nonneg hs1_nn hs_nn, hab]
    calc ‖z‖ = ‖(z - (a' + b)) + (a' + b)‖ := by congr 1; abel
      _ ≤ ‖z - (a' + b)‖ + ‖a' + b‖ := norm_add_le _ _
      _ ≤ 12 * s / 11 + s := by
          have hsum : ‖a' + b‖ ≤ s := by linarith [hs1_le, norm_add_le a' b]
          linarith
      _ = 23/11 * s := by ring
  have hz1_le : ‖z₁‖ ≤ 3 * s / 2 + s^2 / 2 := by
    rw [hz1_def]
    calc ‖(a' + b) + V₂‖ ≤ ‖a' + b‖ + ‖V₂‖ := norm_add_le _ _
      _ ≤ 3 * s / 2 + s^2 / 2 := by linarith
  have hM_le : ‖z‖ + ‖z₁‖ + ‖a'‖ ≤ 5 * s := by
    have hs2_le' : s^2 ≤ s/4 := by nlinarith [hs_lt, hs_nn, sq_nonneg s]
    linarith
  have hM_nn : (0 : ℝ) ≤ ‖z‖ + ‖z₁‖ + ‖a'‖ := by positivity
  -- LipPiece bound.
  have hLip : ‖bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 z₁ a'‖ ≤
              4000000 * s ^ 7 := by
    have h := norm_bch_quintic_term_diff_le (𝕂 := 𝕂) z z₁ a'
    have hM4 : (‖z‖ + ‖z₁‖ + ‖a'‖) ^ 4 ≤ (5 * s) ^ 4 :=
      pow_le_pow_left₀ hM_nn hM_le 4
    have hM4_eq : (5 * s) ^ 4 = 625 * s ^ 4 := by ring
    calc ‖bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 z₁ a'‖
        ≤ (‖z‖ + ‖z₁‖ + ‖a'‖) ^ 4 * ‖z - z₁‖ := h
      _ ≤ (5 * s) ^ 4 * (6000 * s ^ 3) := by
          apply mul_le_mul hM4 hWRest_le (norm_nonneg _) (by positivity)
      _ = 625 * s ^ 4 * (6000 * s ^ 3) := by rw [hM4_eq]
      _ = 3750000 * s ^ 7 := by ring
      _ ≤ 4000000 * s ^ 7 := by nlinarith [hs7_nn]
  -- LinResidual bound.
  have hLin : ‖C5_LinResidual_polynomial 𝕂 a b‖ ≤ 1 * s ^ 7 :=
    norm_C5_LinResidual_polynomial_le (𝕂 := 𝕂) a b hab
  -- Combine: C5_diff_residual = LipPiece + LinResidual.
  have hAlg := C5_LinResidual_at_V2_eq_polynomial (𝕂 := 𝕂) a b
  simp only [show ((2 : 𝕂)⁻¹ • a : 𝔸) = a' from rfl,
             show ((2 : 𝕂)⁻¹ • (a' * b - b * a') : 𝔸) = V₂ from rfl,
             show (a' + b) + V₂ = z₁ from rfl] at hAlg
  -- Use linear_combination directly without set LhsPoly. The polynomial is inlined.
  have hsplit : ((bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a') -
        ((-14 / 46080 : 𝕂) • (a * a * a * a * b * b) +
        (46 / 46080 : 𝕂) • (a * a * a * b * a * b) +
        (10 / 46080 : 𝕂) • (a * a * a * b * b * a) +
        (28 / 46080 : 𝕂) • (a * a * a * b * b * b) +
        (-54 / 46080 : 𝕂) • (a * a * b * a * a * b) +
        (-30 / 46080 : 𝕂) • (a * a * b * a * b * a) +
        (-52 / 46080 : 𝕂) • (a * a * b * a * b * b) +
        (-12 / 46080 : 𝕂) • (a * a * b * b * a * b) +
        (-20 / 46080 : 𝕂) • (a * a * b * b * b * a) +
        (-8 / 46080 : 𝕂) • (a * a * b * b * b * b) +
        (36 / 46080 : 𝕂) • (a * b * a * a * a * b) +
        (-32 / 46080 : 𝕂) • (a * b * a * a * b * b) +
        (30 / 46080 : 𝕂) • (a * b * a * b * a * a) +
        (128 / 46080 : 𝕂) • (a * b * a * b * a * b) +
        (40 / 46080 : 𝕂) • (a * b * a * b * b * a) +
        (32 / 46080 : 𝕂) • (a * b * a * b * b * b) +
        (-10 / 46080 : 𝕂) • (a * b * b * a * a * a) +
        (-32 / 46080 : 𝕂) • (a * b * b * a * a * b) +
        (-40 / 46080 : 𝕂) • (a * b * b * a * b * a) +
        (-48 / 46080 : 𝕂) • (a * b * b * a * b * b) +
        (20 / 46080 : 𝕂) • (a * b * b * b * a * a) +
        (32 / 46080 : 𝕂) • (a * b * b * b * a * b) +
        (-36 / 46080 : 𝕂) • (b * a * a * a * b * a) +
        (54 / 46080 : 𝕂) • (b * a * a * b * a * a) +
        (32 / 46080 : 𝕂) • (b * a * a * b * b * a) +
        (-46 / 46080 : 𝕂) • (b * a * b * a * a * a) +
        (-128 / 46080 : 𝕂) • (b * a * b * a * b * a) +
        (12 / 46080 : 𝕂) • (b * a * b * b * a * a) +
        (-32 / 46080 : 𝕂) • (b * a * b * b * b * a) +
        (14 / 46080 : 𝕂) • (b * b * a * a * a * a) +
        (32 / 46080 : 𝕂) • (b * b * a * a * b * a) +
        (52 / 46080 : 𝕂) • (b * b * a * b * a * a) +
        (48 / 46080 : 𝕂) • (b * b * a * b * b * a) +
        (-28 / 46080 : 𝕂) • (b * b * b * a * a * a) +
        (-32 / 46080 : 𝕂) • (b * b * b * a * b * a) +
        (8 / 46080 : 𝕂) • (b * b * b * b * a * a))) =
                (bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 z₁ a') +
                C5_LinResidual_polynomial 𝕂 a b := by
    linear_combination (norm := abel) hAlg
  rw [hsplit]
  calc ‖(bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 z₁ a') +
        C5_LinResidual_polynomial 𝕂 a b‖
      ≤ ‖bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 z₁ a'‖ +
        ‖C5_LinResidual_polynomial 𝕂 a b‖ := norm_add_le _ _
    _ ≤ 4000000 * s ^ 7 + 1 * s ^ 7 := add_le_add hLip hLin
    _ = 4000001 * s ^ 7 := by ring
    _ ≤ 5000000 * s ^ 7 := by nlinarith [hs7_nn]


/-! ### T2-F7e Phase E.2 step 5: Group C+D combined bound (proved theorem)

Replaces the previous `symmetric_bch_quintic_group_CD_axiom` with a proved
theorem combining:
- `norm_R_T5_sept_le` (≤ 7·10⁶·s⁷, proved)
- `norm_R_T6_sept_le` (≤ 10⁶·s⁷, proved)
- `symmetric_bch_quintic_C5_diff_residual_le` (≤ 5·10⁶·s⁷, proved)

via `group_CD_eq_three_residuals` (algebraic identity) + triangle inequality.
Total bound: 7·10⁶ + 10⁶ + 5·10⁶ = 1.3·10⁷·s⁷ ≤ 10⁸·s⁷ (matches old axiom). -/

set_option maxHeartbeats 800000 in
private theorem symmetric_bch_quintic_group_CD_le
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let a' : 𝔸 := (2 : 𝕂)⁻¹ • a
    let z := bch (𝕂 := 𝕂) a' b
    let DC_a : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a
    ‖-- Group C: Phase B deg-5 cancellation group (4 sub-pieces)
     (bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
       -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
     (bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') +
     (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b) +
     -symmetric_bch_quintic_correction_poly 𝕂 a b +
     -- Group D: Phase C deg-6 cancellation group (4 sub-pieces)
     (2 : 𝕂)⁻¹ • (bch_quintic_term 𝕂 a' b * a' - a' * bch_quintic_term 𝕂 a' b) +
     bch_sextic_term 𝕂 a' b +
     bch_sextic_term 𝕂 (a' + b) a' +
     (bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a')‖ ≤
      100000000 * (‖a‖ + ‖b‖) ^ 7 := by
  intro a' z DC_a
  -- Apply algebraic identity: Group C + Group D = R_T5_sept + R_T6_sept + C5_diff_residual.
  have hAlg := group_CD_eq_three_residuals (𝕂 := 𝕂) a b
  -- Establish the 3 residual bounds (each has its own internal let-bindings).
  have hT5 := norm_R_T5_sept_le (𝕂 := 𝕂) a b hab
  have hT6 := norm_R_T6_sept_le (𝕂 := 𝕂) a b hab
  have hC5 := symmetric_bch_quintic_C5_diff_residual_le (𝕂 := 𝕂) a b hab
  -- Set local names mirroring hAlg's RHS structure (matches let-bindings of hT5/hT6/hC5).
  set V₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a') with hV2_def
  set V₃ : 𝔸 := bch_cubic_term 𝕂 a' b with hV3_def
  set V₄ : 𝔸 := bch_quartic_term 𝕂 a' b with hV4_def
  set x : 𝔸 := a' + b with hx_def
  -- Triangle inequality: ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖.
  -- After rw [hAlg], goal is ‖R_T5_sept + R_T6_sept + C5_diff_residual‖ ≤ 10⁸·s⁷.
  rw [hAlg]
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
  -- Use 2 successive norm_add_le applications.
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
  -- Now goal: ‖R_T5‖ + ‖R_T6‖ + ‖C5_diff‖ ≤ 10⁸·s⁷.
  calc _ ≤ 7000000 * s ^ 7 + 1000000 * s ^ 7 + 5000000 * s ^ 7 :=
        add_le_add (add_le_add hT5 hT6) hC5
    _ = 13000000 * s ^ 7 := by ring
    _ ≤ 100000000 * s ^ 7 := by nlinarith [hs7_nn]

-- Quintic Taylor bridge for the 3-factor symmetric BCH:
-- ‖symmetric_bch_cubic(a,b) − symmetric_bch_cubic_poly(a,b)
--   − symmetric_bch_quintic_poly(a,b)‖ ≤ 2·10¹⁰ · (‖a‖+‖b‖)⁷ for ‖a‖+‖b‖<1/4.
-- Proof: 13-piece extended hdecomp (Phase D), bounding via Phase A septic
-- remainders, Phase E.1 inline (Group A bracket + Group B C₆ pieces), and the
-- Group C+D sub-axiom (Phase E.2 stepping-stone). Total ≤ 1.21·10¹⁰·s⁷ ≤ 2·10¹⁰·s⁷.
include 𝕂 in
set_option maxHeartbeats 1600000 in
theorem norm_symmetric_bch_quintic_sub_poly_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b -
       symmetric_bch_quintic_poly 𝕂 a b‖ ≤
      20000000000 * (‖a‖ + ‖b‖) ^ 7 := by
  -- SETUP: a' = ½a, s = ‖a‖+‖b‖, s₁ = ‖a'‖+‖b‖ ≤ s, z = bch(a', b)
  set a' : 𝔸 := (2 : 𝕂)⁻¹ • a with ha'_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set s₁ := ‖a'‖ + ‖b‖ with hs₁_def
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ ‖a‖ / 2 := by
    calc ‖a'‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt : s < 1 / 4 := hab
  have ha_s : ‖a‖ ≤ s := by have := norm_nonneg b; linarith
  have hb_s : ‖b‖ ≤ s := by have := norm_nonneg a; linarith
  have ha'_s : ‖a'‖ ≤ s / 2 := by
    calc ‖a'‖ ≤ ‖a‖ / 2 := ha'_le
      _ ≤ s / 2 := by linarith
  have hs₁_le : s₁ ≤ s := by
    show ‖a'‖ + ‖b‖ ≤ ‖a‖ + ‖b‖; linarith [ha'_le, norm_nonneg a]
  have hs₁_nn : 0 ≤ s₁ := by positivity
  have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
  -- Inner BCH: z = bch(a', b)
  set z := bch (𝕂 := 𝕂) a' b with hz_def
  -- Septic R₁ and R₂ definitions matching the hdecomp.
  set R₁_sept := z - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a') -
                 bch_cubic_term 𝕂 a' b - bch_quartic_term 𝕂 a' b -
                 bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b with hR1_sept_def
  set R₂_sept := bch (𝕂 := 𝕂) z a' - (z + a') -
                 (2 : 𝕂)⁻¹ • (z * a' - a' * z) -
                 bch_cubic_term 𝕂 z a' - bch_quartic_term 𝕂 z a' -
                 bch_quintic_term 𝕂 z a' - bch_sextic_term 𝕂 z a' with hR2_sept_def
  set DC_a : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a with hDC_a_def
  -- APPLY hdecomp: rewrite the LHS via the 13-piece decomposition.
  have hdecomp := symmetric_bch_quintic_extended_hdecomp (𝕂 := 𝕂) a b
  simp only [show ((2 : 𝕂)⁻¹ • a : 𝔸) = a' from rfl,
             show bch (𝕂 := 𝕂) a' b = z from rfl,
             ← hR1_sept_def, ← hR2_sept_def, ← hDC_a_def] at hdecomp
  rw [hdecomp]
  -- TERM 1: ‖R₁_sept‖ ≤ 1.5·10⁶·s⁷ (Phase A inner)
  have hR1_le : ‖R₁_sept‖ ≤ 1500000 * s ^ 7 := by
    have h := norm_bch_inner_septic_remainder_le (𝕂 := 𝕂) a b hab
    rw [hR1_sept_def]
    -- a' := 2⁻¹•a and z := bch a' b are let-bindings; definitionally equal
    -- to the explicit forms in the Phase A statement. `convert` closes via rfl.
    convert h using 2
  -- TERM 2: ‖R₂_sept‖ ≤ 1.2·10¹⁰·s⁷ (Phase A outer)
  have hR2_le : ‖R₂_sept‖ ≤ 12000000000 * s ^ 7 := by
    have h := norm_bch_outer_septic_remainder_le (𝕂 := 𝕂) a b hab
    rw [hR2_sept_def]
    convert h using 2
  -- TERM 3: ‖½·(R₁_sept·a' - a'·R₁_sept)‖ ≤ ‖R₁_sept‖·‖a'‖ ≤ 1.875·10⁵·s⁷
  -- Using ‖R₁_sept‖ ≤ 1.5·10⁶·s⁷ and ‖a'‖ ≤ s/2 ≤ 1/8.
  have hT3 : ‖(2 : 𝕂)⁻¹ • (R₁_sept * a' - a' * R₁_sept)‖ ≤ 187500 * s ^ 7 := by
    calc ‖(2 : 𝕂)⁻¹ • (R₁_sept * a' - a' * R₁_sept)‖
        ≤ ‖R₁_sept‖ * ‖a'‖ := norm_half_smul_bracket_le R₁_sept a'
      _ ≤ (1500000 * s ^ 7) * (s / 2) :=
          mul_le_mul hR1_le ha'_s (norm_nonneg _) (by positivity)
      _ ≤ 187500 * s ^ 7 := by nlinarith [hs7_nn, hs_lt]
  -- TERM 4: ‖½·(C₆(a',b)·a' - a'·C₆(a',b))‖ ≤ ‖C₆(a',b)‖·‖a'‖ ≤ s⁶·(s/2) = s⁷/2 ≤ s⁷
  have hC6_ab_le : ‖bch_sextic_term 𝕂 a' b‖ ≤ s ^ 6 := by
    calc ‖bch_sextic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 6 := norm_bch_sextic_term_le a' b
      _ = s₁ ^ 6 := by rw [← hs₁_def]
      _ ≤ s ^ 6 := pow_le_pow_left₀ hs₁_nn hs₁_le 6
  have hT4 : ‖(2 : 𝕂)⁻¹ • (bch_sextic_term 𝕂 a' b * a' -
                            a' * bch_sextic_term 𝕂 a' b)‖ ≤ s ^ 7 := by
    calc ‖(2 : 𝕂)⁻¹ • (bch_sextic_term 𝕂 a' b * a' -
                        a' * bch_sextic_term 𝕂 a' b)‖
        ≤ ‖bch_sextic_term 𝕂 a' b‖ * ‖a'‖ :=
          norm_half_smul_bracket_le (bch_sextic_term 𝕂 a' b) a'
      _ ≤ s ^ 6 * (s / 2) :=
          mul_le_mul hC6_ab_le ha'_s (norm_nonneg _) (by positivity)
      _ ≤ s ^ 7 := by nlinarith [hs7_nn, hs_lt]
  -- SETUP for TERM 5: bounds on ‖z‖, ‖a'+b‖, ‖z-(a'+b)‖.
  have hln2 : (1 : ℝ) / 4 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    linarith [real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1:ℝ)/4 < 5/6)]
  have hs₁_lt_log2 : s₁ < Real.log 2 := by linarith
  have hexp_s₁_lt : Real.exp s₁ < 2 := by
    calc _ < Real.exp (Real.log 2) := Real.exp_strictMono hs₁_lt_log2
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith
  have hexp_le : Real.exp s₁ ≤ 1 + s₁ + s₁ ^ 2 := by
    nlinarith [real_exp_third_order_le_cube hs₁_nn (by linarith : s₁ < 5/6)]
  have hdenom_lb : (11 : ℝ) / 16 ≤ 2 - Real.exp s₁ := by nlinarith
  have hW_le : ‖z - (a' + b)‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    rw [hz_def]; exact norm_bch_sub_add_le (𝕂 := 𝕂) a' b hs₁_lt_log2
  have hW_s2 : ‖z - (a' + b)‖ ≤ 48 / 11 * s ^ 2 := by
    have hs₁_sq_le : s₁ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs₁_nn hs₁_le 2
    calc ‖z - (a' + b)‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) := hW_le
      _ ≤ 3 * s ^ 2 / (11 / 16) := by
          apply div_le_div₀ (by positivity) _ (by norm_num) hdenom_lb
          exact mul_le_mul_of_nonneg_left hs₁_sq_le (by norm_num)
      _ = 48 / 11 * s ^ 2 := by ring
  have hquad_bound : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 3 / 11 := by
    rw [div_le_div_iff₀ hdenom₁ (by norm_num : (0:ℝ) < 11)]
    nlinarith [sq_nonneg s₁, sq_nonneg (1/4 - s₁)]
  have hz_le : ‖z‖ ≤ s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    calc ‖z‖ = ‖(z - (a' + b)) + (a' + b)‖ := by congr 1; abel
      _ ≤ ‖z - (a' + b)‖ + ‖a' + b‖ := norm_add_le _ _
      _ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) + s₁ := by
          have hsum : ‖a' + b‖ ≤ s₁ := norm_add_le _ _
          linarith
      _ = s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by ring
  have hz_mult : ‖z‖ ≤ 23/11 * s := by
    have h1 : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 12 * s / 11 := by
      rw [div_le_iff₀ hdenom₁]
      nlinarith [hdenom_lb, hs₁_nn, sq_nonneg s₁, hs₁_le, hs_nn,
        mul_nonneg hs₁_nn hs_nn, hab]
    calc ‖z‖ ≤ s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := hz_le
      _ ≤ s + 12 * s / 11 := by linarith
      _ = 23/11 * s := by ring
  have hp_s : ‖a' + b‖ ≤ 3 / 2 * s := by
    calc ‖a' + b‖ ≤ ‖a'‖ + ‖b‖ := norm_add_le _ _
      _ ≤ s / 2 + s := by linarith
      _ = 3 / 2 * s := by ring
  -- TERM 5: ‖C₆(z, a') - C₆(a'+b, a')‖ ≤ M⁵·‖z-(a'+b)‖, with M ≤ (45/11)·s.
  -- M = ‖z‖+‖a'+b‖+‖a'‖ ≤ 23s/11 + 3s/2 + s/2 = (46/22 + 33/22 + 11/22)s = (90/22)s = (45/11)s.
  have hM_le : ‖z‖ + ‖a' + b‖ + ‖a'‖ ≤ 45/11 * s := by
    have h1 : ‖z‖ + ‖a' + b‖ + ‖a'‖ ≤ 23/11 * s + 3/2 * s + s/2 := by
      linarith [hz_mult, hp_s, ha'_s]
    linarith
  have hM_nn : (0 : ℝ) ≤ ‖z‖ + ‖a' + b‖ + ‖a'‖ := by positivity
  have hT5 : ‖bch_sextic_term 𝕂 z a' - bch_sextic_term 𝕂 (a' + b) a'‖ ≤
              5500 * s ^ 7 := by
    have h := norm_bch_sextic_term_diff_le (𝕂 := 𝕂) z (a' + b) a'
    -- h: ‖.‖ ≤ (‖z‖+‖a'+b‖+‖a'‖)^5 · ‖z-(a'+b)‖
    -- Bound: (45/11·s)^5 · (48/11·s²) = (45/11)^5·(48/11)·s^7
    --      ≤ 1146·(48/11)·s^7 ≈ 5001·s^7 < 5500·s^7.
    have hM_pow_le : (‖z‖ + ‖a' + b‖ + ‖a'‖) ^ 5 ≤ (45/11 * s) ^ 5 :=
      pow_le_pow_left₀ hM_nn hM_le 5
    have hM_pow_eq : (45/11 * s) ^ 5 = (45/11 : ℝ) ^ 5 * s ^ 5 := by ring
    have h_45_5 : ((45 : ℝ) / 11) ^ 5 ≤ 1146 := by norm_num
    have hs5_nn : (0 : ℝ) ≤ s ^ 5 := pow_nonneg hs_nn 5
    calc _ ≤ (‖z‖ + ‖a' + b‖ + ‖a'‖) ^ 5 * ‖z - (a' + b)‖ := h
      _ ≤ (45/11 * s) ^ 5 * (48/11 * s ^ 2) := by
          apply mul_le_mul hM_pow_le hW_s2 (norm_nonneg _) (by positivity)
      _ = (45/11 : ℝ) ^ 5 * s ^ 5 * (48/11 * s ^ 2) := by rw [hM_pow_eq]
      _ ≤ 1146 * s ^ 5 * (48/11 * s ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right h_45_5 hs5_nn
      _ ≤ 5500 * s ^ 7 := by nlinarith [hs7_nn]
  -- GROUP C+D: combined bound via proved theorem (Phase E.2 step 5),
  -- which uses R_T5_sept + R_T6_sept (both proved) + C5_diff_residual axiom.
  have hCD := symmetric_bch_quintic_group_CD_le (𝕂 := 𝕂) a b hab
  simp only [show ((2 : 𝕂)⁻¹ • a : 𝔸) = a' from rfl,
             show bch (𝕂 := 𝕂) a' b = z from rfl,
             ← hDC_a_def] at hCD
  -- Names for the 5 individual pieces (Group A 3 + Group B 2) and the cd-sum.
  set T₁ := R₁_sept with hT₁
  set T₂ := R₂_sept with hT₂
  set T₃ : 𝔸 := (2 : 𝕂)⁻¹ • (R₁_sept * a' - a' * R₁_sept) with hT₃
  set T₄ : 𝔸 := (2 : 𝕂)⁻¹ • (bch_sextic_term 𝕂 a' b * a' -
                              a' * bch_sextic_term 𝕂 a' b) with hT₄
  set T₅ : 𝔸 := bch_sextic_term 𝕂 z a' - bch_sextic_term 𝕂 (a' + b) a' with hT₅
  -- The 8 cd pieces (Group C 4 + Group D 4) appear in the goal in the same form
  -- as in hCD's LHS. We re-associate the 13-piece sum to (T₁..T₅) + (cd-sum).
  set CD_SUM : 𝔸 :=
      (bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
        -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
      (bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') +
      (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b) +
      -symmetric_bch_quintic_correction_poly 𝕂 a b +
      (2 : 𝕂)⁻¹ • (bch_quintic_term 𝕂 a' b * a' - a' * bch_quintic_term 𝕂 a' b) +
      bch_sextic_term 𝕂 a' b +
      bch_sextic_term 𝕂 (a' + b) a' +
      (bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a') with hCD_SUM
  -- hCD now bounds CD_SUM via its definition.
  have hCD_le : ‖CD_SUM‖ ≤ 100000000 * s ^ 7 := by rw [hCD_SUM]; exact hCD
  -- Re-associate the 13-piece goal sum as (T₁..T₅) + CD_SUM.
  -- The cd pieces in the goal are still in unfolded form (set didn't fold the sum).
  have hreorg :
      T₁ + T₂ + T₃ + T₄ + T₅ +
      (bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
        -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
      (bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') +
      (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b) +
      -symmetric_bch_quintic_correction_poly 𝕂 a b +
      (2 : 𝕂)⁻¹ • (bch_quintic_term 𝕂 a' b * a' - a' * bch_quintic_term 𝕂 a' b) +
      bch_sextic_term 𝕂 a' b +
      bch_sextic_term 𝕂 (a' + b) a' +
      (bch_quintic_term 𝕂 z a' - bch_quintic_term 𝕂 (a' + b) a')
      = (T₁ + T₂ + T₃ + T₄ + T₅) + CD_SUM := by
    rw [hCD_SUM]; abel
  rw [hreorg]
  -- Triangle: ‖(T₁+T₂+T₃+T₄+T₅) + CD_SUM‖ ≤ ‖T₁‖+...+‖T₅‖+‖CD_SUM‖
  have hsum_le : ‖(T₁ + T₂ + T₃ + T₄ + T₅) + CD_SUM‖ ≤
      ‖T₁‖ + ‖T₂‖ + ‖T₃‖ + ‖T₄‖ + ‖T₅‖ + ‖CD_SUM‖ := by
    have a5 := norm_add_le (T₁ + T₂ + T₃ + T₄ + T₅) CD_SUM
    have a4 := norm_add_le (T₁ + T₂ + T₃ + T₄) T₅
    have a3 := norm_add_le (T₁ + T₂ + T₃) T₄
    have a2 := norm_add_le (T₁ + T₂) T₃
    have a1 := norm_add_le T₁ T₂
    linarith
  calc ‖(T₁ + T₂ + T₃ + T₄ + T₅) + CD_SUM‖
      ≤ ‖T₁‖ + ‖T₂‖ + ‖T₃‖ + ‖T₄‖ + ‖T₅‖ + ‖CD_SUM‖ := hsum_le
    _ ≤ 1500000 * s ^ 7 + 12000000000 * s ^ 7 + 187500 * s ^ 7 +
        s ^ 7 + 5500 * s ^ 7 + 100000000 * s ^ 7 := by
          linarith [hR1_le, hR2_le, hT3, hT4, hT5, hCD_le]
    _ = 12101693001 * s ^ 7 := by ring
    _ ≤ 20000000000 * s ^ 7 := by nlinarith [hs7_nn]

end QuinticTaylorBridge

end BCH
