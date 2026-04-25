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

/-- **[Tier-2 axiom, pending]** — the quintic Taylor bridge for the 3-factor
symmetric BCH.

Asserts that after subtracting both the cubic polynomial
`symmetric_bch_cubic_poly` (line-3 Taylor coefficient) and the quintic
polynomial `symmetric_bch_quintic_poly` (line-5 Taylor coefficient, defined
above), the residual of `symmetric_bch_cubic a b` is `O(s⁷)`.

By palindromic symmetry of `log(exp(a/2)·exp(b)·exp(a/2))`, degrees 2, 4,
and 6 vanish identically (CAS-verified at
`Lean-Trotter/scripts/verify_strangblock_degree7.py`), so the first
non-zero residual is at degree 7.

The constant `10⁹` is a loose margin — degree 7 has 126 non-zero words in
`{a,b}`, and the geometric tail for `s < 1/4` contributes a small further
factor. A tighter version with `K·s⁷/(2−exp(s))` (analog of
`norm_bch_sextic_remainder_le`) would be possible, but the simpler `K·s⁷`
form suffices for B1.d and B2 downstream uses.

Introduced `private` so only the public derived
`norm_symmetric_bch_quintic_sub_poly_le` theorem appears in the API. -/
private axiom symmetric_bch_quintic_sub_poly_axiom
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b -
       symmetric_bch_quintic_poly 𝕂 a b‖ ≤
      1000000000 * (‖a‖ + ‖b‖) ^ 7

include 𝕂 in
/-- **Quintic Taylor bridge for the 3-factor symmetric BCH**:

    ‖symmetric_bch_cubic(a,b) − symmetric_bch_cubic_poly(a,b)
        − symmetric_bch_quintic_poly(a,b)‖ ≤ 10⁹ · (‖a‖+‖b‖)⁷

for `‖a‖+‖b‖ < 1/4`. Extends `norm_symmetric_bch_cubic_sub_poly_le`
(`Basic.lean`) by one degree higher, factoring out the τ⁵ coefficient
along with the τ³ coefficient.

**Status**: Currently derived from the scoped Tier-2 axiom
`symmetric_bch_quintic_sub_poly_axiom`. The public signature is stable so
downstream work (B1.d's `strangBlock_log` wrapper, B2's symbolic 5-factor
composition, Lean-Trotter's `bch_w4Deriv_quintic_level2`) depends only on
this theorem, not on the underlying axiom. Removing the axiom requires
the Tier 1/2/3 work described in the section header above. -/
theorem norm_symmetric_bch_quintic_sub_poly_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b -
       symmetric_bch_quintic_poly 𝕂 a b‖ ≤
      1000000000 * (‖a‖ + ‖b‖) ^ 7 :=
  symmetric_bch_quintic_sub_poly_axiom (𝕂 := 𝕂) a b hab

end QuinticTaylorBridge

end BCH
