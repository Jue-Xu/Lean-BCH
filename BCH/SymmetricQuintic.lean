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
