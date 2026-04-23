/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH Palindromic: structural identities for palindromic exp-products

This file establishes structural identities for the Suzuki-style 5-block palindromic
exp-product used in Trotter–Suzuki S₄ splitting. The main result is the reflection
identity `suzuki5Product A B p τ · suzuki5Product A B p (-τ) = 1`, which is the
algebraic core underlying oddness arguments for symmetric splittings.

The product is defined to match `Lean-Trotter`'s `s4Func`:
  S(τ) = e(p/2·τ,A)·e(p·τ,B)·e(p·τ,A)·e(p·τ,B)·e((1-3p)/2·τ,A)·e((1-4p)·τ,B)
       · e((1-3p)/2·τ,A)·e(p·τ,B)·e(p·τ,A)·e(p·τ,B)·e(p/2·τ,A)
where e(c,X) := exp(c • X). The coefficient list (p/2, p, p, p, (1-3p)/2, (1-4p),
(1-3p)/2, p, p, p, p/2) is palindromic, so S(-τ) = S(τ)⁻¹.

## Main definitions

* `suzuki5Product A B p τ`: 11-factor palindromic exp-product.

## Main results

* `exp_smul_mul_exp_neg_smul`: `exp((c·τ)•x) · exp((c·(-τ))•x) = 1`.
* `suzuki5Product_mul_neg_eq_one`: `S(τ) · S(-τ) = 1`.
-/

import BCH.Basic

namespace BCH

noncomputable section

open NormedSpace

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### Basic exp cancellation helpers -/

include 𝕂 in
/-- `exp(x) · exp(-x) = 1` in any complete normed algebra. -/
theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl x)), add_neg_cancel, exp_zero]

include 𝕂 in
/-- `exp(-x) · exp(x) = 1` in any complete normed algebra. -/
theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl x)), neg_add_cancel, exp_zero]

include 𝕂 in
/-- Specialization to smul: `exp((c·τ)•x) · exp((c·(-τ))•x) = 1`. -/
theorem exp_smul_mul_exp_neg_smul (c : 𝕂) (x : 𝔸) (τ : 𝕂) :
    exp ((c * τ) • x) * exp ((c * -τ) • x) = 1 := by
  have h : (c * -τ) • x = -((c * τ) • x) := by
    rw [mul_neg, neg_smul]
  rw [h]
  exact exp_mul_exp_neg (𝕂 := 𝕂) _

/-! ### Suzuki 5-block palindromic product -/

/-- The 11-factor palindromic Suzuki S₄ exp-product, matching `Lean-Trotter`'s
`s4Func A B p τ`. Parameterized over the scalar field `𝕂`; Trotter uses `𝕂 = ℝ`. -/
def suzuki5Product (A B : 𝔸) (p τ : 𝕂) : 𝔸 :=
  exp ((p / 2 * τ) • A) * exp ((p * τ) • B) *
  exp ((p * τ) • A) * exp ((p * τ) • B) *
  exp (((1 - 3 * p) / 2 * τ) • A) * exp (((1 - 4 * p) * τ) • B) *
  exp (((1 - 3 * p) / 2 * τ) • A) * exp ((p * τ) • B) *
  exp ((p * τ) • A) * exp ((p * τ) • B) *
  exp ((p / 2 * τ) • A)

/-! ### Reflection identity

The palindromic coefficient structure forces `S(τ) · S(-τ) = 1`: the 11 pairs
`(position k of S(τ), position 12-k of S(-τ))` telescope to 1 from the center outward.
-/

include 𝕂 in
/-- The Suzuki 5-block palindromic reflection identity: `S(τ) · S(-τ) = 1`.

This expresses the palindromic structure algebraically. It gives
`S(-τ) = S(τ)⁻¹` and is the foundation for oddness statements about `log S(τ)`. -/
theorem suzuki5Product_mul_neg_eq_one (A B : 𝔸) (p τ : 𝕂) :
    suzuki5Product A B p τ * suzuki5Product A B p (-τ) = 1 := by
  unfold suzuki5Product
  -- Name the 11 factors of S(τ) and of S(-τ)
  set f₁ : 𝔸 := exp ((p / 2 * τ) • A) with hf₁
  set f₂ : 𝔸 := exp ((p * τ) • B) with hf₂
  set f₃ : 𝔸 := exp ((p * τ) • A) with hf₃
  set f₄ : 𝔸 := exp ((p * τ) • B) with hf₄
  set f₅ : 𝔸 := exp (((1 - 3 * p) / 2 * τ) • A) with hf₅
  set f₆ : 𝔸 := exp (((1 - 4 * p) * τ) • B) with hf₆
  set f₇ : 𝔸 := exp (((1 - 3 * p) / 2 * τ) • A) with hf₇
  set f₈ : 𝔸 := exp ((p * τ) • B) with hf₈
  set f₉ : 𝔸 := exp ((p * τ) • A) with hf₉
  set f₁₀ : 𝔸 := exp ((p * τ) • B) with hf₁₀
  set f₁₁ : 𝔸 := exp ((p / 2 * τ) • A) with hf₁₁
  set g₁ : 𝔸 := exp ((p / 2 * -τ) • A) with hg₁
  set g₂ : 𝔸 := exp ((p * -τ) • B) with hg₂
  set g₃ : 𝔸 := exp ((p * -τ) • A) with hg₃
  set g₄ : 𝔸 := exp ((p * -τ) • B) with hg₄
  set g₅ : 𝔸 := exp (((1 - 3 * p) / 2 * -τ) • A) with hg₅
  set g₆ : 𝔸 := exp (((1 - 4 * p) * -τ) • B) with hg₆
  set g₇ : 𝔸 := exp (((1 - 3 * p) / 2 * -τ) • A) with hg₇
  set g₈ : 𝔸 := exp ((p * -τ) • B) with hg₈
  set g₉ : 𝔸 := exp ((p * -τ) • A) with hg₉
  set g₁₀ : 𝔸 := exp ((p * -τ) • B) with hg₁₀
  set g₁₁ : 𝔸 := exp ((p / 2 * -τ) • A) with hg₁₁
  -- Palindromic cancellation pairs: position k of S(τ) with position (12-k) of S(-τ).
  -- By palindrome c_k = c_{12-k} and X_k = X_{12-k}, so the arguments are negatives.
  have h_11_1 : f₁₁ * g₁ = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) (p / 2) A τ
  have h_10_2 : f₁₀ * g₂ = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) p B τ
  have h_9_3  : f₉ * g₃  = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) p A τ
  have h_8_4  : f₈ * g₄  = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) p B τ
  have h_7_5  : f₇ * g₅  = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) ((1 - 3 * p) / 2) A τ
  have h_6_6  : f₆ * g₆  = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) (1 - 4 * p) B τ
  have h_5_7  : f₅ * g₇  = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) ((1 - 3 * p) / 2) A τ
  have h_4_8  : f₄ * g₈  = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) p B τ
  have h_3_9  : f₃ * g₉  = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) p A τ
  have h_2_10 : f₂ * g₁₀ = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) p B τ
  have h_1_11 : f₁ * g₁₁ = 1 := exp_smul_mul_exp_neg_smul (𝕂 := 𝕂) (p / 2) A τ
  -- Telescoping cancellation. The goal has S(τ) and S(-τ) each written as a
  -- left-associated 11-fold product. Reassociate and cancel from the middle.
  -- The full product is
  --   f₁·f₂·…·f₁₁ · g₁·g₂·…·g₁₁
  -- We rewrite as  f₁·(f₂·(…(f₁₁·g₁)·g₂)·…·g₁₀)·g₁₁  and cancel innermost pairs.
  calc
    (f₁ * f₂ * f₃ * f₄ * f₅ * f₆ * f₇ * f₈ * f₉ * f₁₀ * f₁₁) *
      (g₁ * g₂ * g₃ * g₄ * g₅ * g₆ * g₇ * g₈ * g₉ * g₁₀ * g₁₁)
        = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * (f₈ * (f₉ * (f₁₀ *
            ((f₁₁ * g₁) * g₂) * g₃) * g₄) * g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              noncomm_ring
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * (f₈ * (f₉ * (f₁₀ *
            (1 * g₂) * g₃) * g₄) * g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [h_11_1]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * (f₈ * (f₉ * ((f₁₀ * g₂) * g₃) *
            g₄) * g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * (f₈ * (f₉ * (1 * g₃) *
            g₄) * g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [h_10_2]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * (f₈ * ((f₉ * g₃) *
            g₄) * g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * (f₈ * (1 *
            g₄) * g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [h_9_3]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * ((f₈ *
            g₄) * g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (f₇ * (1 *
            g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [h_8_4]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * ((f₇ *
            g₅) * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (f₆ * (1 * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [h_7_5]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * ((f₆ * g₆) * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (f₅ * (1 * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [h_6_6]
      _ = f₁ * (f₂ * (f₃ * (f₄ * ((f₅ * g₇) * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (f₃ * (f₄ * (1 * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [h_5_7]
      _ = f₁ * (f₂ * (f₃ * ((f₄ * g₈) * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (f₃ * (1 * g₉) * g₁₀) * g₁₁) := by
              rw [h_4_8]
      _ = f₁ * (f₂ * ((f₃ * g₉) * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (f₂ * (1 * g₁₀) * g₁₁) := by
              rw [h_3_9]
      _ = f₁ * ((f₂ * g₁₀) * g₁₁) := by
              rw [one_mul]
      _ = f₁ * (1 * g₁₁) := by
              rw [h_2_10]
      _ = f₁ * g₁₁ := by
              rw [one_mul]
      _ = 1 := h_1_11

/-! ### Small-coefficient regime for `suzuki5Product - 1`

To define `log(S(τ))` via the existing `logOnePlus` series, we need `‖S(τ) - 1‖ < 1`.
We bound this by a product-of-exps estimate:

  `‖S(τ) - 1‖ ≤ exp(∑ᵢ ‖zᵢ‖) - 1`

where `zᵢ` are the 11 exponent arguments. Combined with
`∑ᵢ ‖zᵢ‖ ≤ ‖τ‖·((3‖p‖+‖1-3p‖)·‖A‖ + (4‖p‖+‖1-4p‖)·‖B‖)`,
this gives an explicit regime in which the log is defined.
-/

include 𝕂 in
/-- Inductive step for bounding `‖∏ᵢ exp(xᵢ) - 1‖`: if `‖y - 1‖ ≤ exp(r) - 1`
with `r ≥ 0`, then appending one more factor `exp x` on the right gives
`‖y · exp(x) - 1‖ ≤ exp(r + ‖x‖) - 1`. -/
lemma norm_mul_exp_sub_one_le (y x : 𝔸) {r : ℝ} (hr : 0 ≤ r)
    (hy : ‖y - 1‖ ≤ Real.exp r - 1) :
    ‖y * exp x - 1‖ ≤ Real.exp (r + ‖x‖) - 1 := by
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hfactor : y * exp x - 1 = (y - 1) * exp x + (exp x - 1) := by
    rw [sub_mul, one_mul]; abel
  have hr_expm1_nn : 0 ≤ Real.exp r - 1 := by
    linarith [Real.add_one_le_exp r]
  have hexp_x_nn : 0 ≤ Real.exp ‖x‖ := (Real.exp_pos _).le
  have hexp_norm : ‖exp x‖ ≤ Real.exp ‖x‖ := norm_exp_le (𝕂 := 𝕂) x
  have hexp_sub_norm : ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := norm_exp_sub_one_le (𝕂 := 𝕂) x
  calc ‖y * exp x - 1‖
      = ‖(y - 1) * exp x + (exp x - 1)‖ := by rw [hfactor]
    _ ≤ ‖(y - 1) * exp x‖ + ‖exp x - 1‖ := norm_add_le _ _
    _ ≤ ‖y - 1‖ * ‖exp x‖ + ‖exp x - 1‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ (Real.exp r - 1) * Real.exp ‖x‖ + (Real.exp ‖x‖ - 1) := by
        gcongr
    _ = Real.exp (r + ‖x‖) - 1 := by rw [Real.exp_add]; ring

include 𝕂 in
/-- Norm bound on `‖suzuki5Product - 1‖` in terms of the 11 exponent argument norms. -/
theorem norm_suzuki5Product_sub_one_le (A B : 𝔸) (p τ : 𝕂) :
    ‖suzuki5Product A B p τ - 1‖ ≤
      Real.exp (‖(p / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ + ‖(p * τ) • B‖ +
                ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ +
                ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ +
                ‖(p * τ) • B‖ + ‖(p / 2 * τ) • A‖) - 1 := by
  unfold suzuki5Product
  set z₁ := (p / 2 * τ) • A with hz₁
  set z₂ := (p * τ) • B with hz₂
  set z₃ := (p * τ) • A with hz₃
  set z₄ := (p * τ) • B with hz₄
  set z₅ := ((1 - 3 * p) / 2 * τ) • A with hz₅
  set z₆ := ((1 - 4 * p) * τ) • B with hz₆
  set z₇ := ((1 - 3 * p) / 2 * τ) • A with hz₇
  set z₈ := (p * τ) • B with hz₈
  set z₉ := (p * τ) • A with hz₉
  set z₁₀ := (p * τ) • B with hz₁₀
  set z₁₁ := (p / 2 * τ) • A with hz₁₁
  -- Base: ‖exp z₁ - 1‖ ≤ exp ‖z₁‖ - 1
  have h1 : ‖exp z₁ - 1‖ ≤ Real.exp ‖z₁‖ - 1 := norm_exp_sub_one_le (𝕂 := 𝕂) _
  -- Chain via the helper lemma; r is the running sum of norms.
  have h2 : ‖exp z₁ * exp z₂ - 1‖ ≤ Real.exp (‖z₁‖ + ‖z₂‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (norm_nonneg _) h1
  have h3 : ‖exp z₁ * exp z₂ * exp z₃ - 1‖ ≤ Real.exp ((‖z₁‖ + ‖z₂‖) + ‖z₃‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h2
  have h4 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ - 1‖ ≤
      Real.exp (((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h3
  have h5 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ * exp z₅ - 1‖ ≤
      Real.exp ((((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) + ‖z₅‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h4
  have h6 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ * exp z₅ * exp z₆ - 1‖ ≤
      Real.exp (((((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) + ‖z₅‖) + ‖z₆‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h5
  have h7 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ * exp z₅ * exp z₆ * exp z₇ - 1‖ ≤
      Real.exp ((((((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) + ‖z₅‖) + ‖z₆‖) + ‖z₇‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h6
  have h8 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ * exp z₅ * exp z₆ * exp z₇ * exp z₈ - 1‖ ≤
      Real.exp (((((((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) + ‖z₅‖) + ‖z₆‖) + ‖z₇‖) + ‖z₈‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h7
  have h9 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ * exp z₅ * exp z₆ * exp z₇ * exp z₈ *
                exp z₉ - 1‖ ≤
      Real.exp ((((((((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) + ‖z₅‖) + ‖z₆‖) + ‖z₇‖) + ‖z₈‖) +
                ‖z₉‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h8
  have h10 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ * exp z₅ * exp z₆ * exp z₇ * exp z₈ *
                exp z₉ * exp z₁₀ - 1‖ ≤
      Real.exp (((((((((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) + ‖z₅‖) + ‖z₆‖) + ‖z₇‖) + ‖z₈‖) +
                ‖z₉‖) + ‖z₁₀‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h9
  have h11 : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ * exp z₅ * exp z₆ * exp z₇ * exp z₈ *
                exp z₉ * exp z₁₀ * exp z₁₁ - 1‖ ≤
      Real.exp ((((((((((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) + ‖z₅‖) + ‖z₆‖) + ‖z₇‖) + ‖z₈‖) +
                ‖z₉‖) + ‖z₁₀‖) + ‖z₁₁‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h10
  -- The target expression differs only by parenthesization of a sum.
  convert h11 using 2

/-- Total norm bound for the 11 exponent arguments of `suzuki5Product`,
    factored as `‖τ‖ · ((3‖p‖+‖1-3p‖)·‖A‖ + (4‖p‖+‖1-4p‖)·‖B‖)`. -/
noncomputable def suzuki5ArgNormBound (A B : 𝔸) (p τ : 𝕂) : ℝ :=
  ‖τ‖ * ((3 * ‖p‖ + ‖1 - 3 * p‖) * ‖A‖ + (4 * ‖p‖ + ‖1 - 4 * p‖) * ‖B‖)

include 𝕂 in
/-- The 11-factor sum of argument norms is bounded by `suzuki5ArgNormBound`. -/
lemma sum_arg_norms_le_bound (A B : 𝔸) (p τ : 𝕂) :
    ‖(p / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ + ‖(p * τ) • B‖ +
    ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ +
    ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ +
    ‖(p * τ) • B‖ + ‖(p / 2 * τ) • A‖ ≤ suzuki5ArgNormBound A B p τ := by
  unfold suzuki5ArgNormBound
  -- Each ‖c • X‖ ≤ ‖c‖ * ‖X‖
  have hpA : ‖(p / 2 * τ) • A‖ ≤ ‖p / 2 * τ‖ * ‖A‖ := norm_smul_le _ _
  have hpB : ‖(p * τ) • B‖ ≤ ‖p * τ‖ * ‖B‖ := norm_smul_le _ _
  have hpA' : ‖(p * τ) • A‖ ≤ ‖p * τ‖ * ‖A‖ := norm_smul_le _ _
  have h3pA : ‖((1 - 3 * p) / 2 * τ) • A‖ ≤ ‖(1 - 3 * p) / 2 * τ‖ * ‖A‖ := norm_smul_le _ _
  have h4pB : ‖((1 - 4 * p) * τ) • B‖ ≤ ‖(1 - 4 * p) * τ‖ * ‖B‖ := norm_smul_le _ _
  -- Compute the scalar norms: ‖p/2 · τ‖ = ‖p‖ · ‖τ‖ / 2, etc. (using RCLike/norm_mul/norm_div)
  have hnorm_half : ‖(p / 2 * τ : 𝕂)‖ = ‖p‖ * ‖τ‖ / 2 := by
    rw [norm_mul, norm_div, RCLike.norm_ofNat]; ring
  have hnorm_pτ : ‖(p * τ : 𝕂)‖ = ‖p‖ * ‖τ‖ := by rw [norm_mul]
  have hnorm_3p_half : ‖((1 - 3 * p) / 2 * τ : 𝕂)‖ = ‖1 - 3 * p‖ * ‖τ‖ / 2 := by
    rw [norm_mul, norm_div, RCLike.norm_ofNat]; ring
  have hnorm_4p : ‖((1 - 4 * p) * τ : 𝕂)‖ = ‖1 - 4 * p‖ * ‖τ‖ := by rw [norm_mul]
  -- Bound each term. `A` shows up at positions 1,3,5,7,9,11; `B` at 2,4,6,8,10.
  have hA_nn : 0 ≤ ‖A‖ := norm_nonneg _
  have hB_nn : 0 ≤ ‖B‖ := norm_nonneg _
  nlinarith [hpA, hpB, hpA', h3pA, h4pB, hA_nn, hB_nn,
             hnorm_half, hnorm_pτ, hnorm_3p_half, hnorm_4p,
             norm_nonneg ((p / 2 * τ : 𝕂)), norm_nonneg ((p * τ : 𝕂)),
             norm_nonneg ((1 - 3 * p : 𝕂)), norm_nonneg ((1 - 4 * p : 𝕂)),
             norm_nonneg (p : 𝕂), norm_nonneg (τ : 𝕂)]

include 𝕂 in
/-- **M2a**: In the regime `‖τ‖·((3‖p‖+‖1-3p‖)·‖A‖ + (4‖p‖+‖1-4p‖)·‖B‖) < log 2`,
we have `‖suzuki5Product A B p τ - 1‖ < 1`. This is the regime in which
`logOnePlus(suzuki5Product - 1)` is defined. -/
theorem norm_suzuki5Product_sub_one_lt_one (A B : 𝔸) (p τ : 𝕂)
    (h : suzuki5ArgNormBound A B p τ < Real.log 2) :
    ‖suzuki5Product A B p τ - 1‖ < 1 := by
  have hbound := norm_suzuki5Product_sub_one_le (𝕂 := 𝕂) A B p τ
  have hsum := sum_arg_norms_le_bound (𝕂 := 𝕂) A B p τ
  -- Combine: bound ≤ exp(sum) - 1 ≤ exp(suzuki5ArgNormBound) - 1
  have hstep1 : ‖suzuki5Product A B p τ - 1‖ ≤
      Real.exp (suzuki5ArgNormBound A B p τ) - 1 := by
    refine le_trans hbound ?_
    have := Real.exp_le_exp.mpr hsum
    linarith
  have hstep2 : Real.exp (suzuki5ArgNormBound A B p τ) < 2 := by
    calc Real.exp (suzuki5ArgNormBound A B p τ)
        < Real.exp (Real.log 2) := Real.exp_strictMono h
      _ = 2 := Real.exp_log (by norm_num)
  linarith

end

end BCH
