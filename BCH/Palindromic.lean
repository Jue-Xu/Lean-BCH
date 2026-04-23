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

/-! ### Definition of `suzuki5_bch` and exp round-trip (M2b)

In the regime where `‖S(τ) - 1‖ < 1`, define
  `suzuki5_bch A B p τ := logOnePlus(suzuki5Product A B p τ - 1)`
and prove that `exp(suzuki5_bch A B p τ) = suzuki5Product A B p τ`, using the
existing `exp_logOnePlus : exp(logOnePlus x) = 1 + x` for `‖x‖ < 1`.
-/

/-- The Suzuki 5-block BCH element: the unique `Z` with `exp(Z) = suzuki5Product A B p τ`
in the small-coefficient regime. Defined as `logOnePlus(S(τ) - 1)`. -/
noncomputable def suzuki5_bch (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (p τ : 𝕂) : 𝔸 :=
  logOnePlus (𝕂 := 𝕂) (suzuki5Product A B p τ - 1)

include 𝕂 in
/-- **M2b** — exp round-trip: `exp(suzuki5_bch A B p τ) = suzuki5Product A B p τ`
in the small-coefficient regime `suzuki5ArgNormBound A B p τ < log 2`. -/
theorem exp_suzuki5_bch (A B : 𝔸) (p τ : 𝕂)
    (h : suzuki5ArgNormBound A B p τ < Real.log 2) :
    exp (suzuki5_bch 𝕂 A B p τ) = suzuki5Product A B p τ := by
  unfold suzuki5_bch
  have hnorm : ‖suzuki5Product A B p τ - 1‖ < 1 :=
    norm_suzuki5Product_sub_one_lt_one (𝕂 := 𝕂) A B p τ h
  rw [exp_logOnePlus (𝕂 := 𝕂) (suzuki5Product A B p τ - 1) hnorm]
  abel

/-! ### Oddness of suzuki5_bch (M3a)

The palindromic reflection identity `S(τ) · S(-τ) = 1` lifts to the log level:
`suzuki5_bch A B p (-τ) = -suzuki5_bch A B p τ`.

Proof structure: from `exp(Z) · exp(Z') = 1` (with `Z := suzuki5_bch τ`,
`Z' := suzuki5_bch (-τ)`) we derive `exp(Z') = exp(-Z)` by left-multiplying
by `exp(-Z)`. Then applying `logOnePlus_exp_sub_one` to both sides gives
`Z' = -Z`, provided `‖Z‖, ‖Z'‖ < log 2`.
-/

include 𝕂 in
/-- The argument-norm bound is invariant under `τ → -τ`. -/
lemma suzuki5ArgNormBound_neg (A B : 𝔸) (p τ : 𝕂) :
    suzuki5ArgNormBound A B p (-τ) = suzuki5ArgNormBound A B p τ := by
  unfold suzuki5ArgNormBound
  rw [norm_neg]

include 𝕂 in
/-- **M3a** — oddness: `suzuki5_bch A B p (-τ) = -suzuki5_bch A B p τ` in the regime
where (i) the coefficient regime `suzuki5ArgNormBound A B p τ < log 2` holds (which
is τ-symmetric), and (ii) both `‖suzuki5_bch(τ)‖` and `‖suzuki5_bch(-τ)‖` are `< log 2`
(needed for log injectivity). -/
theorem suzuki5_bch_neg (A B : 𝔸) (p τ : 𝕂)
    (hregime : suzuki5ArgNormBound A B p τ < Real.log 2)
    (hZτ : ‖suzuki5_bch 𝕂 A B p τ‖ < Real.log 2)
    (hZnegτ : ‖suzuki5_bch 𝕂 A B p (-τ)‖ < Real.log 2) :
    suzuki5_bch 𝕂 A B p (-τ) = -suzuki5_bch 𝕂 A B p τ := by
  set Z := suzuki5_bch 𝕂 A B p τ with hZ_def
  set Z' := suzuki5_bch 𝕂 A B p (-τ) with hZ'_def
  -- exp(Z) = S(τ), exp(Z') = S(-τ)
  have hexpZ : exp Z = suzuki5Product A B p τ :=
    exp_suzuki5_bch (𝕂 := 𝕂) A B p τ hregime
  have hexpZ' : exp Z' = suzuki5Product A B p (-τ) := by
    apply exp_suzuki5_bch (𝕂 := 𝕂) A B p (-τ)
    rw [suzuki5ArgNormBound_neg (𝕂 := 𝕂)]; exact hregime
  -- exp(Z) · exp(Z') = 1
  have hprod : exp Z * exp Z' = 1 := by
    rw [hexpZ, hexpZ']
    exact suzuki5Product_mul_neg_eq_one (𝕂 := 𝕂) A B p τ
  -- exp(-Z) · exp(Z) = 1
  have hneg_Z : exp (-Z) * exp Z = 1 := exp_neg_mul_exp (𝕂 := 𝕂) Z
  -- Derive exp(Z') = exp(-Z) via left-multiplying hprod by exp(-Z)
  have hexp_flip : exp Z' = exp (-Z) := by
    calc exp Z'
        = 1 * exp Z' := by rw [one_mul]
      _ = (exp (-Z) * exp Z) * exp Z' := by rw [hneg_Z]
      _ = exp (-Z) * (exp Z * exp Z') := by rw [mul_assoc]
      _ = exp (-Z) * 1 := by rw [hprod]
      _ = exp (-Z) := by rw [mul_one]
  -- Log injectivity on both sides
  have hlZ' : logOnePlus (𝕂 := 𝕂) (exp Z' - 1) = Z' :=
    logOnePlus_exp_sub_one (𝕂 := 𝕂) Z' hZnegτ
  have hlnegZ : logOnePlus (𝕂 := 𝕂) (exp (-Z) - 1) = -Z := by
    apply logOnePlus_exp_sub_one (𝕂 := 𝕂) (-Z)
    rw [norm_neg]; exact hZτ
  calc Z' = logOnePlus (𝕂 := 𝕂) (exp Z' - 1) := hlZ'.symm
    _ = logOnePlus (𝕂 := 𝕂) (exp (-Z) - 1) := by rw [hexp_flip]
    _ = -Z := hlnegZ

/-! ### Leading-order remainder for suzuki5_bch (M3b)

We prove `‖suzuki5_bch A B p τ - τ • (A+B)‖` is `O(τ²)` by splitting

  `‖log(1+(S-1)) - τ(A+B)‖ ≤ ‖log(1+(S-1)) - (S-1)‖ + ‖(S-1) - τ(A+B)‖`

Both pieces are `O(τ²)`:

1. `‖logOnePlus(y) - y‖ ≤ ‖y‖²/(1-‖y‖)` from `LogSeries.lean`.
2. `‖S(τ) - 1 - ∑ᵢzᵢ‖ ≤ exp(R) - 1 - R` proved by induction on the number of
   factors, using the three invariants (‖S_k‖ bound, ‖S_k-1‖ bound, linear bound).
3. `∑ᵢ zᵢ = τ•(A+B)` because the A-coefficients sum to 1 (p/2+p+(1-3p)/2+(1-3p)/2+p+p/2 = 1)
   and the B-coefficients sum to 1 (p+p+(1-4p)+p+p = 1).
-/

include 𝕂 in
/-- Multiplicative norm preservation: if `‖y‖ ≤ exp(r)`, then `‖y · exp(x)‖ ≤ exp(r+‖x‖)`. -/
lemma norm_mul_exp_le_of_norm_le (y x : 𝔸) {r : ℝ}
    (hy : ‖y‖ ≤ Real.exp r) :
    ‖y * exp x‖ ≤ Real.exp (r + ‖x‖) := by
  have hexp_x : ‖exp x‖ ≤ Real.exp ‖x‖ := norm_exp_le (𝕂 := 𝕂) x
  calc ‖y * exp x‖
      ≤ ‖y‖ * ‖exp x‖ := norm_mul_le _ _
    _ ≤ Real.exp r * Real.exp ‖x‖ :=
        mul_le_mul hy hexp_x (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (r + ‖x‖) := by rw [← Real.exp_add]

include 𝕂 in
/-- Three-invariant inductive step. Given bounds on `‖y‖`, `‖y-1‖`, and `‖y-1-u‖`
(the "linear remainder"), extending by one factor `exp(z)` preserves all three bounds
with `r` replaced by `r + ‖z‖` and `u` by `u + z`. -/
lemma norm_mul_exp_sub_linear_le (y u z : 𝔸) {r : ℝ} (hr : 0 ≤ r)
    (hy_norm : ‖y‖ ≤ Real.exp r)
    (hy_sub_one : ‖y - 1‖ ≤ Real.exp r - 1)
    (hy_lin : ‖y - 1 - u‖ ≤ Real.exp r - 1 - r) :
    ‖y * exp z - 1 - (u + z)‖ ≤ Real.exp (r + ‖z‖) - 1 - (r + ‖z‖) := by
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- y * exp z - 1 - (u + z) = (y - 1 - u) + (y - 1) * z + y * (exp z - 1 - z)
  have heq : y * exp z - 1 - (u + z) =
      (y - 1 - u) + (y - 1) * z + y * (exp z - 1 - z) := by noncomm_ring
  have hexp_sub_sub : ‖exp z - 1 - z‖ ≤ Real.exp ‖z‖ - 1 - ‖z‖ :=
    norm_exp_sub_one_sub_le (𝕂 := 𝕂) z
  have hexp_r_nn : 0 ≤ Real.exp r := (Real.exp_pos _).le
  have hexp_r_sub_one_nn : 0 ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
  have hexp_z_sub_sub_nn : 0 ≤ Real.exp ‖z‖ - 1 - ‖z‖ := by
    have := Real.add_one_le_exp ‖z‖
    nlinarith [norm_nonneg z, Real.exp_pos ‖z‖]
  rw [heq]
  calc ‖(y - 1 - u) + (y - 1) * z + y * (exp z - 1 - z)‖
      ≤ ‖(y - 1 - u) + (y - 1) * z‖ + ‖y * (exp z - 1 - z)‖ := norm_add_le _ _
    _ ≤ ‖y - 1 - u‖ + ‖(y - 1) * z‖ + ‖y * (exp z - 1 - z)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖y - 1 - u‖ + ‖y - 1‖ * ‖z‖ + ‖y‖ * ‖exp z - 1 - z‖ := by
        gcongr <;> exact norm_mul_le _ _
    _ ≤ (Real.exp r - 1 - r) + (Real.exp r - 1) * ‖z‖ +
          Real.exp r * (Real.exp ‖z‖ - 1 - ‖z‖) := by
        gcongr
    _ = Real.exp (r + ‖z‖) - 1 - (r + ‖z‖) := by
        rw [Real.exp_add]; ring

include 𝕂 in
/-- Bound for `‖suzuki5Product - 1 - (sum of 11 exponent args)‖`.

Proved inductively across the 11 factors via `norm_mul_exp_sub_linear_le`,
tracking the three invariants in parallel with those from the M2a bound. -/
theorem norm_suzuki5Product_sub_one_sub_linear_le (A B : 𝔸) (p τ : 𝕂) :
    let R := ‖(p / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ + ‖(p * τ) • B‖ +
              ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ +
              ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ +
              ‖(p * τ) • B‖ + ‖(p / 2 * τ) • A‖
    let u := (p / 2 * τ) • A + (p * τ) • B + (p * τ) • A + (p * τ) • B +
              ((1 - 3 * p) / 2 * τ) • A + ((1 - 4 * p) * τ) • B +
              ((1 - 3 * p) / 2 * τ) • A + (p * τ) • B + (p * τ) • A +
              (p * τ) • B + (p / 2 * τ) • A
    ‖suzuki5Product A B p τ - 1 - u‖ ≤ Real.exp R - 1 - R := by
  intro R u
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
  -- Base case (k = 1): y = exp z₁, u = z₁.
  -- Invariants: ‖y‖ ≤ exp‖z₁‖, ‖y-1‖ ≤ exp‖z₁‖-1, ‖y-1-z₁‖ ≤ exp‖z₁‖-1-‖z₁‖
  have hA₁ : ‖exp z₁‖ ≤ Real.exp ‖z₁‖ := norm_exp_le (𝕂 := 𝕂) _
  have hB₁ : ‖exp z₁ - 1‖ ≤ Real.exp ‖z₁‖ - 1 := norm_exp_sub_one_le (𝕂 := 𝕂) _
  have hC₁ : ‖exp z₁ - 1 - z₁‖ ≤ Real.exp ‖z₁‖ - 1 - ‖z₁‖ :=
    norm_exp_sub_one_sub_le (𝕂 := 𝕂) _
  -- Package the three invariants via the helper norm_mul_exp_sub_linear_le.
  -- Also propagate norm bounds via norm_mul_exp_le_of_norm_le and norm_mul_exp_sub_one_le.
  -- Step 2: extend to exp z₁ * exp z₂.
  have hA₂ : ‖exp z₁ * exp z₂‖ ≤ Real.exp (‖z₁‖ + ‖z₂‖) :=
    norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) _ _ hA₁
  have hB₂ : ‖exp z₁ * exp z₂ - 1‖ ≤ Real.exp (‖z₁‖ + ‖z₂‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (norm_nonneg _) hB₁
  have hC₂ : ‖exp z₁ * exp z₂ - 1 - (z₁ + z₂)‖ ≤
      Real.exp (‖z₁‖ + ‖z₂‖) - 1 - (‖z₁‖ + ‖z₂‖) :=
    norm_mul_exp_sub_linear_le (𝕂 := 𝕂) _ _ _ (norm_nonneg _) hA₁ hB₁ hC₁
  -- Step 3
  have hA₃ : ‖exp z₁ * exp z₂ * exp z₃‖ ≤ Real.exp ((‖z₁‖ + ‖z₂‖) + ‖z₃‖) :=
    norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) _ _ hA₂
  have hB₃ : ‖exp z₁ * exp z₂ * exp z₃ - 1‖ ≤ Real.exp ((‖z₁‖ + ‖z₂‖) + ‖z₃‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) hB₂
  have hC₃ : ‖exp z₁ * exp z₂ * exp z₃ - 1 - ((z₁ + z₂) + z₃)‖ ≤
      Real.exp ((‖z₁‖ + ‖z₂‖) + ‖z₃‖) - 1 - ((‖z₁‖ + ‖z₂‖) + ‖z₃‖) :=
    norm_mul_exp_sub_linear_le (𝕂 := 𝕂) _ _ _ (by positivity) hA₂ hB₂ hC₂
  -- Step 4
  have hA₄ : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄‖ ≤ Real.exp (((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) :=
    norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) _ _ hA₃
  have hB₄ : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ - 1‖ ≤
      Real.exp (((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) hB₃
  have hC₄ : ‖exp z₁ * exp z₂ * exp z₃ * exp z₄ - 1 - (((z₁ + z₂) + z₃) + z₄)‖ ≤
      Real.exp (((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) - 1 - (((‖z₁‖ + ‖z₂‖) + ‖z₃‖) + ‖z₄‖) :=
    norm_mul_exp_sub_linear_le (𝕂 := 𝕂) _ _ _ (by positivity) hA₃ hB₃ hC₃
  -- Step 5
  have hA₅ := norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) (_ : 𝔸) z₅ hA₄
  have hB₅ := norm_mul_exp_sub_one_le (𝕂 := 𝕂) (_ : 𝔸) z₅ (by positivity : (0:ℝ) ≤ _) hB₄
  have hC₅ := norm_mul_exp_sub_linear_le (𝕂 := 𝕂) (_ : 𝔸) _ z₅ (by positivity) hA₄ hB₄ hC₄
  -- Step 6
  have hA₆ := norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) (_ : 𝔸) z₆ hA₅
  have hB₆ := norm_mul_exp_sub_one_le (𝕂 := 𝕂) (_ : 𝔸) z₆ (by positivity) hB₅
  have hC₆ := norm_mul_exp_sub_linear_le (𝕂 := 𝕂) (_ : 𝔸) _ z₆ (by positivity) hA₅ hB₅ hC₅
  -- Step 7
  have hA₇ := norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) (_ : 𝔸) z₇ hA₆
  have hB₇ := norm_mul_exp_sub_one_le (𝕂 := 𝕂) (_ : 𝔸) z₇ (by positivity) hB₆
  have hC₇ := norm_mul_exp_sub_linear_le (𝕂 := 𝕂) (_ : 𝔸) _ z₇ (by positivity) hA₆ hB₆ hC₆
  -- Step 8
  have hA₈ := norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) (_ : 𝔸) z₈ hA₇
  have hB₈ := norm_mul_exp_sub_one_le (𝕂 := 𝕂) (_ : 𝔸) z₈ (by positivity) hB₇
  have hC₈ := norm_mul_exp_sub_linear_le (𝕂 := 𝕂) (_ : 𝔸) _ z₈ (by positivity) hA₇ hB₇ hC₇
  -- Step 9
  have hA₉ := norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) (_ : 𝔸) z₉ hA₈
  have hB₉ := norm_mul_exp_sub_one_le (𝕂 := 𝕂) (_ : 𝔸) z₉ (by positivity) hB₈
  have hC₉ := norm_mul_exp_sub_linear_le (𝕂 := 𝕂) (_ : 𝔸) _ z₉ (by positivity) hA₈ hB₈ hC₈
  -- Step 10
  have hA₁₀ := norm_mul_exp_le_of_norm_le (𝕂 := 𝕂) (_ : 𝔸) z₁₀ hA₉
  have hB₁₀ := norm_mul_exp_sub_one_le (𝕂 := 𝕂) (_ : 𝔸) z₁₀ (by positivity) hB₉
  have hC₁₀ := norm_mul_exp_sub_linear_le (𝕂 := 𝕂) (_ : 𝔸) _ z₁₀ (by positivity) hA₉ hB₉ hC₉
  -- Step 11
  have hC₁₁ := norm_mul_exp_sub_linear_le (𝕂 := 𝕂) (_ : 𝔸) _ z₁₁ (by positivity) hA₁₀ hB₁₀ hC₁₀
  convert hC₁₁ using 2 <;> ring

include 𝕂 in
/-- Coefficient sum identity: the 11 exponent arguments of `suzuki5Product`
sum to `τ • (A + B)`. The A-coefficients sum to 1 (`p/2+p+(1-3p)/2+(1-3p)/2+p+p/2 = 1`)
and the B-coefficients sum to 1 (`p+p+(1-4p)+p+p = 1`). -/
lemma suzuki5_linear_sum (A B : 𝔸) (p τ : 𝕂) :
    (p / 2 * τ) • A + (p * τ) • B + (p * τ) • A + (p * τ) • B +
    ((1 - 3 * p) / 2 * τ) • A + ((1 - 4 * p) * τ) • B +
    ((1 - 3 * p) / 2 * τ) • A + (p * τ) • B + (p * τ) • A +
    (p * τ) • B + (p / 2 * τ) • A = τ • (A + B) := by
  -- Collect A-terms and B-terms separately using ← add_smul, then combine.
  have hA_terms : (p / 2 * τ) • A + (p * τ) • A + ((1 - 3 * p) / 2 * τ) • A +
                  ((1 - 3 * p) / 2 * τ) • A + (p * τ) • A + (p / 2 * τ) • A = τ • A := by
    simp only [← add_smul]
    congr 1; ring
  have hB_terms : (p * τ) • B + (p * τ) • B + ((1 - 4 * p) * τ) • B + (p * τ) • B +
                  (p * τ) • B = τ • B := by
    simp only [← add_smul]
    congr 1; ring
  -- Rearrange and combine
  have hsplit : (p / 2 * τ) • A + (p * τ) • B + (p * τ) • A + (p * τ) • B +
                ((1 - 3 * p) / 2 * τ) • A + ((1 - 4 * p) * τ) • B +
                ((1 - 3 * p) / 2 * τ) • A + (p * τ) • B + (p * τ) • A +
                (p * τ) • B + (p / 2 * τ) • A =
      ((p / 2 * τ) • A + (p * τ) • A + ((1 - 3 * p) / 2 * τ) • A +
       ((1 - 3 * p) / 2 * τ) • A + (p * τ) • A + (p / 2 * τ) • A) +
      ((p * τ) • B + (p * τ) • B + ((1 - 4 * p) * τ) • B + (p * τ) • B + (p * τ) • B) := by
    abel
  rw [hsplit, hA_terms, hB_terms, ← smul_add]

include 𝕂 in
/-- **M3b** — leading-order bound: `‖suzuki5_bch A B p τ - τ•(A+B)‖` is `O(τ²)`.
Explicitly bounded by `(exp R - 1 - R) + (exp R - 1)²/(2 - exp R)` where
`R = suzuki5ArgNormBound A B p τ < log 2`. Both pieces are `O(R²) = O(τ²·s²)`
as `R → 0`. -/
theorem norm_suzuki5_bch_sub_smul_le (A B : 𝔸) (p τ : 𝕂)
    (h : suzuki5ArgNormBound A B p τ < Real.log 2) :
    ‖suzuki5_bch 𝕂 A B p τ - τ • (A + B)‖ ≤
      (Real.exp (suzuki5ArgNormBound A B p τ) - 1 -
         suzuki5ArgNormBound A B p τ) +
      (Real.exp (suzuki5ArgNormBound A B p τ) - 1) ^ 2 /
        (2 - Real.exp (suzuki5ArgNormBound A B p τ)) := by
  -- Split via triangle inequality:
  --   ‖logOnePlus(S-1) - τ•(A+B)‖
  --     ≤ ‖logOnePlus(S-1) - (S-1)‖ + ‖(S-1) - τ•(A+B)‖
  -- First piece bounded by norm_logOnePlus_sub_le.
  -- Second piece bounded by norm_suzuki5Product_sub_one_sub_linear_le + linear_sum identity.
  set R := suzuki5ArgNormBound A B p τ with hR_def
  -- The argument-norm sum is bounded by R (from M2a sum_arg_norms_le_bound)
  have hsum := sum_arg_norms_le_bound (𝕂 := 𝕂) A B p τ
  -- Unfold suzuki5_bch
  unfold suzuki5_bch
  set y := suzuki5Product A B p τ - 1 with hy_def
  -- ‖y‖ bound
  have hy_norm_lt_one : ‖y‖ < 1 := norm_suzuki5Product_sub_one_lt_one (𝕂 := 𝕂) A B p τ h
  have hy_norm_le : ‖y‖ ≤ Real.exp R - 1 := by
    have h1 := norm_suzuki5Product_sub_one_le (𝕂 := 𝕂) A B p τ
    -- ‖S - 1‖ ≤ exp(∑‖zᵢ‖) - 1 ≤ exp R - 1
    have := Real.exp_le_exp.mpr hsum
    have : Real.exp (‖(p / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ + ‖(p * τ) • B‖ +
                      ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ +
                      ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ +
                      ‖(p * τ) • B‖ + ‖(p / 2 * τ) • A‖) ≤ Real.exp R := this
    linarith [h1]
  -- First piece: ‖logOnePlus(y) - y‖ ≤ ‖y‖²/(1 - ‖y‖)
  have hlog_sub : ‖logOnePlus (𝕂 := 𝕂) y - y‖ ≤ ‖y‖ ^ 2 / (1 - ‖y‖) :=
    norm_logOnePlus_sub_le (𝕂 := 𝕂) y hy_norm_lt_one
  -- Second piece: ‖y - τ•(A+B)‖ = ‖S(τ) - 1 - ∑zᵢ‖ ≤ exp R - 1 - R
  have hlin := norm_suzuki5Product_sub_one_sub_linear_le (𝕂 := 𝕂) A B p τ
  simp only at hlin
  -- Use the linear_sum identity to replace the sum with τ•(A+B).
  -- But hlin uses the explicit sum of zᵢ, which via suzuki5_linear_sum = τ•(A+B).
  have hy_linear : y - τ • (A + B) = suzuki5Product A B p τ - 1 -
      ((p / 2 * τ) • A + (p * τ) • B + (p * τ) • A + (p * τ) • B +
       ((1 - 3 * p) / 2 * τ) • A + ((1 - 4 * p) * τ) • B +
       ((1 - 3 * p) / 2 * τ) • A + (p * τ) • B + (p * τ) • A +
       (p * τ) • B + (p / 2 * τ) • A) := by
    rw [← suzuki5_linear_sum (𝕂 := 𝕂) A B p τ, hy_def]
  -- Bound on the "sum of argument norms" ≤ R
  have hsum_bound := sum_arg_norms_le_bound (𝕂 := 𝕂) A B p τ
  have hlin' : ‖y - τ • (A + B)‖ ≤ Real.exp R - 1 - R := by
    rw [hy_linear]
    refine le_trans hlin ?_
    -- exp(sum_args) - 1 - sum_args ≤ exp R - 1 - R since f(x) = exp(x) - 1 - x is monotone for x ≥ 0
    have hmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → Real.exp a - 1 - a ≤ Real.exp b - 1 - b := by
      intro a b ha hab
      have hexp_a_ge_one : 1 ≤ Real.exp a := Real.one_le_exp ha
      have hba_nn : 0 ≤ b - a := by linarith
      have hexp_ba_ge : 1 + (b - a) ≤ Real.exp (b - a) := by
        have := Real.add_one_le_exp (b - a); linarith
      have hexp_ab : Real.exp b = Real.exp a * Real.exp (b - a) := by
        rw [← Real.exp_add]; congr 1; ring
      -- exp b ≥ exp a * (1 + (b - a)) = exp a + exp a * (b - a) ≥ exp a + (b - a)
      have h1 : Real.exp a + Real.exp a * (b - a) ≤ Real.exp b := by
        rw [hexp_ab]
        have : Real.exp a * (1 + (b - a)) ≤ Real.exp a * Real.exp (b - a) :=
          mul_le_mul_of_nonneg_left hexp_ba_ge (Real.exp_pos a).le
        linarith
      have h2 : (b - a) ≤ Real.exp a * (b - a) := by
        have := mul_le_mul_of_nonneg_right hexp_a_ge_one hba_nn
        linarith
      linarith
    have hsum_nn : 0 ≤
      ‖(p / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ + ‖(p * τ) • B‖ +
      ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ +
      ‖((1 - 3 * p) / 2 * τ) • A‖ + ‖(p * τ) • B‖ + ‖(p * τ) • A‖ +
      ‖(p * τ) • B‖ + ‖(p / 2 * τ) • A‖ := by positivity
    exact hmono hsum_nn hsum_bound
  -- Combine via triangle inequality
  have hy_sq_bound : ‖y‖ ^ 2 ≤ (Real.exp R - 1) ^ 2 := by
    apply sq_le_sq'
    · linarith [norm_nonneg y, sq_nonneg ‖y‖]
    · exact hy_norm_le
  have hden : 2 - Real.exp R ≤ 1 - ‖y‖ := by
    -- ‖y‖ ≤ exp R - 1, so 1 - ‖y‖ ≥ 1 - (exp R - 1) = 2 - exp R
    linarith [hy_norm_le]
  have hden_pos : 0 < 2 - Real.exp R := by
    have : Real.exp R < 2 := by
      calc Real.exp R < Real.exp (Real.log 2) := Real.exp_strictMono h
        _ = 2 := Real.exp_log (by norm_num)
    linarith
  have hden_left_pos : 0 < 1 - ‖y‖ := by linarith
  calc ‖logOnePlus (𝕂 := 𝕂) y - τ • (A + B)‖
      = ‖(logOnePlus (𝕂 := 𝕂) y - y) + (y - τ • (A + B))‖ := by congr 1; abel
    _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y‖ + ‖y - τ • (A + B)‖ := norm_add_le _ _
    _ ≤ ‖y‖ ^ 2 / (1 - ‖y‖) + (Real.exp R - 1 - R) := by gcongr
    _ ≤ (Real.exp R - 1) ^ 2 / (2 - Real.exp R) + (Real.exp R - 1 - R) := by
        have : ‖y‖ ^ 2 / (1 - ‖y‖) ≤ (Real.exp R - 1) ^ 2 / (2 - Real.exp R) :=
          div_le_div₀ (sq_nonneg _) hy_sq_bound hden_pos hden
        linarith
    _ = (Real.exp R - 1 - R) + (Real.exp R - 1) ^ 2 / (2 - Real.exp R) := by ring

/-! ### Strang block decomposition (M4a setup)

The Suzuki 5-block product decomposes as a 5-fold composition of Strang blocks
with coefficients `(p, p, 1-4p, p, p)`. Adjacent A-half exponentials merge by
`[A, A] = 0`. This decomposition is the algebraic backbone of M4a: each Strang
block has a known cubic correction `c³·E_sym(A,B)`, and the 5-fold composition
sums these (cross-block commutators contribute only at order τ⁴).
-/

/-- A single Strang block: `exp((c·τ/2)•A) · exp((c·τ)•B) · exp((c·τ/2)•A)`. -/
noncomputable def strangBlock (A B : 𝔸) (c τ : 𝕂) : 𝔸 :=
  exp ((c * τ / 2) • A) * exp ((c * τ) • B) * exp ((c * τ / 2) • A)

include 𝕂 in
/-- Merging of A-exponentials: `exp(α•A) · exp(β•A) = exp((α+β)•A)`
    since `[A, A] = 0`. -/
lemma exp_smul_mul_exp_smul_self (A : 𝔸) (α β : 𝕂) :
    exp (α • A) * exp (β • A) = exp ((α + β) • A) := by
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have h_comm : Commute (α • A) (β • A) :=
    ((Commute.refl A).smul_left α).smul_right β
  rw [← exp_add_of_commute h_comm, ← add_smul]

include 𝕂 in
/-- The Suzuki 5-block product factors as `S_p · S_p · S_{1-4p} · S_p · S_p`,
    where `S_c(τ) = exp((c·τ/2)•A)·exp((c·τ)•B)·exp((c·τ/2)•A)` is the Strang
    block with coefficient `c`. The decomposition uses 4 A-merges:
    `e(p·τ/2)·e(p·τ/2) → e(p·τ)` (twice, at the joins of the two pairs of S_p) and
    `e(p·τ/2)·e((1-4p)·τ/2) → e((1-3p)/2·τ)` (twice, at the joins involving S_{1-4p}). -/
theorem suzuki5Product_eq_strangBlock_prod (A B : 𝔸) (p τ : 𝕂) :
    suzuki5Product A B p τ =
      strangBlock A B p τ * strangBlock A B p τ *
      strangBlock A B (1 - 4 * p) τ *
      strangBlock A B p τ * strangBlock A B p τ := by
  -- Strategy: rewrite both sides to a common 11-factor form with adjacent
  -- A-half exponentials merged into single A-exponentials.
  -- Set abbreviations for the merged A-exponentials.
  -- `hP_full = exp(p·τ·A)` arises from merging two `hP_half`s.
  -- `hPQ = exp((1-3p)/2·τ·A)` arises from merging hP_half + hQ_half.
  unfold suzuki5Product strangBlock
  -- The two equivalent forms of the half coefficient.
  have hp_halves : (p * τ / 2 + p * τ / 2 : 𝕂) = p * τ := by ring
  have hpq_halves_left : (p * τ / 2 + (1 - 4 * p) * τ / 2 : 𝕂) = (1 - 3 * p) / 2 * τ := by ring
  have hpq_halves_right : ((1 - 4 * p) * τ / 2 + p * τ / 2 : 𝕂) = (1 - 3 * p) / 2 * τ := by ring
  -- Rewrite RHS adjacent A halves into single A-exps.
  rw [show
      exp ((p * τ / 2) • A) * exp ((p * τ) • B) * exp ((p * τ / 2) • A) *
      (exp ((p * τ / 2) • A) * exp ((p * τ) • B) * exp ((p * τ / 2) • A)) *
      (exp (((1 - 4 * p) * τ / 2) • A) * exp (((1 - 4 * p) * τ) • B) *
        exp (((1 - 4 * p) * τ / 2) • A)) *
      (exp ((p * τ / 2) • A) * exp ((p * τ) • B) * exp ((p * τ / 2) • A)) *
      (exp ((p * τ / 2) • A) * exp ((p * τ) • B) * exp ((p * τ / 2) • A)) =
      exp ((p * τ / 2) • A) * exp ((p * τ) • B) *
      (exp ((p * τ / 2) • A) * exp ((p * τ / 2) • A)) * exp ((p * τ) • B) *
      (exp ((p * τ / 2) • A) * exp (((1 - 4 * p) * τ / 2) • A)) *
      exp (((1 - 4 * p) * τ) • B) *
      (exp (((1 - 4 * p) * τ / 2) • A) * exp ((p * τ / 2) • A)) *
      exp ((p * τ) • B) *
      (exp ((p * τ / 2) • A) * exp ((p * τ / 2) • A)) * exp ((p * τ) • B) *
      exp ((p * τ / 2) • A) from by noncomm_ring]
  -- Apply merging 4 times then collapse the scalar additions via composition
  -- of `exp_smul_mul_exp_smul_self` with the scalar identity.
  have merge_pp : ∀ X : 𝔸,
      exp ((p * τ / 2) • X) * exp ((p * τ / 2) • X) = exp ((p * τ) • X) := by
    intro X
    rw [exp_smul_mul_exp_smul_self (𝕂 := 𝕂) X (p * τ / 2) (p * τ / 2)]
    congr 1
    rw [show (p * τ / 2 + p * τ / 2 : 𝕂) = p * τ from by ring]
  have merge_pq : ∀ X : 𝔸,
      exp ((p * τ / 2) • X) * exp (((1 - 4 * p) * τ / 2) • X) =
        exp (((1 - 3 * p) / 2 * τ) • X) := by
    intro X
    rw [exp_smul_mul_exp_smul_self (𝕂 := 𝕂) X (p * τ / 2) ((1 - 4 * p) * τ / 2)]
    congr 1
    rw [show (p * τ / 2 + (1 - 4 * p) * τ / 2 : 𝕂) = (1 - 3 * p) / 2 * τ from by ring]
  have merge_qp : ∀ X : 𝔸,
      exp (((1 - 4 * p) * τ / 2) • X) * exp ((p * τ / 2) • X) =
        exp (((1 - 3 * p) / 2 * τ) • X) := by
    intro X
    rw [exp_smul_mul_exp_smul_self (𝕂 := 𝕂) X ((1 - 4 * p) * τ / 2) (p * τ / 2)]
    congr 1
    rw [show ((1 - 4 * p) * τ / 2 + p * τ / 2 : 𝕂) = (1 - 3 * p) / 2 * τ from by ring]
  simp only [merge_pp, merge_pq, merge_qp]
  -- Now both sides match modulo the LHS p/2·τ vs RHS p·τ/2 form.
  have hP_alt : exp ((p / 2 * τ) • A) = exp ((p * τ / 2) • A) := by
    rw [div_mul_eq_mul_div]
  rw [hP_alt]

/-! ### Cubic coefficient and the symmetric BCH cubic structure

The τ³ coefficient of `suzuki5_bch` is `C₃(p) := 4p³ + (1-4p)³`. This is the
sum of cubes of the 5 Strang block coefficients `(p, p, 1-4p, p, p)`.
Cross-block commutators only contribute at τ⁴ and higher, so the τ³ coefficient
is simply the sum of per-block contributions.

The cubic "shape" `E_sym(A,B) := -(1/24)·[A,[A,B]] + (1/12)·[B,[B,A]]` is the
symmetric Strang splitting cubic, encoded as `symmetric_bch_cubic_poly` in
`BCH/Basic.lean`.
-/

/-- The τ³ scalar coefficient of `suzuki5_bch`: `C₃(p) := 4p³ + (1-4p)³`.
This is the sum of cubes of the 5 Strang coefficients `(p, p, 1-4p, p, p)`.
Vanishes precisely under the Suzuki cubic-cancellation condition. -/
def suzuki5_bch_cubic_coeff (𝕂 : Type*) [Field 𝕂] (p : 𝕂) : 𝕂 :=
  4 * p ^ 3 + (1 - 4 * p) ^ 3

/-- The Suzuki cubic-cancellation condition: `4p³ + (1-4p)³ = 0`. The standard
choice is `p = 1/(4 - 4^(1/3))`, the real root of the cubic. Under this
condition, the τ³ correction in `suzuki5_bch` vanishes, leaving the leading
error at τ⁵ — the Suzuki S₄ fourth-order property. -/
def IsSuzukiCubic {𝕂 : Type*} [Field 𝕂] (p : 𝕂) : Prop :=
  suzuki5_bch_cubic_coeff 𝕂 p = 0

/-- Restating: `IsSuzukiCubic p ↔ 4p³ + (1-4p)³ = 0`, by definitional unfolding. -/
lemma IsSuzukiCubic_iff {𝕂 : Type*} [Field 𝕂] (p : 𝕂) :
    IsSuzukiCubic p ↔ 4 * p ^ 3 + (1 - 4 * p) ^ 3 = 0 := Iff.rfl

/-- **M4b precursor**: under `IsSuzukiCubic p`, the τ³ coefficient vanishes.
This is a definitional one-liner. The full M4b — that `suzuki5_bch` itself
has no τ³ term under `IsSuzukiCubic` — follows once M4a is established. -/
lemma suzuki5_bch_cubic_coeff_eq_zero_of_IsSuzukiCubic
    {𝕂 : Type*} [Field 𝕂] {p : 𝕂} (h : IsSuzukiCubic p) :
    suzuki5_bch_cubic_coeff 𝕂 p = 0 := h

/-! ### Per-block cubic structure (foundational lemmas for M4a)

Each Strang block `S_c(τ)` has logarithm
  `log(S_c(τ)) = bch(bch((cτ/2)•A, (cτ)•B), (cτ/2)•A) = (cτ)•V + (cτ)³•E_sym + O(s⁵)`
where V = A+B and E_sym = symmetric_bch_cubic_poly. The constants are tracked
through the existing `norm_symmetric_bch_cubic_sub_poly_le` from BCH/Basic.lean.
-/

/-- The "ideal" log of a Strang block: the polynomial `cτ•(A+B) + (cτ)³•E_sym(A,B)`
that approximates the actual log up to O(s⁵). Used as the comparison target for the
per-block cubic analysis. -/
noncomputable def strangBlock_log_target (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (A B : 𝔸) (c τ : 𝕂) : 𝔸 :=
  (c * τ) • (A + B) + (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B

/-- The actual log of a Strang block: `bch(bch((cτ/2)•A, (cτ)•B), (cτ/2)•A)`.

By `exp_symmetric_bch`, this satisfies `exp(strangBlock_log) = strangBlock`,
provided `‖cτ•A‖ + ‖cτ•B‖ < 1/4`. -/
noncomputable def strangBlock_log (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (c τ : 𝕂) : 𝔸 :=
  bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • ((c * τ) • A)) ((c * τ) • B))
    ((2 : 𝕂)⁻¹ • ((c * τ) • A))

include 𝕂 in
/-- Round-trip: `exp(strangBlock_log A B c τ) = strangBlock A B c τ` whenever
`‖(cτ)•A‖ + ‖(cτ)•B‖ < 1/4`. The output is the Strang block in the form
`exp((cτ/2)•A) · exp((cτ)•B) · exp((cτ/2)•A)`. -/
theorem exp_strangBlock_log (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4) :
    exp (strangBlock_log 𝕂 A B c τ) = strangBlock A B c τ := by
  unfold strangBlock_log strangBlock
  -- Apply exp_symmetric_bch with a = cτ•A, b = cτ•B; matches via smul re-association.
  have key := exp_symmetric_bch (𝕂 := 𝕂) ((c * τ) • A) ((c * τ) • B) h
  -- key gives: exp(bch(bch(½(cτ•A), cτ•B), ½(cτ•A))) =
  --           exp(½•(cτ•A)) · exp(cτ•B) · exp(½•(cτ•A))
  -- We need the RHS to match `exp((cτ/2)•A) * exp((cτ)•B) * exp((cτ/2)•A)`.
  -- Since (1/2)•(c*τ)•A = (c*τ/2)•A by smul associativity:
  rw [key]
  congr 2
  · rw [smul_smul]; congr 1; ring
  · rw [smul_smul]; congr 1; ring

include 𝕂 in
/-- **Per-block cubic bound (M4a per-block)**: each Strang block's log differs
from the target `cτ•(A+B) + (cτ)³•E_sym(A,B)` by at most `K·s⁵` where
`s = ‖cτ•A‖ + ‖cτ•B‖`. Direct application of `norm_symmetric_bch_cubic_sub_poly_le`
to the Strang composition.

Note: the `(c*τ)•(A+B)` regrouping uses smul-distributivity. -/
theorem norm_strangBlock_log_sub_target_le (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4) :
    ‖strangBlock_log 𝕂 A B c τ - strangBlock_log_target 𝕂 A B c τ‖ ≤
      10000000 * (‖(c * τ) • A‖ + ‖(c * τ) • B‖) ^ 5 := by
  unfold strangBlock_log strangBlock_log_target
  -- Apply `norm_symmetric_bch_cubic_sub_poly_le` with a = cτ•A, b = cτ•B.
  -- The conclusion: ‖sym_bch_cubic - sym_E₃‖ ≤ 10⁷·s⁵ where sym_bch_cubic =
  -- bch(bch(½a,b),½a) - (a+b).
  have key := norm_symmetric_bch_cubic_sub_poly_le (𝕂 := 𝕂) ((c * τ) • A) ((c * τ) • B) h
  -- key : ‖bch(bch(½cτA, cτB), ½cτA) - (cτA+cτB) - sym_E₃(cτA, cτB)‖ ≤ 10⁷·s⁵
  -- Rewrite (cτA+cτB) = cτ•(A+B) and sym_E₃(cτA, cτB) = (cτ)³•sym_E₃(A,B).
  unfold symmetric_bch_cubic at key
  -- key now uses bch(...) - (cτA+cτB) - symmetric_bch_cubic_poly(cτA, cτB)
  have hsmul_dist : (c * τ) • A + (c * τ) • B = (c * τ) • (A + B) := by
    rw [smul_add]
  have hsym_hom : symmetric_bch_cubic_poly 𝕂 ((c * τ) • A) ((c * τ) • B) =
      (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B :=
    symmetric_bch_cubic_poly_smul A B (c * τ)
  -- Massage key to match the goal's expression.
  rw [hsmul_dist, hsym_hom] at key
  -- Now key matches goal modulo grouping of subtraction.
  convert key using 2
  abel

/-! ### Sum of 5-block targets

The sum of the 5 Strang-block targets with coefficients `(p, p, 1-4p, p, p)` equals
the expected form `τ•(A+B) + τ³·C₃(p)·E_sym(A,B)`. This is the algebraic identity
that will combine with per-block bounds to yield the M4a main theorem.
-/

include 𝕂 in
/-- The sum of per-block targets equals the M4a main target.

The linear sum: `Σc_i = p+p+(1-4p)+p+p = 1`, giving `τ•(A+B)` overall.
The cubic sum: `Σc_i³ = 4p³+(1-4p)³ = C₃(p)`, giving `τ³·C₃(p)·E_sym` overall. -/
theorem suzuki5_targets_sum (A B : 𝔸) (p τ : 𝕂) :
    strangBlock_log_target 𝕂 A B p τ +
    strangBlock_log_target 𝕂 A B p τ +
    strangBlock_log_target 𝕂 A B (1 - 4 * p) τ +
    strangBlock_log_target 𝕂 A B p τ +
    strangBlock_log_target 𝕂 A B p τ =
    τ • (A + B) +
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B := by
  unfold strangBlock_log_target suzuki5_bch_cubic_coeff
  -- Collect linear and cubic contributions separately.
  set V := A + B with hV_def
  set E := symmetric_bch_cubic_poly 𝕂 A B with hE_def
  -- Coefficients (Σc_i)·τ = τ for the linear part
  have h_lin_sum : (p * τ) + (p * τ) + ((1 - 4 * p) * τ) + (p * τ) + (p * τ) = τ := by ring
  -- Coefficients Σc_i³·τ³ for the cubic part
  have h_cub_sum : (p * τ) ^ 3 + (p * τ) ^ 3 + ((1 - 4 * p) * τ) ^ 3 + (p * τ) ^ 3 +
      (p * τ) ^ 3 = τ ^ 3 * (4 * p ^ 3 + (1 - 4 * p) ^ 3) := by ring
  -- Group the LHS into linear + cubic
  have hsplit :
      ((p * τ) • V + (p * τ) ^ 3 • E) +
      ((p * τ) • V + (p * τ) ^ 3 • E) +
      (((1 - 4 * p) * τ) • V + ((1 - 4 * p) * τ) ^ 3 • E) +
      ((p * τ) • V + (p * τ) ^ 3 • E) +
      ((p * τ) • V + (p * τ) ^ 3 • E) =
      ((p * τ) • V + (p * τ) • V + ((1 - 4 * p) * τ) • V + (p * τ) • V + (p * τ) • V) +
      ((p * τ) ^ 3 • E + (p * τ) ^ 3 • E + ((1 - 4 * p) * τ) ^ 3 • E + (p * τ) ^ 3 • E +
        (p * τ) ^ 3 • E) := by
    abel
  rw [hsplit]
  -- Combine V-part: sum of smul's = (Σc_iτ)•V = τ•V
  rw [show (p * τ) • V + (p * τ) • V + ((1 - 4 * p) * τ) • V + (p * τ) • V +
          (p * τ) • V =
          ((p * τ) + (p * τ) + ((1 - 4 * p) * τ) + (p * τ) + (p * τ)) • V from by
        simp only [add_smul],
      h_lin_sum]
  -- Combine E-part similarly
  rw [show (p * τ) ^ 3 • E + (p * τ) ^ 3 • E + ((1 - 4 * p) * τ) ^ 3 • E + (p * τ) ^ 3 • E +
          (p * τ) ^ 3 • E =
          ((p * τ) ^ 3 + (p * τ) ^ 3 + ((1 - 4 * p) * τ) ^ 3 + (p * τ) ^ 3 +
            (p * τ) ^ 3) • E from by simp only [add_smul],
      h_cub_sum]

/-! ### Per-block bounds under the M4a regime

Translating the local regime `‖(c*τ)•A‖ + ‖(c*τ)•B‖ < 1/4` to global R-based
bounds. We need the regime to hold for both `c = p` and `c = 1-4p`. -/

include 𝕂 in
/-- Norm bound for Strang block args: `‖(c*τ)•A‖ + ‖(c*τ)•B‖ ≤ ‖c‖·‖τ‖·(‖A‖+‖B‖)`. -/
lemma strangBlock_arg_norm_le (A B : 𝔸) (c τ : 𝕂) :
    ‖(c * τ) • A‖ + ‖(c * τ) • B‖ ≤ ‖c‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
  have hcτ : ‖(c * τ : 𝕂)‖ = ‖c‖ * ‖τ‖ := norm_mul _ _
  calc ‖(c * τ) • A‖ + ‖(c * τ) • B‖
      ≤ ‖c * τ‖ * ‖A‖ + ‖c * τ‖ * ‖B‖ := by gcongr <;> exact norm_smul_le _ _
    _ = ‖c * τ‖ * (‖A‖ + ‖B‖) := by ring
    _ = ‖c‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by rw [hcτ]

/-! ### Cubic-order norm bound for `strangBlock_log - cτ•V`

This is the "linear remainder" of strangBlock_log: after subtracting the leading
linear term `cτ•V`, what's left is bounded cubically in `η := ‖cτ‖·(‖A‖+‖B‖)`.
The natural norm to use here is `η` rather than `σ = ‖cτ•A‖+‖cτ•B‖`, because
the cubic polynomial `E_sym(A,B)` has norm `≤ (‖A‖+‖B‖)³`, not `≤ σ³`. We have
`σ ≤ η`, so per-block cubic bounds in `σ` also lift to bounds in `η`.
-/

include 𝕂 in
/-- **Linear remainder for a Strang block** (cubic-order bound in `η = ‖cτ‖·(‖A‖+‖B‖)`):
  `‖strangBlock_log A B c τ - (c*τ)•(A+B)‖ ≤ η³ + 10⁷·η⁵`.

The bound follows from the per-block cubic bound
`norm_strangBlock_log_sub_target_le` (which is σ⁵, but σ ≤ η so also ≤ η⁵) and
the cubic-polynomial norm bound `norm_symmetric_bch_cubic_poly_le`. -/
theorem norm_strangBlock_log_sub_linear_le (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4) :
    ‖strangBlock_log 𝕂 A B c τ - (c * τ) • (A + B)‖ ≤
      (‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 +
        10000000 * (‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 := by
  set σ := ‖(c * τ) • A‖ + ‖(c * τ) • B‖ with hσ_def
  set η := ‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖) with hη_def
  -- σ ≤ η (via norm_smul_le on each summand)
  have hσ_le_η : σ ≤ η := by
    rw [hσ_def, hη_def]
    calc ‖(c * τ) • A‖ + ‖(c * τ) • B‖
        ≤ ‖(c * τ : 𝕂)‖ * ‖A‖ + ‖(c * τ : 𝕂)‖ * ‖B‖ := by
          gcongr <;> exact norm_smul_le _ _
      _ = ‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖) := by ring
  have hσ_nn : 0 ≤ σ := by rw [hσ_def]; positivity
  -- Per-block cubic bound: ‖sb_log - target‖ ≤ 10⁷·σ⁵ ≤ 10⁷·η⁵
  have hcubic_bound := norm_strangBlock_log_sub_target_le (𝕂 := 𝕂) A B c τ h
  unfold strangBlock_log_target at hcubic_bound
  have hcubic_bound' :
      ‖strangBlock_log 𝕂 A B c τ -
        ((c * τ) • (A + B) + (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)‖ ≤
      10000000 * η ^ 5 := by
    refine le_trans hcubic_bound ?_
    have : σ ^ 5 ≤ η ^ 5 := by
      gcongr
    linarith
  -- Bound ‖(cτ)³·E_sym‖ ≤ η³
  have hE_bound : ‖(c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B‖ ≤ η ^ 3 := by
    calc ‖(c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B‖
        ≤ ‖((c * τ : 𝕂)) ^ 3‖ * ‖symmetric_bch_cubic_poly 𝕂 A B‖ := norm_smul_le _ _
      _ ≤ ‖(c * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 := by
          gcongr
          · rw [norm_pow]
          · exact norm_symmetric_bch_cubic_poly_le (𝕂 := 𝕂) _ _
      _ = η ^ 3 := by rw [hη_def]; ring
  -- Triangle inequality
  have heq : strangBlock_log 𝕂 A B c τ - (c * τ) • (A + B) =
      (strangBlock_log 𝕂 A B c τ -
        ((c * τ) • (A + B) + (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)) +
      (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B := by abel
  calc ‖strangBlock_log 𝕂 A B c τ - (c * τ) • (A + B)‖
      = ‖(strangBlock_log 𝕂 A B c τ -
          ((c * τ) • (A + B) + (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)) +
        (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B‖ := by rw [heq]
    _ ≤ ‖strangBlock_log 𝕂 A B c τ -
          ((c * τ) • (A + B) + (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)‖ +
        ‖(c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B‖ := norm_add_le _ _
    _ ≤ 10000000 * η ^ 5 + η ^ 3 := by linarith
    _ = η ^ 3 + 10000000 * η ^ 5 := by ring

/-! ### Logarithm of a squared Strang block

Since any element commutes with itself, `S_c(τ) · S_c(τ) = exp(2·strangBlock_log)`.
This gives `log(S_c · S_c) = 2 · strangBlock_log`, bypassing iterated BCH.
-/

include 𝕂 in
/-- Squared Strang block: `S_c · S_c = exp(2 · strangBlock_log)`. Follows from
`S_c = exp(strangBlock_log)` (via `exp_strangBlock_log`) plus commutativity with itself. -/
theorem strangBlock_mul_self (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4) :
    strangBlock A B c τ * strangBlock A B c τ =
      exp ((2 : 𝕂) • strangBlock_log 𝕂 A B c τ) := by
  rw [← exp_strangBlock_log (𝕂 := 𝕂) A B c τ h]
  set X := strangBlock_log 𝕂 A B c τ
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.refl X), ← two_smul 𝕂]

/-! ### Symmetric-BCH decomposition of suzuki5_bch

Combining the 5-Strang factorization with A-merging gives
  `S(τ) = S_p² · S_{1-4p} · S_p² = A·C·A`
where `A = exp(2·logS_p)` and `C = exp(logS_{1-4p})`. By `exp_symmetric_bch`
on `(4·logS_p, logS_{1-4p})`, we obtain
  `exp(bch(bch(2·logS_p, logS_{1-4p}), 2·logS_p)) = S(τ)`.
Log injectivity then gives
  `suzuki5_bch = bch(bch(2·logS_p, logS_{1-4p}), 2·logS_p)`.

This reduces the iterated-BCH problem to a SINGLE symmetric-BCH application,
enabling direct use of `norm_symmetric_bch_cubic_sub_poly_le` for the M4a bound.
-/

include 𝕂 in
/-- The Suzuki 5-block product reassembles as `A·C·A` with `A = S_p²` and `C = S_{1-4p}`. -/
theorem suzuki5Product_eq_ACA (A B : 𝔸) (p τ : 𝕂) :
    suzuki5Product A B p τ =
      (strangBlock A B p τ * strangBlock A B p τ) *
      strangBlock A B (1 - 4 * p) τ *
      (strangBlock A B p τ * strangBlock A B p τ) := by
  rw [suzuki5Product_eq_strangBlock_prod]
  noncomm_ring

include 𝕂 in
/-- `exp(bch(bch(2•logS_p, logS_{1-4p}), 2•logS_p)) = suzuki5Product A B p τ`
under the regime `‖4•logS_p‖ + ‖logS_{1-4p}‖ < 1/4` (hypothesis for
`exp_symmetric_bch`) and `‖p·τ•A‖+‖p·τ•B‖ < 1/4`, `‖(1-4p)·τ•A‖+‖(1-4p)·τ•B‖ < 1/4`
(per-block hypotheses for `exp_strangBlock_log`). -/
theorem exp_suzuki5_symmetric_bch (A B : 𝔸) (p τ : 𝕂)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4)
    (hreg : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
            ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ < 1 / 4) :
    exp (bch (𝕂 := 𝕂)
      (bch (𝕂 := 𝕂)
        ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ))
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))) =
    suzuki5Product A B p τ := by
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  -- Apply exp_symmetric_bch with a = 4•X, b = Y.
  have key := exp_symmetric_bch (𝕂 := 𝕂) ((4 : 𝕂) • X) Y hreg
  -- key: exp(bch(bch(2⁻¹•(4•X), Y), 2⁻¹•(4•X))) = exp(2⁻¹•(4•X))·exp(Y)·exp(2⁻¹•(4•X))
  rw [key]
  -- Now: exp(2⁻¹•(4•X)) = exp(2•X) (since 2⁻¹•4 = 2)
  have h_scalar : (2 : 𝕂)⁻¹ • ((4 : 𝕂) • X) = (2 : 𝕂) • X := by
    rw [smul_smul]
    congr 1
    show (2 : 𝕂)⁻¹ * 4 = 2
    norm_num
  rw [h_scalar]
  -- Now: exp(2•X)·exp(Y)·exp(2•X) = strangBlock²·strangBlock_{1-4p}·strangBlock²
  -- Use strangBlock_mul_self and exp_strangBlock_log.
  have hexp2X : exp ((2 : 𝕂) • X) = strangBlock A B p τ * strangBlock A B p τ := by
    rw [← strangBlock_mul_self (𝕂 := 𝕂) A B p τ hp]
  have hexpY : exp Y = strangBlock A B (1 - 4 * p) τ :=
    exp_strangBlock_log (𝕂 := 𝕂) A B (1 - 4 * p) τ h1m4p
  rw [hexp2X, hexpY]
  -- Now: S_p²·S_{1-4p}·S_p² = suzuki5Product
  rw [suzuki5Product_eq_ACA]

include 𝕂 in
/-- **Key M4a decomposition**: `suzuki5_bch A B p τ = symmetric_bch(4•X, Y)`
where `X = strangBlock_log A B p τ` and `Y = strangBlock_log A B (1-4p) τ`.

Equivalently: `suzuki5_bch = bch(bch(2•X, Y), 2•X)`.

Hypotheses:
- Per-block regimes for `p` and `1-4p`: `‖cτ•A‖ + ‖cτ•B‖ < 1/4`.
- Symmetric-BCH regime: `‖4•X‖ + ‖Y‖ < 1/4`.
- Log injectivity: the overall 5-block argument norm bound `R < log 2` and
  `‖suzuki5_bch‖ < log 2`, `‖bch(bch(2•X,Y),2•X)‖ < log 2`. -/
theorem suzuki5_bch_eq_symmetric_bch (A B : 𝔸) (p τ : 𝕂)
    (hR : suzuki5ArgNormBound A B p τ < Real.log 2)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4)
    (hreg : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
            ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ < 1 / 4)
    (hZ1 : ‖suzuki5_bch 𝕂 A B p τ‖ < Real.log 2)
    (hZ2 : ‖bch (𝕂 := 𝕂)
      (bch (𝕂 := 𝕂)
        ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ))
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))‖ < Real.log 2) :
    suzuki5_bch 𝕂 A B p τ =
    bch (𝕂 := 𝕂)
      (bch (𝕂 := 𝕂)
        ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ))
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)) := by
  set Z₁ := suzuki5_bch 𝕂 A B p τ
  set Z₂ := bch (𝕂 := 𝕂)
    (bch (𝕂 := 𝕂)
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
      (strangBlock_log 𝕂 A B (1 - 4 * p) τ))
    ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
  -- exp(Z₁) = S(τ), exp(Z₂) = S(τ), so exp(Z₁) = exp(Z₂).
  have hexp1 : exp Z₁ = suzuki5Product A B p τ := exp_suzuki5_bch (𝕂 := 𝕂) A B p τ hR
  have hexp2 : exp Z₂ = suzuki5Product A B p τ :=
    exp_suzuki5_symmetric_bch (𝕂 := 𝕂) A B p τ hp h1m4p hreg
  have hexp_eq : exp Z₁ = exp Z₂ := by rw [hexp1, hexp2]
  -- By log injectivity: logOnePlus(exp Z - 1) = Z for ‖Z‖ < log 2.
  have hlog1 : logOnePlus (𝕂 := 𝕂) (exp Z₁ - 1) = Z₁ :=
    logOnePlus_exp_sub_one (𝕂 := 𝕂) Z₁ hZ1
  have hlog2 : logOnePlus (𝕂 := 𝕂) (exp Z₂ - 1) = Z₂ :=
    logOnePlus_exp_sub_one (𝕂 := 𝕂) Z₂ hZ2
  calc Z₁ = logOnePlus (𝕂 := 𝕂) (exp Z₁ - 1) := hlog1.symm
    _ = logOnePlus (𝕂 := 𝕂) (exp Z₂ - 1) := by rw [hexp_eq]
    _ = Z₂ := hlog2

/-! ### Commutator-based norm bound for symm_bch_cubic_poly

The key observation: `symm_bch_cubic_poly(a, b) = -(1/24)·[a,[a,b]] - (1/12)·[b,[a,b]]`
is *expressed entirely via the commutator* `[a,b] = a·b - b·a`. Hence its norm is
bounded linearly by `‖[a,b]‖`:
  `‖symm_bch_cubic_poly(a,b)‖ ≤ (1/6)·(‖a‖+‖b‖)·‖a·b - b·a‖`.

This is CRUCIAL for the M4a bound: when `a ≈ α·V` and `b ≈ β·V` (V = A+B), the
commutator `[a, b]` is O(R⁴) (because `[V, V] = 0` kills the leading term),
giving `symm_bch_cubic_poly(4X, Y) = O(R⁵)`.
-/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Commutator-based bound for `symmetric_bch_cubic_poly`**:
  `‖symm_bch_cubic_poly(a, b)‖ ≤ (1/6)·(‖a‖+‖b‖)·‖a*b - b*a‖`.

Proof: symm_bch_cubic_poly(a,b) = -(1/24)·[a,[a,b]] - (1/12)·[b,[a,b]] (both inner
commutators are built from [a,b]). Bound via `‖[x, y]‖ ≤ 2‖x‖·‖y‖`. -/
theorem norm_symmetric_bch_cubic_poly_le_commutator (a b : 𝔸) :
    ‖symmetric_bch_cubic_poly 𝕂 a b‖ ≤
      (6 : ℝ)⁻¹ * (‖a‖ + ‖b‖) * ‖a * b - b * a‖ := by
  set C : 𝔸 := a * b - b * a with hC_def
  set s := ‖a‖ + ‖b‖
  -- Rewrite symm_bch_cubic_poly using C:
  --   a·b - b·a = C
  --   b·a - a·b = -C
  -- symm_bch_cubic_poly = -(1/24)·(a·C - C·a) + (1/12)·(b·(-C) - (-C)·b)
  --                    = -(1/24)·(a·C - C·a) - (1/12)·(b·C - C·b)
  have h_rewrite : symmetric_bch_cubic_poly 𝕂 a b =
      -((24 : 𝕂)⁻¹ • (a * C - C * a)) - (12 : 𝕂)⁻¹ • (b * C - C * b) := by
    unfold symmetric_bch_cubic_poly
    -- Direct algebraic identity via hC_def and the smul/ring manipulations.
    rw [hC_def]
    -- Goal: -((24:𝕂)⁻¹ • (a*(ab-ba) - (ab-ba)*a)) + (12:𝕂)⁻¹ • (b*(ba-ab) - (ba-ab)*b) =
    --        -((24:𝕂)⁻¹ • (a*(ab-ba) - (ab-ba)*a)) - (12:𝕂)⁻¹ • (b*(ab-ba) - (ab-ba)*b)
    -- The (b·_ - _·b) terms differ by a sign: ba-ab = -(ab-ba).
    -- Clear smuls by injectivity-on-24 and injectivity-on-12 approach.
    have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
    have h3ne : (3 : 𝕂) ≠ 0 := by exact_mod_cast (show (3 : ℕ) ≠ 0 by norm_num)
    have h12ne : (12 : 𝕂) ≠ 0 := by exact_mod_cast (show (12 : ℕ) ≠ 0 by norm_num)
    have h24ne : (24 : 𝕂) ≠ 0 := by exact_mod_cast (show (24 : ℕ) ≠ 0 by norm_num)
    have hinj : Function.Injective ((24 : 𝕂) • · : 𝔸 → 𝔸) := by
      intro x y hxy
      have := congrArg ((24 : 𝕂)⁻¹ • ·) hxy
      simp only [smul_smul, inv_mul_cancel₀ h24ne, one_smul] at this; exact this
    apply hinj
    simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
      mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
      inv_mul_cancel₀ h24ne,
      show (24 : 𝕂) * (12 : 𝕂)⁻¹ = 2 from by norm_num,
      one_smul]
    noncomm_ring
  rw [h_rewrite]
  -- Bound each scalar-smul'd commutator.
  have h24 : ‖((24 : 𝕂)⁻¹ : 𝕂)‖ = (1 / 24 : ℝ) := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h12 : ‖((12 : 𝕂)⁻¹ : 𝕂)‖ = (1 / 12 : ℝ) := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have hCa : ‖a * C - C * a‖ ≤ 2 * ‖a‖ * ‖C‖ := by
    calc ‖a * C - C * a‖ ≤ ‖a * C‖ + ‖C * a‖ := by
          rw [sub_eq_add_neg]
          exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ ‖a‖ * ‖C‖ + ‖C‖ * ‖a‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖a‖ * ‖C‖ := by ring
  have hCb : ‖b * C - C * b‖ ≤ 2 * ‖b‖ * ‖C‖ := by
    calc ‖b * C - C * b‖ ≤ ‖b * C‖ + ‖C * b‖ := by
          rw [sub_eq_add_neg]
          exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ ‖b‖ * ‖C‖ + ‖C‖ * ‖b‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖b‖ * ‖C‖ := by ring
  have hs1 : ‖(24 : 𝕂)⁻¹ • (a * C - C * a)‖ ≤ (1 / 12 : ℝ) * ‖a‖ * ‖C‖ := by
    calc _ ≤ ‖(24 : 𝕂)⁻¹‖ * ‖a * C - C * a‖ := norm_smul_le _ _
      _ ≤ (1 / 24 : ℝ) * (2 * ‖a‖ * ‖C‖) := by rw [h24]; gcongr
      _ = (1 / 12 : ℝ) * ‖a‖ * ‖C‖ := by ring
  have hs2 : ‖(12 : 𝕂)⁻¹ • (b * C - C * b)‖ ≤ (1 / 6 : ℝ) * ‖b‖ * ‖C‖ := by
    calc _ ≤ ‖(12 : 𝕂)⁻¹‖ * ‖b * C - C * b‖ := norm_smul_le _ _
      _ ≤ (1 / 12 : ℝ) * (2 * ‖b‖ * ‖C‖) := by rw [h12]; gcongr
      _ = (1 / 6 : ℝ) * ‖b‖ * ‖C‖ := by ring
  have ha_nn : 0 ≤ ‖a‖ := norm_nonneg _
  have hb_nn : 0 ≤ ‖b‖ := norm_nonneg _
  have hC_nn : 0 ≤ ‖C‖ := norm_nonneg _
  calc ‖-((24 : 𝕂)⁻¹ • (a * C - C * a)) - (12 : 𝕂)⁻¹ • (b * C - C * b)‖
      ≤ ‖-((24 : 𝕂)⁻¹ • (a * C - C * a))‖ + ‖(12 : 𝕂)⁻¹ • (b * C - C * b)‖ :=
        norm_sub_le _ _
    _ = ‖(24 : 𝕂)⁻¹ • (a * C - C * a)‖ + ‖(12 : 𝕂)⁻¹ • (b * C - C * b)‖ := by rw [norm_neg]
    _ ≤ (1 / 12 : ℝ) * ‖a‖ * ‖C‖ + (1 / 6 : ℝ) * ‖b‖ * ‖C‖ := by linarith
    _ ≤ (6 : ℝ)⁻¹ * s * ‖C‖ := by
        show _ ≤ (6 : ℝ)⁻¹ * (‖a‖ + ‖b‖) * ‖C‖
        nlinarith

/-! ### Commutator bound for elements close to scalar multiples of V

When `a ≈ α·V` and `b ≈ β·V` (i.e., both are close to scalar multiples of a
common element `V`), the commutator `[a, b]` is small: the leading term
`[α•V, β•V] = αβ·[V,V] = 0` vanishes by scalar-commutativity, leaving only
contributions involving the "remainders" `a - α•V` and `b - β•V`.
-/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Commutator bound near V**: for any `V, a, b : 𝔸` and scalars `α, β : 𝕂`,
  `‖a·b - b·a‖ ≤ 2·‖α•V‖·‖b - β•V‖ + 2·‖β•V‖·‖a - α•V‖ + 2·‖a - α•V‖·‖b - β•V‖`.

Proof: write `a = α•V + δ_a` and `b = β•V + δ_b`. Then
  `a·b - b·a = (α•V)(β•V) - (β•V)(α•V) + (α•V)·δ_b - δ_b·(α•V)
             + δ_a·(β•V) - (β•V)·δ_a + δ_a·δ_b - δ_b·δ_a`.
The first pair cancels since scalars commute (`αβ·V² - βα·V² = 0`). -/
theorem norm_commutator_near_V_le (V a b : 𝔸) (α β : 𝕂) :
    ‖a * b - b * a‖ ≤
      2 * ‖α • V‖ * ‖b - β • V‖ + 2 * ‖β • V‖ * ‖a - α • V‖ +
      2 * ‖a - α • V‖ * ‖b - β • V‖ := by
  set δa := a - α • V with hδa_def
  set δb := b - β • V with hδb_def
  have ha_eq : a = α • V + δa := by rw [hδa_def]; abel
  have hb_eq : b = β • V + δb := by rw [hδb_def]; abel
  -- `(α•V) * (β•V) = (β•V) * (α•V)` since scalars commute.
  have h_comm_V : (α • V) * (β • V) = (β • V) * (α • V) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
        smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm β α]
  -- Expand a·b - b·a using distributive law manually (noncomm_ring has issues with smul).
  have hexpand : a * b - b * a =
      ((α • V) * δb - δb * (α • V)) + (δa * (β • V) - (β • V) * δa) +
      (δa * δb - δb * δa) := by
    have h1 : a * b = (α • V) * (β • V) + (α • V) * δb + δa * (β • V) + δa * δb := by
      rw [ha_eq, hb_eq]
      -- ((α•V) + δa) * ((β•V) + δb) expansion
      rw [add_mul, mul_add, mul_add]
      abel
    have h2 : b * a = (β • V) * (α • V) + (β • V) * δa + δb * (α • V) + δb * δa := by
      rw [ha_eq, hb_eq]
      rw [add_mul, mul_add, mul_add]
      abel
    rw [h1, h2, h_comm_V]
    abel
  rw [hexpand]
  calc ‖((α • V) * δb - δb * (α • V)) + (δa * (β • V) - (β • V) * δa) +
          (δa * δb - δb * δa)‖
      ≤ ‖((α • V) * δb - δb * (α • V)) + (δa * (β • V) - (β • V) * δa)‖ +
        ‖δa * δb - δb * δa‖ := norm_add_le _ _
    _ ≤ (‖(α • V) * δb - δb * (α • V)‖ + ‖δa * (β • V) - (β • V) * δa‖) +
        ‖δa * δb - δb * δa‖ := by gcongr; exact norm_add_le _ _
    _ ≤ 2 * ‖α • V‖ * ‖δb‖ + 2 * ‖β • V‖ * ‖δa‖ + 2 * ‖δa‖ * ‖δb‖ := by
        gcongr
        · calc ‖(α • V) * δb - δb * (α • V)‖
              ≤ ‖(α • V) * δb‖ + ‖δb * (α • V)‖ := norm_sub_le _ _
            _ ≤ ‖α • V‖ * ‖δb‖ + ‖δb‖ * ‖α • V‖ := by
                gcongr <;> exact norm_mul_le _ _
            _ = 2 * ‖α • V‖ * ‖δb‖ := by ring
        · calc ‖δa * (β • V) - (β • V) * δa‖
              ≤ ‖δa * (β • V)‖ + ‖(β • V) * δa‖ := norm_sub_le _ _
            _ ≤ ‖δa‖ * ‖β • V‖ + ‖β • V‖ * ‖δa‖ := by
                gcongr <;> exact norm_mul_le _ _
            _ = 2 * ‖β • V‖ * ‖δa‖ := by ring
        · calc ‖δa * δb - δb * δa‖
              ≤ ‖δa * δb‖ + ‖δb * δa‖ := norm_sub_le _ _
            _ ≤ ‖δa‖ * ‖δb‖ + ‖δb‖ * ‖δa‖ := by gcongr <;> exact norm_mul_le _ _
            _ = 2 * ‖δa‖ * ‖δb‖ := by ring

/-! ### Specialization: commutator bound for `[4·X, Y]` in the Suzuki setting

Combining `norm_commutator_near_V_le` (slice 8) and
`norm_strangBlock_log_sub_linear_le` (slice 4) yields a concrete bound on
`‖[4•X, Y] ‖` in terms of `η_p := ‖p·τ‖·(‖A‖+‖B‖)` and
`η_{1-4p} := ‖(1-4p)·τ‖·(‖A‖+‖B‖)`. This bound is `O(R⁴)` uniformly.
-/

include 𝕂 in
/-- **Commutator bound for the Suzuki-5 symmetric BCH arguments**: for
`X = strangBlock_log A B p τ` and `Y = strangBlock_log A B (1-4p) τ`,
  `‖(4·X)·Y - Y·(4·X)‖` is bounded by an explicit expression involving only
`η_p = ‖p·τ‖·(‖A‖+‖B‖)` and `η_{1-4p} = ‖(1-4p)·τ‖·(‖A‖+‖B‖)`.

The expression is a polynomial that's `O(η_p·η_{1-4p}³) + O(η_p³·η_{1-4p})` as
the leading term, thus O(R⁴) when η_p, η_{1-4p} ≤ R. -/
theorem norm_comm_4X_Y_le (A B : 𝔸) (p τ : 𝕂)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖(((4 : 𝕂) • strangBlock_log 𝕂 A B p τ) * strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        strangBlock_log 𝕂 A B (1 - 4 * p) τ * ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))‖ ≤
      2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
        (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) +
      2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
        (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) +
      2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
        (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  set V := A + B with hV_def
  -- Apply norm_commutator_near_V_le with a = 4•X, b = Y, α = 4p·τ, β = (1-4p)·τ.
  have hcomm := norm_commutator_near_V_le (𝕂 := 𝕂) V ((4 : 𝕂) • X) Y
    ((4 : 𝕂) * p * τ) ((1 - 4 * p) * τ)
  -- ‖a - α•V‖ = ‖4•X - 4p·τ•V‖ = 4·‖X - p·τ•V‖
  -- Using triangle with T_p = p·τ•V + (p·τ)³•E_sym:
  -- ‖X - p·τ•V‖ ≤ ‖X - T_p‖ + ‖(p·τ)³•E_sym‖ ≤ (p·τ)³·(‖A‖+‖B‖)³ + 10⁷·η_p⁵
  have hδa : ‖(4 : 𝕂) • X - (4 * p * τ : 𝕂) • V‖ ≤
      4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
           10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by
    -- 4•X - (4p·τ)•V = 4•(X - (p·τ)•V)
    have hsmul_eq : (4 : 𝕂) • X - (4 * p * τ : 𝕂) • V = (4 : 𝕂) • (X - (p * τ : 𝕂) • V) := by
      rw [smul_sub, smul_smul]
      congr 2
      ring
    rw [hsmul_eq]
    -- ‖4•(X - (p·τ)•V)‖ ≤ 4·‖X - (p·τ)•V‖
    have h4_norm : ‖(4 : 𝕂) • (X - (p * τ : 𝕂) • V)‖ ≤ 4 * ‖X - (p * τ : 𝕂) • V‖ := by
      have h4_scalar_norm : ‖(4 : 𝕂)‖ = 4 := by rw [RCLike.norm_ofNat]
      calc ‖(4 : 𝕂) • (X - (p * τ : 𝕂) • V)‖ ≤ ‖(4 : 𝕂)‖ * ‖X - (p * τ : 𝕂) • V‖ :=
            norm_smul_le _ _
        _ = 4 * ‖X - (p * τ : 𝕂) • V‖ := by rw [h4_scalar_norm]
    refine le_trans h4_norm ?_
    -- Now: 4·‖X - (p·τ)•V‖ ≤ 4·(‖X - T_p‖ + ‖(p·τ)³•E_sym‖)
    have hlin := norm_strangBlock_log_sub_linear_le (𝕂 := 𝕂) A B p τ hp
    -- hlin : ‖strangBlock_log - (p·τ)•(A+B)‖ ≤ η³ + 10⁷·η⁵
    -- But hlin has bound (‖p·τ‖·(‖A‖+‖B‖))³, not ‖p·τ‖³·(‖A‖+‖B‖)³. They are equal.
    have : (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 = ‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 := by ring
    gcongr
    calc ‖X - (p * τ : 𝕂) • V‖
        ≤ _ := hlin
      _ = ‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 := by rw [this]
  have hδb : ‖Y - ((1 - 4 * p) * τ : 𝕂) • V‖ ≤
      ‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
        10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 := by
    have hlin := norm_strangBlock_log_sub_linear_le (𝕂 := 𝕂) A B (1 - 4 * p) τ h1m4p
    have : (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 =
        ‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 := by ring
    calc ‖Y - ((1 - 4 * p) * τ : 𝕂) • V‖ ≤ _ := hlin
      _ = ‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 := by rw [this]
  -- Now apply hcomm with hδa and hδb as the bounds on "δa" and "δb".
  refine le_trans hcomm ?_
  gcongr

/-! ### Target sum in 4·T_p + T_{1-4p} form

Convenient restatement of the target sum used in the M4a assembly. -/

include 𝕂 in
/-- Target decomposition: `4•T_p + T_{1-4p} = τ•(A+B) + τ³·C₃(p)•E_sym(A,B)`.
Restatement of `suzuki5_targets_sum` using smul `(4:𝕂) • T_p` instead of
the repeated-addition form `T_p + T_p + T_p + T_p`. -/
theorem target_sum_4_form (A B : 𝔸) (p τ : 𝕂) :
    (4 : 𝕂) • strangBlock_log_target 𝕂 A B p τ +
      strangBlock_log_target 𝕂 A B (1 - 4 * p) τ =
    τ • (A + B) +
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B := by
  unfold strangBlock_log_target suzuki5_bch_cubic_coeff
  set V := A + B with hV_def
  set E := symmetric_bch_cubic_poly 𝕂 A B with hE_def
  -- 4•((p·τ)•V + (p·τ)³•E) = (4·(p·τ))•V + (4·(p·τ)³)•E
  -- Combine with ((1-4p)·τ)•V + ((1-4p)·τ)³•E
  -- to get (4*p*τ + (1-4p)*τ)•V + (4*(p*τ)^3 + ((1-4p)*τ)^3)•E
  -- and simplify scalar expressions.
  rw [smul_add, smul_smul, smul_smul]
  -- Goal: (4·(p·τ))•V + (4·(p·τ)³)•E + ((1-4p)·τ)•V + ((1-4p)·τ)³•E = ...
  have h1 : ((4 : 𝕂) * (p * τ)) • V + ((4 : 𝕂) * (p * τ) ^ 3) • E +
            (((1 - 4 * p) * τ) • V + ((1 - 4 * p) * τ) ^ 3 • E) =
            (((4 : 𝕂) * (p * τ)) + ((1 - 4 * p) * τ)) • V +
            (((4 : 𝕂) * (p * τ) ^ 3) + ((1 - 4 * p) * τ) ^ 3) • E := by
    rw [add_smul, add_smul]; abel
  rw [h1]
  -- Simplify scalar coefficients
  congr 1
  · -- (4·(p·τ)) + ((1-4p)·τ) = τ
    congr 1
    ring
  · -- (4·(p·τ)³) + ((1-4p)·τ)³ = τ³ · (4p³ + (1-4p)³)
    congr 1
    ring

/-! ### M4a main theorem (symmetric-BCH assembly)

Using the symmetric-BCH decomposition from slice 6,
  `suzuki5_bch = bch(bch(2•X, Y), 2•X) = (4•X + Y) + symmetric_bch_cubic(4•X, Y)`
the main theorem assembles the triangle inequality:

  ‖suzuki5_bch - target‖
    ≤ ‖4•(X - T_p)‖ + ‖Y - T_{1-4p}‖               -- per-block cubic
      + ‖symmetric_bch_cubic(4•X, Y) - symm_bch_cubic_poly(4•X, Y)‖   -- 10⁷·s⁵
      + ‖symm_bch_cubic_poly(4•X, Y)‖                -- (1/6)·(‖4X‖+‖Y‖)·‖[4X,Y]‖

where `[4X, Y]` is bounded by the slice-9 commutator bound.

For simplicity, we state the bound in the form `K·(‖4X‖ + ‖Y‖ + s_p + s_{1-4p})^4`
where `s_c = ‖(cτ)•A‖+‖(cτ)•B‖` are per-block argument norms. This avoids the
algebraic conversion to `suzuki5ArgNormBound`.
-/

include 𝕂 in
/-- **M4a main theorem (symmetric-BCH form)**: the Suzuki-5 BCH element equals
its linear+cubic target up to a quartic-plus-higher remainder, bounded via
the symmetric-BCH decomposition.

The bound is expressed as the sum of three contributions:
(a) per-block cubic error `4·‖X - T_p‖ + ‖Y - T_{1-4p}‖`,
(b) the quintic remainder from `symm_bch_cubic - symm_bch_cubic_poly`,
(c) the commutator-based bound on `symm_bch_cubic_poly(4•X, Y)` via slices 7-9.

Each contribution is O(R⁴) or smaller under the stated hypotheses. -/
theorem norm_suzuki5_bch_sub_smul_sub_cubic_le (A B : 𝔸) (p τ : 𝕂)
    (hR : suzuki5ArgNormBound A B p τ < Real.log 2)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4)
    (hreg : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
            ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ < 1 / 4)
    (hZ1 : ‖suzuki5_bch 𝕂 A B p τ‖ < Real.log 2)
    (hZ2 : ‖bch (𝕂 := 𝕂)
      (bch (𝕂 := 𝕂)
        ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ))
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))‖ < Real.log 2) :
    ‖suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B‖ ≤
      4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) +
      10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5 +
      10000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                  ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 5 +
      (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                   ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
        (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
          (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) +
        2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
          (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) +
        2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
              10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
          (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) := by
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  set V := A + B with hV_def
  set E := symmetric_bch_cubic_poly 𝕂 A B with hE_def
  set T_p := strangBlock_log_target 𝕂 A B p τ with hTp_def
  set T_q := strangBlock_log_target 𝕂 A B (1 - 4 * p) τ with hTq_def
  -- Step 1: suzuki5_bch = bch(bch(2•X, Y), 2•X) (via slice 6)
  have h_sym_bch :=
    suzuki5_bch_eq_symmetric_bch (𝕂 := 𝕂) A B p τ hR hp h1m4p hreg hZ1 hZ2
  -- Step 2: bch(bch(2•X, Y), 2•X) = (4•X + Y) + symmetric_bch_cubic(4•X, Y)
  have h_sbc_def : bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂)
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • X)) Y) ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • X)) =
      ((4 : 𝕂) • X + Y) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y := by
    unfold symmetric_bch_cubic
    abel
  -- Combine: suzuki5_bch = (4•X + Y) + symmetric_bch_cubic(4•X, Y)
  have h_decomp : suzuki5_bch 𝕂 A B p τ =
      ((4 : 𝕂) • X + Y) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y := by
    rw [h_sym_bch]; exact h_sbc_def
  -- Step 3: target = 4•T_p + T_q (via target_sum_4_form)
  have h_target : τ • V + (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • E =
      (4 : 𝕂) • T_p + T_q := by
    rw [hTp_def, hTq_def, hV_def, hE_def]
    rw [target_sum_4_form (𝕂 := 𝕂)]
  -- Step 4: rewrite the goal's LHS using h_decomp and h_target.
  -- suzuki5_bch - target = ((4•X + Y) + symm_bch_cubic) - (4•T_p + T_q)
  --                    = 4•(X - T_p) + (Y - T_q) + symm_bch_cubic(4•X, Y)
  have h_diff_eq : suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • E =
      ((4 : 𝕂) • (X - T_p)) + (Y - T_q) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y := by
    -- First, rewrite `τ • (A + B) + (τ³ * C₃) • E = (4:𝕂)•T_p + T_q` using target_sum_4_form.
    have h_target_expanded :
        τ • (A + B) + (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • E =
        (4 : 𝕂) • T_p + T_q := by
      rw [hTp_def, hTq_def, hE_def]
      exact (target_sum_4_form (𝕂 := 𝕂) A B p τ).symm
    -- Convert `a - b - c` to `a - (b + c)` for easier substitution.
    have hsub_regroup : suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • E =
        suzuki5_bch 𝕂 A B p τ - (τ • (A + B) + (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • E) := by
      abel
    rw [hsub_regroup, h_target_expanded, h_decomp, smul_sub]
    abel
  rw [h_diff_eq]
  -- Now bound: 4•(X - T_p) + (Y - T_q) + symm_bch_cubic(4•X, Y)
  have h_X_minus_Tp : ‖X - T_p‖ ≤ 10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5 := by
    exact norm_strangBlock_log_sub_target_le (𝕂 := 𝕂) A B p τ hp
  have h_Y_minus_Tq : ‖Y - T_q‖ ≤
      10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5 := by
    exact norm_strangBlock_log_sub_target_le (𝕂 := 𝕂) A B (1 - 4 * p) τ h1m4p
  -- Bound for 4•(X - T_p)
  have h4_norm_eq : ‖(4 : 𝕂)‖ = 4 := by rw [RCLike.norm_ofNat]
  have h_4Xmp : ‖(4 : 𝕂) • (X - T_p)‖ ≤
      4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) := by
    calc ‖(4 : 𝕂) • (X - T_p)‖ ≤ ‖(4 : 𝕂)‖ * ‖X - T_p‖ := norm_smul_le _ _
      _ = 4 * ‖X - T_p‖ := by rw [h4_norm_eq]
      _ ≤ 4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) := by gcongr
  -- Bound for symm_bch_cubic(4•X, Y) via norm_symmetric_bch_cubic_sub_poly_le
  have h_sbc_bound : ‖symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y‖ ≤
      10000000 * (‖(4 : 𝕂) • X‖ + ‖Y‖) ^ 5 +
      (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • X‖ + ‖Y‖) *
        ‖((4 : 𝕂) • X) * Y - Y * ((4 : 𝕂) • X)‖ := by
    have h_sub_poly := norm_symmetric_bch_cubic_sub_poly_le (𝕂 := 𝕂)
      ((4 : 𝕂) • X) Y hreg
    have h_poly := norm_symmetric_bch_cubic_poly_le_commutator (𝕂 := 𝕂)
      ((4 : 𝕂) • X) Y
    calc ‖symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y‖
        = ‖(symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
             symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y) +
            symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y‖ := by abel_nf
      _ ≤ ‖symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y‖ +
          ‖symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y‖ := norm_add_le _ _
      _ ≤ 10000000 * (‖(4 : 𝕂) • X‖ + ‖Y‖) ^ 5 +
          (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • X‖ + ‖Y‖) *
            ‖((4 : 𝕂) • X) * Y - Y * ((4 : 𝕂) • X)‖ := by linarith
  -- Commutator bound from slice 9
  have h_comm_bound := norm_comm_4X_Y_le (𝕂 := 𝕂) A B p τ hp h1m4p
  -- Final triangle inequality
  calc ‖(4 : 𝕂) • (X - T_p) + (Y - T_q) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y‖
      ≤ ‖(4 : 𝕂) • (X - T_p) + (Y - T_q)‖ +
        ‖symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y‖ := norm_add_le _ _
    _ ≤ (‖(4 : 𝕂) • (X - T_p)‖ + ‖Y - T_q‖) +
        ‖symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) +
         10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5) +
        (10000000 * (‖(4 : 𝕂) • X‖ + ‖Y‖) ^ 5 +
         (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • X‖ + ‖Y‖) *
           ‖((4 : 𝕂) • X) * Y - Y * ((4 : 𝕂) • X)‖) := by
        gcongr
    _ ≤ 4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) +
        10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5 +
        10000000 * (‖(4 : 𝕂) • X‖ + ‖Y‖) ^ 5 +
        (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • X‖ + ‖Y‖) *
          (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
            (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
              10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) +
          2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
            (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
              10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) +
          2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
            (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
              10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) := by
        -- Use h_comm_bound to bound the commutator norm
        have hpos : 0 ≤ (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • X‖ + ‖Y‖) := by positivity
        nlinarith [h_comm_bound, norm_nonneg (((4 : 𝕂) • X) * Y - Y * ((4 : 𝕂) • X)),
                   norm_nonneg ((4 : 𝕂) • X), norm_nonneg Y]

/-! ### M4b: cubic vanishing under IsSuzukiCubic

Under the Suzuki condition `4p³ + (1-4p)³ = 0`, the cubic coefficient vanishes
and M4a collapses to a direct O(R⁴) bound on `suzuki5_bch - τ•(A+B)`.
-/

include 𝕂 in
/-- **M4b**: under the Suzuki cubic-cancellation condition, the cubic correction
term vanishes, giving the sharper bound

  `‖suzuki5_bch A B p τ - τ•(A+B)‖ ≤ (M4a bound)`

which is O(R⁴) — an order-of-magnitude improvement over M3b's O(R²). -/
theorem norm_suzuki5_bch_sub_smul_le_of_IsSuzukiCubic (A B : 𝔸) (p τ : 𝕂)
    (hSuzuki : IsSuzukiCubic p)
    (hR : suzuki5ArgNormBound A B p τ < Real.log 2)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4)
    (hreg : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
            ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ < 1 / 4)
    (hZ1 : ‖suzuki5_bch 𝕂 A B p τ‖ < Real.log 2)
    (hZ2 : ‖bch (𝕂 := 𝕂)
      (bch (𝕂 := 𝕂)
        ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ))
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))‖ < Real.log 2) :
    ‖suzuki5_bch 𝕂 A B p τ - τ • (A + B)‖ ≤
      4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) +
      10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5 +
      10000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                  ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 5 +
      (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                   ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
        (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
          (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) +
        2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
          (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) +
        2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
              10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
          (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) := by
  -- Under IsSuzukiCubic, the cubic coefficient is zero so the cubic term vanishes.
  have h_coef_zero : suzuki5_bch_cubic_coeff 𝕂 p = 0 :=
    suzuki5_bch_cubic_coeff_eq_zero_of_IsSuzukiCubic hSuzuki
  have h_cubic_zero :
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B = 0 := by
    rw [h_coef_zero, mul_zero, zero_smul]
  have h_eq : suzuki5_bch 𝕂 A B p τ - τ • (A + B) =
      suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B := by
    rw [h_cubic_zero, sub_zero]
  rw [h_eq]
  exact norm_suzuki5_bch_sub_smul_sub_cubic_le (𝕂 := 𝕂) A B p τ hR hp h1m4p hreg hZ1 hZ2

/-! ### Norm bound for strangBlock_log

Useful intermediate: bounds `‖strangBlock_log‖` by the argument norm plus
cubic/quintic corrections. Derived by triangle inequality from slice 4.
-/

include 𝕂 in
/-- `‖strangBlock_log A B c τ‖ ≤ η + η³ + 10⁷·η⁵` where `η = ‖c*τ‖·(‖A‖+‖B‖)`.
Follows from triangle inequality with slice 4's linear-remainder cubic bound. -/
theorem norm_strangBlock_log_le (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4) :
    ‖strangBlock_log 𝕂 A B c τ‖ ≤
      ‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖) +
      (‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 +
      10000000 * (‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 := by
  set η := ‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖) with hη_def
  -- ‖strangBlock_log - (cτ)•V‖ ≤ η³ + 10⁷·η⁵ (slice 4)
  have hlin := norm_strangBlock_log_sub_linear_le (𝕂 := 𝕂) A B c τ h
  -- ‖(cτ)•V‖ ≤ ‖cτ‖·‖V‖ ≤ ‖cτ‖·(‖A‖+‖B‖) = η
  have hV_bound : ‖(c * τ) • (A + B)‖ ≤ η := by
    calc ‖(c * τ) • (A + B)‖ ≤ ‖(c * τ : 𝕂)‖ * ‖A + B‖ := norm_smul_le _ _
      _ ≤ ‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖) := by gcongr; exact norm_add_le _ _
      _ = η := by rw [hη_def]
  -- Triangle: ‖sb_log‖ ≤ ‖sb_log - (cτ)•V‖ + ‖(cτ)•V‖
  calc ‖strangBlock_log 𝕂 A B c τ‖
      = ‖(strangBlock_log 𝕂 A B c τ - (c * τ) • (A + B)) + (c * τ) • (A + B)‖ := by
        congr 1; abel
    _ ≤ ‖strangBlock_log 𝕂 A B c τ - (c * τ) • (A + B)‖ + ‖(c * τ) • (A + B)‖ :=
        norm_add_le _ _
    _ ≤ (η ^ 3 + 10000000 * η ^ 5) + η := by
        gcongr
    _ = η + η ^ 3 + 10000000 * η ^ 5 := by ring

/-! ### Reduction of per-block argument norms to `R`

Useful building blocks for M5 (clean quintic form). Show that the per-block
argument norms `η_c := ‖c·τ‖·(‖A‖+‖B‖)` are bounded by explicit multiples of
`R := suzuki5ArgNormBound A B p τ`.
-/

include 𝕂 in
/-- `η_p := ‖p·τ‖·(‖A‖+‖B‖) ≤ (7/12)·R`, where `R = suzuki5ArgNormBound A B p τ`.
Derived from the structure of `suzuki5ArgNormBound`:
  `R ≥ 3·‖p‖·‖τ‖·‖A‖ + 4·‖p‖·‖τ‖·‖B‖` ⟹ `‖p·τ‖·‖A‖ ≤ R/3`, `‖p·τ‖·‖B‖ ≤ R/4`. -/
theorem norm_p_tau_s_le_R (A B : 𝔸) (p τ : 𝕂) :
    ‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖) ≤ (7 / 12) * suzuki5ArgNormBound A B p τ := by
  unfold suzuki5ArgNormBound
  have hnorm_eq : ‖(p * τ : 𝕂)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hpnn : 0 ≤ ‖p‖ := norm_nonneg _
  have hτnn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hAnn : 0 ≤ ‖A‖ := norm_nonneg _
  have hBnn : 0 ≤ ‖B‖ := norm_nonneg _
  have h13pnn : 0 ≤ ‖1 - 3 * p‖ := norm_nonneg _
  have h14pnn : 0 ≤ ‖1 - 4 * p‖ := norm_nonneg _
  rw [hnorm_eq]
  -- We want: ‖p‖·‖τ‖·(‖A‖+‖B‖) ≤ (7/12) · ‖τ‖·((3‖p‖+‖1-3p‖)·‖A‖ + (4‖p‖+‖1-4p‖)·‖B‖)
  -- LHS = ‖p‖·‖τ‖·‖A‖ + ‖p‖·‖τ‖·‖B‖
  -- 12·LHS = 12·‖p‖·‖τ‖·‖A‖ + 12·‖p‖·‖τ‖·‖B‖
  -- RHS = 7·‖τ‖·((3‖p‖+‖1-3p‖)·‖A‖ + (4‖p‖+‖1-4p‖)·‖B‖)
  --     = 21·‖p‖·‖τ‖·‖A‖ + 7·‖1-3p‖·‖τ‖·‖A‖ + 28·‖p‖·‖τ‖·‖B‖ + 7·‖1-4p‖·‖τ‖·‖B‖
  -- Need 12·LHS ≤ 12·RHS, equivalently LHS ≤ RHS.
  nlinarith [hpnn, hτnn, hAnn, hBnn, h13pnn, h14pnn,
             mul_nonneg hpnn hτnn,
             mul_nonneg (mul_nonneg hpnn hτnn) hAnn,
             mul_nonneg (mul_nonneg hpnn hτnn) hBnn,
             mul_nonneg (mul_nonneg h13pnn hτnn) hAnn,
             mul_nonneg (mul_nonneg h14pnn hτnn) hBnn]

include 𝕂 in
/-- `η_{1-4p} := ‖(1-4p)·τ‖·(‖A‖+‖B‖) ≤ 2·R`, where `R = suzuki5ArgNormBound A B p τ`.
Derived from the same structure:
  `R ≥ ‖1-4p‖·‖τ‖·‖A‖` (via `‖1-4p‖ ≤ 3‖p‖+‖1-3p‖`) and `R ≥ ‖1-4p‖·‖τ‖·‖B‖`. -/
theorem norm_1m4p_tau_s_le_R (A B : 𝔸) (p τ : 𝕂) :
    ‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖) ≤ 2 * suzuki5ArgNormBound A B p τ := by
  unfold suzuki5ArgNormBound
  have hnorm_eq : ‖((1 - 4 * p) * τ : 𝕂)‖ = ‖1 - 4 * p‖ * ‖τ‖ := norm_mul _ _
  have hpnn : 0 ≤ ‖p‖ := norm_nonneg _
  have hτnn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hAnn : 0 ≤ ‖A‖ := norm_nonneg _
  have hBnn : 0 ≤ ‖B‖ := norm_nonneg _
  have h13pnn : 0 ≤ ‖1 - 3 * p‖ := norm_nonneg _
  have h14pnn : 0 ≤ ‖1 - 4 * p‖ := norm_nonneg _
  -- Key inequality: ‖1 - 4p‖ = ‖(1-3p) - p‖ ≤ ‖1-3p‖ + ‖p‖
  have h14p_bound : ‖1 - 4 * p‖ ≤ ‖1 - 3 * p‖ + ‖p‖ := by
    have : (1 - 4 * p : 𝕂) = (1 - 3 * p) - p := by ring
    rw [this]
    exact norm_sub_le _ _
  -- Hence ‖1-4p‖ ≤ 3‖p‖ + ‖1-3p‖ (since ‖p‖ ≤ 3‖p‖).
  have h14p_bound2 : ‖1 - 4 * p‖ ≤ 3 * ‖p‖ + ‖1 - 3 * p‖ := by linarith
  rw [hnorm_eq]
  -- Split into the A and B contributions.
  -- A part: ‖1-4p‖·‖τ‖·‖A‖ ≤ (3‖p‖+‖1-3p‖)·‖τ‖·‖A‖ ≤ 2·(3‖p‖+‖1-3p‖)·‖τ‖·‖A‖
  have hA_part : ‖1 - 4 * p‖ * ‖τ‖ * ‖A‖ ≤
      2 * ((3 * ‖p‖ + ‖1 - 3 * p‖) * ‖τ‖ * ‖A‖) := by
    have : ‖1 - 4 * p‖ * ‖τ‖ * ‖A‖ ≤ (3 * ‖p‖ + ‖1 - 3 * p‖) * ‖τ‖ * ‖A‖ := by
      gcongr
    linarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hpnn) h13pnn) hτnn) hAnn]
  -- B part: ‖1-4p‖·‖τ‖·‖B‖ ≤ (4‖p‖+‖1-4p‖)·‖τ‖·‖B‖ ≤ 2·(4‖p‖+‖1-4p‖)·‖τ‖·‖B‖
  have hB_part : ‖1 - 4 * p‖ * ‖τ‖ * ‖B‖ ≤
      2 * ((4 * ‖p‖ + ‖1 - 4 * p‖) * ‖τ‖ * ‖B‖) := by
    have : ‖1 - 4 * p‖ * ‖τ‖ * ‖B‖ ≤ (4 * ‖p‖ + ‖1 - 4 * p‖) * ‖τ‖ * ‖B‖ := by
      have : ‖1 - 4 * p‖ ≤ 4 * ‖p‖ + ‖1 - 4 * p‖ := by linarith
      gcongr
    linarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hpnn) h14pnn) hτnn) hBnn]
  -- Combine using `mul_add` and `add_mul`.
  calc ‖1 - 4 * p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
      = ‖1 - 4 * p‖ * ‖τ‖ * ‖A‖ + ‖1 - 4 * p‖ * ‖τ‖ * ‖B‖ := by ring
    _ ≤ 2 * ((3 * ‖p‖ + ‖1 - 3 * p‖) * ‖τ‖ * ‖A‖) +
        2 * ((4 * ‖p‖ + ‖1 - 4 * p‖) * ‖τ‖ * ‖B‖) := by linarith
    _ = 2 * (‖τ‖ * ((3 * ‖p‖ + ‖1 - 3 * p‖) * ‖A‖ + (4 * ‖p‖ + ‖1 - 4 * p‖) * ‖B‖)) := by
        ring

/-! ### Bound on `‖4•X‖ + ‖Y‖` in terms of `R = suzuki5ArgNormBound`

Combining `norm_strangBlock_log_le` with the η_c ≤ R reduction lemmas gives
an explicit bound on the composite norm `‖4•X‖ + ‖Y‖` — essential for M5's
clean quintic form.
-/

include 𝕂 in
/-- **Composite norm bound**: `‖4•X‖ + ‖Y‖` is bounded by an explicit expression
in η_p and η_{1-4p}. Each is bounded by a polynomial in the respective argument
norm via `norm_strangBlock_log_le`. -/
theorem norm_4X_plus_Y_le_eta (A B : 𝔸) (p τ : 𝕂)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
      ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ ≤
      4 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖) +
           (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 +
           10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) +
      (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖) +
       (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 +
       10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by
  -- ‖4•X‖ ≤ ‖4‖·‖X‖ = 4·‖X‖
  have h4X : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ ≤
      4 * ‖strangBlock_log 𝕂 A B p τ‖ := by
    have h4_norm : ‖(4 : 𝕂)‖ = 4 := by rw [RCLike.norm_ofNat]
    calc ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖
        ≤ ‖(4 : 𝕂)‖ * ‖strangBlock_log 𝕂 A B p τ‖ := norm_smul_le _ _
      _ = 4 * ‖strangBlock_log 𝕂 A B p τ‖ := by rw [h4_norm]
  -- ‖X‖ bound
  have hX_bound := norm_strangBlock_log_le (𝕂 := 𝕂) A B p τ hp
  have hY_bound := norm_strangBlock_log_le (𝕂 := 𝕂) A B (1 - 4 * p) τ h1m4p
  calc ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
       ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖
      ≤ 4 * ‖strangBlock_log 𝕂 A B p τ‖ +
        ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ := by linarith
    _ ≤ 4 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖) +
            (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 +
            10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) +
        (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖) +
         (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 3 +
         10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by gcongr

/-! ### Telescoping norm bound for `(X + δ)^n - X^n`

The key analytic input for exp-Lipschitz: `‖(X+δ)^(n+1) - X^(n+1)‖ ≤ (n+1)·‖δ‖·(‖X‖+‖δ‖)^n`.
Proved by induction using the identity
  `(X+δ)^(n+2) - X^(n+2) = X · ((X+δ)^(n+1) - X^(n+1)) + δ · (X+δ)^(n+1)`. -/

/-- Telescoping norm bound: `‖(X + δ)^(n+1) - X^(n+1)‖ ≤ (n+1) · ‖δ‖ · (‖X‖+‖δ‖)^n`. -/
theorem norm_pow_add_sub_pow_le (X δ : 𝔸) :
    ∀ n : ℕ, ‖(X + δ) ^ (n + 1) - X ^ (n + 1)‖ ≤
      (n + 1 : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n
  | 0 => by
      have : (X + δ) ^ 1 - X ^ 1 = δ := by rw [pow_one, pow_one]; abel
      rw [this]; simp
  | n + 1 => by
      -- identity: (X+δ)^(n+2) - X^(n+2) = X · ((X+δ)^(n+1) - X^(n+1)) + δ · (X+δ)^(n+1)
      have ih := norm_pow_add_sub_pow_le X δ n
      have h_id : (X + δ) ^ (n + 1 + 1) - X ^ (n + 1 + 1) =
          X * ((X + δ) ^ (n + 1) - X ^ (n + 1)) + δ * (X + δ) ^ (n + 1) := by
        rw [pow_succ' (X + δ) (n + 1), pow_succ' X (n + 1), add_mul]
        noncomm_ring
      rw [h_id]
      have hXnn : 0 ≤ ‖X‖ := norm_nonneg _
      have hδnn : 0 ≤ ‖δ‖ := norm_nonneg _
      have hMnn : 0 ≤ ‖X‖ + ‖δ‖ := add_nonneg hXnn hδnn
      have hMn_nn : 0 ≤ (‖X‖ + ‖δ‖) ^ n := pow_nonneg hMnn n
      have hMn1_nn : 0 ≤ (‖X‖ + ‖δ‖) ^ (n + 1) := pow_nonneg hMnn (n + 1)
      have hcoef_nn : 0 ≤ (n + 1 : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n := by positivity
      -- `‖(X+δ)^(n+1)‖ ≤ (‖X‖+‖δ‖)^(n+1)`
      have h_pow_Xδ : ‖(X + δ) ^ (n + 1)‖ ≤ (‖X‖ + ‖δ‖) ^ (n + 1) := by
        calc ‖(X + δ) ^ (n + 1)‖ ≤ ‖X + δ‖ ^ (n + 1) := norm_pow_le _ _
          _ ≤ (‖X‖ + ‖δ‖) ^ (n + 1) := by
              gcongr
              exact norm_add_le _ _
      calc ‖X * ((X + δ) ^ (n + 1) - X ^ (n + 1)) + δ * (X + δ) ^ (n + 1)‖
          ≤ ‖X * ((X + δ) ^ (n + 1) - X ^ (n + 1))‖ + ‖δ * (X + δ) ^ (n + 1)‖ :=
            norm_add_le _ _
        _ ≤ ‖X‖ * ‖(X + δ) ^ (n + 1) - X ^ (n + 1)‖ +
            ‖δ‖ * ‖(X + δ) ^ (n + 1)‖ := by
            gcongr <;> exact norm_mul_le _ _
        _ ≤ ‖X‖ * ((n + 1 : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n) +
            ‖δ‖ * (‖X‖ + ‖δ‖) ^ (n + 1) := by gcongr
        _ ≤ (‖X‖ + ‖δ‖) * ((n + 1 : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n) +
            ‖δ‖ * (‖X‖ + ‖δ‖) ^ (n + 1) := by
            have h_le : ‖X‖ ≤ ‖X‖ + ‖δ‖ := by linarith
            gcongr
        _ = ((n + 1 : ℕ) + 1 : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ (n + 1) := by
            push_cast
            ring

/-! ### M6: Iterated Suzuki product and exponential form

Connects the Suzuki-5 BCH to iterated products. Since `suzuki5_bch` commutes with
itself, `S(τ)^n = exp(n • suzuki5_bch)`. Combined with M4b, this gives
`S(τ)^n = exp(n·τ·(A+B) + n·δ)` where `‖δ‖ = O(|τ|⁵·s⁵)` under IsSuzukiCubic,
yielding the `O(1/n⁴)` Trotter-h4 rate.
-/

/-- The `n`-fold iterated Suzuki-5 product: matches `Lean-Trotter`'s `s4Func`
interpretation for fixed Suzuki parameter `p`. -/
noncomputable def s4Func (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (p τ : 𝕂) (n : ℕ) : 𝔸 :=
  (suzuki5Product A B p τ) ^ n

include 𝕂 in
/-- **Exponential form of the iterated Suzuki-5 product**: in the regime where
`suzuki5_bch` is well-defined, `s4Func A B p τ n = exp(n • suzuki5_bch A B p τ)`.

Follows from `exp(suzuki5_bch) = S(τ)` (M2b round-trip) + `exp(n•x) = exp(x)^n`
(since any element commutes with itself). -/
theorem s4Func_eq_exp_nsmul (A B : 𝔸) (p τ : 𝕂) (n : ℕ)
    (h : suzuki5ArgNormBound A B p τ < Real.log 2) :
    s4Func 𝕂 A B p τ n = exp ((n : 𝕂) • suzuki5_bch 𝕂 A B p τ) := by
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold s4Func
  have hexp : exp (suzuki5_bch 𝕂 A B p τ) = suzuki5Product A B p τ :=
    exp_suzuki5_bch (𝕂 := 𝕂) A B p τ h
  rw [← hexp]
  -- Convert (n : 𝕂) smul to ℕ nsmul to use exp_nsmul
  have h_smul_eq : ((n : 𝕂) • suzuki5_bch 𝕂 A B p τ) = n • suzuki5_bch 𝕂 A B p τ := by
    rw [← Nat.cast_smul_eq_nsmul 𝕂]
  rw [h_smul_eq, exp_nsmul]

/-! ### Scaled M4b bound: `‖n • (suzuki5_bch - τ•V)‖`

For Trotter h4, we want the error of `exp(n • suzuki5_bch)` vs `exp(n·τ•V)`,
which by exp-Lipschitz-like arguments scales with `‖n • (suzuki5_bch - τ•V)‖`.
Bounded as `n` times M4b's bound. -/

include 𝕂 in
/-- `‖n • (suzuki5_bch - τ•V)‖ ≤ n · (M4b bound)` under IsSuzukiCubic.
Useful for Trotter-h4 error analysis: setting τ = t/n, this gives
`‖n • (suzuki5_bch(t/n) - (t/n)•V)‖ ≤ n · K · |t/n|⁵ · s⁵ = K · t⁵ · s⁵ / n⁴`. -/
theorem norm_nsmul_suzuki5_bch_sub_smul_le_of_IsSuzukiCubic (A B : 𝔸) (p τ : 𝕂) (n : ℕ)
    (hSuzuki : IsSuzukiCubic p)
    (hR : suzuki5ArgNormBound A B p τ < Real.log 2)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4)
    (hreg : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
            ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ < 1 / 4)
    (hZ1 : ‖suzuki5_bch 𝕂 A B p τ‖ < Real.log 2)
    (hZ2 : ‖bch (𝕂 := 𝕂)
      (bch (𝕂 := 𝕂)
        ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ))
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ))‖ < Real.log 2) :
    ‖(n : 𝕂) • (suzuki5_bch 𝕂 A B p τ - τ • (A + B))‖ ≤
      (n : ℝ) *
      (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) +
       10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5 +
       10000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                   ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 5 +
       (6 : ℝ)⁻¹ * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
         (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
           (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
             10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) +
         2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
           (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
             10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) +
         2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
               10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
           (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
             10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))) := by
  -- ‖(n : 𝕂) • X‖ ≤ n · ‖X‖ via norm_smul_le + ‖n:𝕂‖ = n.
  have hn_norm : ‖((n : 𝕂) : 𝕂)‖ = n := by
    rw [RCLike.norm_natCast]
  have h_smul_bound : ‖(n : 𝕂) • (suzuki5_bch 𝕂 A B p τ - τ • (A + B))‖ ≤
      n * ‖suzuki5_bch 𝕂 A B p τ - τ • (A + B)‖ := by
    calc ‖(n : 𝕂) • (suzuki5_bch 𝕂 A B p τ - τ • (A + B))‖
        ≤ ‖((n : 𝕂) : 𝕂)‖ * ‖suzuki5_bch 𝕂 A B p τ - τ • (A + B)‖ := norm_smul_le _ _
      _ = n * ‖suzuki5_bch 𝕂 A B p τ - τ • (A + B)‖ := by rw [hn_norm]
  refine le_trans h_smul_bound ?_
  have h_m4b := norm_suzuki5_bch_sub_smul_le_of_IsSuzukiCubic (𝕂 := 𝕂) A B p τ
    hSuzuki hR hp h1m4p hreg hZ1 hZ2
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  gcongr

/-! ### Status note: M5 (clean quintic bound)

Under IsSuzukiCubic, M4b's sprawling bound is already O(|τ|⁵·(‖A‖+‖B‖)⁵):
- Per-block terms `σ_c⁵` are `O((|c·τ|·s)⁵) = O(|τ|⁵·s⁵)`.
- Outer symmetric term `(‖4X‖+‖Y‖)⁵` is `O(|τ|⁵·s⁵)` since `‖X‖ = O(|pτ|·s)`.
- Commutator term `(‖4X‖+‖Y‖)·‖[4X,Y]‖` is `O(|τ|·s)·O(|τ|⁴·s⁴) = O(|τ|⁵·s⁵)`.

Converting M4b's bound to a clean `K·|τ|⁵·s⁵` form requires tracking constants
through σ_c ≤ |c|·|τ|·s, ‖X‖ ≤ C·|pτ|·s (derivable from slice 4), and the
slice 9 commutator bound. This assembly is deferred to a subsequent session;
the existing M4b bound is sufficient for downstream Trotter h4 applications
by bounding each term individually.
-/
