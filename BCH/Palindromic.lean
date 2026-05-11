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
import BCH.SymmetricQuintic
import BCH.ChildsBasis
import Mathlib.Analysis.Complex.ExponentialBounds

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
/-- **Norm bound for a Strang block minus 1**:
`‖exp(½a)·exp(b)·exp(½a) - 1‖ ≤ exp(s) - 1` where `s = ‖a‖+‖b‖`.

Three-factor analog of `norm_exp_sub_one_le`. Used as foundation for the
T2-F discharge of `symmetric_bch_quintic_sub_poly_axiom` via the 3-factor
Strang tail bound. The crucial property: when `s < log 2`, we have
`exp(s) - 1 < 1`, so the log series for `log(strangBlock) = log(1 + (P-1))`
converges absolutely. -/
lemma norm_three_factor_exp_product_sub_one_le (a b : 𝔸) :
    ‖exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1‖ ≤
      Real.exp (‖a‖ + ‖b‖) - 1 := by
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
  have ha_half_le : ‖((2 : 𝕂)⁻¹ • a)‖ ≤ ‖a‖ / 2 := by
    calc ‖((2 : 𝕂)⁻¹ • a)‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  -- Build via norm_mul_exp_sub_one_le inductively.
  have h1 : ‖exp ((2 : 𝕂)⁻¹ • a) - 1‖ ≤
      Real.exp ‖((2 : 𝕂)⁻¹ • a)‖ - 1 := norm_exp_sub_one_le (𝕂 := 𝕂) _
  have h2 : ‖exp ((2 : 𝕂)⁻¹ • a) * exp b - 1‖ ≤
      Real.exp (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (norm_nonneg _) h1
  have h3 : ‖exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1‖ ≤
      Real.exp ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) - 1 :=
    norm_mul_exp_sub_one_le (𝕂 := 𝕂) _ _ (by positivity) h2
  -- Now bound the exponent: 2·‖½a‖ + ‖b‖ ≤ ‖a‖ + ‖b‖
  have hexp_bound :
      Real.exp ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) ≤
        Real.exp (‖a‖ + ‖b‖) := by
    apply Real.exp_le_exp.mpr
    calc (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖
        = 2 * ‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖ := by ring
      _ ≤ 2 * (‖a‖ / 2) + ‖b‖ := by linarith
      _ = ‖a‖ + ‖b‖ := by ring
  linarith

include 𝕂 in
/-- **Inductive step (deg-2 chain)**: if `‖y - 1 - z‖ ≤ exp(r) - 1 - r`
where `‖z‖ ≤ r` and `r ≥ 0`, then appending `exp(x)` on the right gives
`‖y · exp(x) - 1 - z - x‖ ≤ exp(r + ‖x‖) - 1 - (r + ‖x‖)`. Analog of
`norm_mul_exp_sub_one_le` at one degree higher. -/
lemma norm_mul_exp_sub_one_sub_le (y z x : 𝔸) {r : ℝ} (hr : 0 ≤ r)
    (hz_le : ‖z‖ ≤ r)
    (hy : ‖y - 1 - z‖ ≤ Real.exp r - 1 - r) :
    ‖y * exp x - 1 - z - x‖ ≤ Real.exp (r + ‖x‖) - 1 - (r + ‖x‖) := by
  letI : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hfactor : y * exp x - 1 - z - x =
      (y - 1 - z) * exp x + z * (exp x - 1) + (exp x - 1 - x) := by
    rw [sub_mul, sub_mul, one_mul]; noncomm_ring
  have hexp_x_nn : 0 ≤ Real.exp ‖x‖ := (Real.exp_pos _).le
  have hexp_norm : ‖exp x‖ ≤ Real.exp ‖x‖ := norm_exp_le (𝕂 := 𝕂) x
  have hexp_sub_norm : ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := norm_exp_sub_one_le (𝕂 := 𝕂) x
  have hexp_sub_sub_norm : ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ :=
    norm_exp_sub_one_sub_le (𝕂 := 𝕂) x
  have hexp_r_m1_nn : 0 ≤ Real.exp r - 1 - r := by
    have := Real.add_one_le_exp r
    have h2 := Real.quadratic_le_exp_of_nonneg hr
    nlinarith
  have hr_nn : (0 : ℝ) ≤ r := hr
  calc ‖y * exp x - 1 - z - x‖
      = ‖(y - 1 - z) * exp x + z * (exp x - 1) + (exp x - 1 - x)‖ := by rw [hfactor]
    _ ≤ ‖(y - 1 - z) * exp x + z * (exp x - 1)‖ + ‖exp x - 1 - x‖ := norm_add_le _ _
    _ ≤ ‖(y - 1 - z) * exp x‖ + ‖z * (exp x - 1)‖ + ‖exp x - 1 - x‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖y - 1 - z‖ * ‖exp x‖ + ‖z‖ * ‖exp x - 1‖ + ‖exp x - 1 - x‖ := by
        gcongr <;> exact norm_mul_le _ _
    _ ≤ (Real.exp r - 1 - r) * Real.exp ‖x‖ + r * (Real.exp ‖x‖ - 1) +
        (Real.exp ‖x‖ - 1 - ‖x‖) := by
        gcongr
    _ = Real.exp (r + ‖x‖) - 1 - (r + ‖x‖) := by rw [Real.exp_add]; ring

include 𝕂 in
/-- **T2-F7-aux**: bounds the deg-2+ part of `P − 1`:

  ‖exp(½a)·exp(b)·exp(½a) − 1 − (a+b)‖ ≤ exp(s) − 1 − s

where `s = ‖a‖+‖b‖`. The RHS is approximately `s²/2 + s³/6 + …`, so this
is an O(s²) bound capturing the deg-≥2 contributions of the Strang block.

Built via inductive chain `norm_mul_exp_sub_one_sub_le` analog of T2-F1's
`norm_mul_exp_sub_one_le`, applied twice through the 3-factor product. -/
lemma norm_three_factor_exp_product_sub_one_sub_add_le (a b : 𝔸) :
    ‖exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 - (a + b)‖ ≤
      Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) := by
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
  have ha_half_le : ‖((2 : 𝕂)⁻¹ • a)‖ ≤ ‖a‖ / 2 := by
    calc ‖((2 : 𝕂)⁻¹ • a)‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  -- Track ‖z₁‖ + ‖z₂‖ + ‖z₃‖ where z₁ = z₃ = ½a, z₂ = b. Bounded by ‖a‖ + ‖b‖.
  -- Step 1: y₁ = exp(z₁), bound ‖y₁ - 1 - z₁‖ ≤ exp(‖z₁‖) - 1 - ‖z₁‖.
  have h1 : ‖exp ((2 : 𝕂)⁻¹ • a) - 1 - ((2 : 𝕂)⁻¹ • a)‖ ≤
      Real.exp ‖((2 : 𝕂)⁻¹ • a)‖ - 1 - ‖((2 : 𝕂)⁻¹ • a)‖ :=
    norm_exp_sub_one_sub_le (𝕂 := 𝕂) _
  -- Step 2: extend with exp(b).
  have h2 : ‖exp ((2 : 𝕂)⁻¹ • a) * exp b - 1 - ((2 : 𝕂)⁻¹ • a) - b‖ ≤
      Real.exp (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) - 1 -
        (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) :=
    norm_mul_exp_sub_one_sub_le (𝕂 := 𝕂) _ _ _ (norm_nonneg _) (le_refl _) h1
  -- Need to rewrite h2 to expose z = (½a) + b as a single term.
  have h2' : ‖exp ((2 : 𝕂)⁻¹ • a) * exp b - 1 - (((2 : 𝕂)⁻¹ • a) + b)‖ ≤
      Real.exp (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) - 1 -
        (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) := by
    have heq : exp ((2 : 𝕂)⁻¹ • a) * exp b - 1 - (((2 : 𝕂)⁻¹ • a) + b) =
        exp ((2 : 𝕂)⁻¹ • a) * exp b - 1 - ((2 : 𝕂)⁻¹ • a) - b := by abel
    rw [heq]; exact h2
  -- Step 3: extend with exp(½a) again.
  have h_z_le : ‖((2 : 𝕂)⁻¹ • a) + b‖ ≤ ‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖ := norm_add_le _ _
  have h3 : ‖exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) -
                1 - (((2 : 𝕂)⁻¹ • a) + b) - ((2 : 𝕂)⁻¹ • a)‖ ≤
      Real.exp ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) - 1 -
        ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) :=
    norm_mul_exp_sub_one_sub_le (𝕂 := 𝕂)
      (exp ((2 : 𝕂)⁻¹ • a) * exp b) (((2 : 𝕂)⁻¹ • a) + b) ((2 : 𝕂)⁻¹ • a)
      (by positivity) h_z_le h2'
  -- The accumulator is: (½•a) + b + (½•a) = a + b (algebraic identity).
  have h_acc_eq : ((2 : 𝕂)⁻¹ • a) + b + ((2 : 𝕂)⁻¹ • a) = a + b := by
    rw [show ((2 : 𝕂)⁻¹ • a) + b + ((2 : 𝕂)⁻¹ • a) = ((2 : 𝕂)⁻¹ + (2 : 𝕂)⁻¹) • a + b from by
      simp [add_smul]; abel,
        show ((2 : 𝕂)⁻¹ + (2 : 𝕂)⁻¹) = (1 : 𝕂) from by ring,
        one_smul]
  -- Rewrite h3's LHS to match (a + b) form.
  have h3' : ‖exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 - (a + b)‖ ≤
      Real.exp ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) - 1 -
        ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) := by
    have heq : exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 - (a + b) =
        exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) -
          1 - (((2 : 𝕂)⁻¹ • a) + b) - ((2 : 𝕂)⁻¹ • a) := by
      rw [← h_acc_eq]; abel
    rw [heq]; exact h3
  -- Bound the exponent: 2·‖½a‖ + ‖b‖ ≤ ‖a‖ + ‖b‖.
  have h_arg_le : (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖ ≤ ‖a‖ + ‖b‖ := by
    calc (‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖
        = 2 * ‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖ := by ring
      _ ≤ 2 * (‖a‖ / 2) + ‖b‖ := by linarith
      _ = ‖a‖ + ‖b‖ := by ring
  -- exp(t) - 1 - t is monotonic in t ≥ 0.
  have hf_mono : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ →
      Real.exp t₁ - 1 - t₁ ≤ Real.exp t₂ - 1 - t₂ := by
    intro t₁ t₂ ht₁ ht₁₂
    have h1 : Real.exp t₁ ≥ 1 := Real.one_le_exp ht₁
    have h2 : Real.exp (t₂ - t₁) ≥ (t₂ - t₁) + 1 := Real.add_one_le_exp _
    have h3 : Real.exp t₂ = Real.exp t₁ * Real.exp (t₂ - t₁) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [Real.exp_pos t₁, Real.exp_pos (t₂ - t₁)]
  have h_mono : Real.exp ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) - 1 -
      ((‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖) + ‖((2 : 𝕂)⁻¹ • a)‖) ≤
        Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) :=
    hf_mono _ _ (by positivity) h_arg_le
  linarith

include 𝕂 in
/-- **Strict bound**: when `‖a‖ + ‖b‖ < log 2`, the 3-factor exp product
satisfies `‖P − 1‖ < 1`. Direct from T2-F1 + `exp(log 2) = 2`. Used to
ensure absolute convergence of `log(P) = log(1 + (P−1))` series. -/
lemma norm_three_factor_exp_product_sub_one_lt_one (a b : 𝔸)
    (h : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1‖ < 1 := by
  have hbound := norm_three_factor_exp_product_sub_one_le (𝕂 := 𝕂) a b
  have hexp_lt : Real.exp (‖a‖ + ‖b‖) < 2 := by
    calc Real.exp (‖a‖ + ‖b‖) < Real.exp (Real.log 2) := Real.exp_strictMono h
      _ = 2 := Real.exp_log (by norm_num)
  linarith

include 𝕂 in
/-- **Tail bound**: for `‖a‖+‖b‖ < log 2`, the deg-7+ tail of
`logOnePlus(strangBlock - 1)` is bounded by `(exp(s)-1)⁷ / (2 - exp(s))`
where `s = ‖a‖+‖b‖`.

Direct application of `norm_logOnePlus_sub_sub_sub_sub_sub_sub_le` to
`y = exp(½a)·exp(b)·exp(½a) - 1` (which has `‖y‖ ≤ exp(s) - 1 < 1`).
The denominator `1 - ‖y‖ ≥ 2 - exp(s) > 0`. -/
lemma norm_logOnePlus_strangBlock_sub_through_deg_6_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    let y := exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1
    ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
        (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 + (6 : 𝕂)⁻¹ • y ^ 6‖ ≤
      (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  intro y
  have hy_lt : ‖y‖ < 1 := norm_three_factor_exp_product_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp (‖a‖ + ‖b‖) - 1 :=
    norm_three_factor_exp_product_sub_one_le (𝕂 := 𝕂) a b
  have hexp_lt : Real.exp (‖a‖ + ‖b‖) < 2 := by
    calc Real.exp (‖a‖ + ‖b‖) < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom_y : 0 < 1 - ‖y‖ := by linarith
  have hdenom_s : 0 < 2 - Real.exp (‖a‖ + ‖b‖) := by linarith
  have htail := norm_logOnePlus_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) y hy_lt
  -- htail : ‖...‖ ≤ ‖y‖^7 / (1 - ‖y‖)
  -- We want: ≤ (exp(s)-1)^7 / (2 - exp(s))
  have hy7_le : ‖y‖ ^ 7 ≤ (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 :=
    pow_le_pow_left₀ (norm_nonneg _) hy_le 7
  have h_denom_le : 2 - Real.exp (‖a‖ + ‖b‖) ≤ 1 - ‖y‖ := by
    have : ‖y‖ ≤ Real.exp (‖a‖ + ‖b‖) - 1 := hy_le
    linarith
  -- Apply: (a/b ≤ a'/b' when a ≤ a', 0 < b ≤ b')
  calc ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
        (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 + (6 : 𝕂)⁻¹ • y ^ 6‖
      ≤ ‖y‖ ^ 7 / (1 - ‖y‖) := htail
    _ ≤ (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
        apply div_le_div₀
        · exact pow_nonneg (by linarith [norm_nonneg y, hy_le]) 7
        · exact hy7_le
        · exact hdenom_s
        · exact h_denom_le

include 𝕂 in
/-- **T2-F7 preliminary bound** (loose, O(s²)):

  ‖polynomial_in_y − (a+b)‖ ≤ (exp(s) − 1 − s) + Σₖ₌₂⁶ (exp(s) − 1)ᵏ / k

where polynomial_in_y = y − y²/2 + y³/3 − y⁴/4 + y⁵/5 − y⁶/6.

Coarse O(s²) bound on the deg-2+ residual after subtracting (a+b). Sets
up the framework for finer T2-F7 work where we identify the deg-3 and
deg-5 contributions as sym_E₃ and sym_E₅ to refine to O(s⁷). -/
lemma norm_polynomial_in_y_sub_add_le (a b : 𝔸) :
    ‖((exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) -
        (2 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 2 +
        (3 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 3 -
        (4 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 4 +
        (5 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 5 -
        (6 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 6) -
        (a + b)‖ ≤
      (Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖)) +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 2 / 2 +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 3 / 3 +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 4 / 4 +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 5 / 5 +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 6 / 6 := by
  set y := exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  have hy_le : ‖y‖ ≤ Real.exp s - 1 :=
    norm_three_factor_exp_product_sub_one_le (𝕂 := 𝕂) a b
  have hy_aux : ‖y - (a + b)‖ ≤ Real.exp s - 1 - s :=
    norm_three_factor_exp_product_sub_one_sub_add_le (𝕂 := 𝕂) a b
  have hs_nn : 0 ≤ s := by rw [hs_def]; positivity
  have hexp_m1_nn : 0 ≤ Real.exp s - 1 := by
    have := Real.add_one_le_exp s; linarith
  -- Per-term bounds: ‖(k:𝕂)⁻¹ • y^k‖ ≤ ‖y‖^k / k for k ≥ 1.
  have h_norm_inv : ∀ (k : ℕ), 0 < k → ‖((k : 𝕂)⁻¹ : 𝕂)‖ = (k : ℝ)⁻¹ := by
    intro k hk
    rw [norm_inv]
    congr 1
    rw [show ((k : 𝕂) : 𝕂) = ((k : ℕ) : 𝕂) from rfl, RCLike.norm_natCast]
  have h_smul_pow_le : ∀ (k : ℕ), 0 < k →
      ‖((k : 𝕂)⁻¹ • y ^ k)‖ ≤ ‖y‖ ^ k / k := by
    intro k hk
    have hpow := norm_pow_le' y hk
    calc ‖((k : 𝕂)⁻¹ • y ^ k)‖ ≤ ‖((k : 𝕂)⁻¹ : 𝕂)‖ * ‖y ^ k‖ := norm_smul_le _ _
      _ = (k : ℝ)⁻¹ * ‖y ^ k‖ := by rw [h_norm_inv k hk]
      _ ≤ (k : ℝ)⁻¹ * ‖y‖ ^ k := by
          apply mul_le_mul_of_nonneg_left hpow
          positivity
      _ = ‖y‖ ^ k / k := by field_simp
  have h2 : ‖((2 : 𝕂)⁻¹ • y ^ 2)‖ ≤ ‖y‖ ^ 2 / 2 := h_smul_pow_le 2 (by norm_num)
  have h3 : ‖((3 : 𝕂)⁻¹ • y ^ 3)‖ ≤ ‖y‖ ^ 3 / 3 := h_smul_pow_le 3 (by norm_num)
  have h4 : ‖((4 : 𝕂)⁻¹ • y ^ 4)‖ ≤ ‖y‖ ^ 4 / 4 := h_smul_pow_le 4 (by norm_num)
  have h5 : ‖((5 : 𝕂)⁻¹ • y ^ 5)‖ ≤ ‖y‖ ^ 5 / 5 := h_smul_pow_le 5 (by norm_num)
  have h6 : ‖((6 : 𝕂)⁻¹ • y ^ 6)‖ ≤ ‖y‖ ^ 6 / 6 := h_smul_pow_le 6 (by norm_num)
  -- Triangle inequality: bound the sum.
  have hpoly_eq : (y - (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 +
      (5 : 𝕂)⁻¹ • y ^ 5 - (6 : 𝕂)⁻¹ • y ^ 6) - (a + b) =
      (y - (a + b)) + (-((2 : 𝕂)⁻¹ • y ^ 2)) + ((3 : 𝕂)⁻¹ • y ^ 3) +
        (-((4 : 𝕂)⁻¹ • y ^ 4)) + ((5 : 𝕂)⁻¹ • y ^ 5) + (-((6 : 𝕂)⁻¹ • y ^ 6)) := by abel
  rw [hpoly_eq]
  -- Bound each piece via the per-term bounds + monotonicity (‖y‖^k ≤ (exp(s)-1)^k).
  have hy2 : ‖((2 : 𝕂)⁻¹ • y ^ 2)‖ ≤ (Real.exp s - 1) ^ 2 / 2 := by
    apply h2.trans; gcongr
  have hy3 : ‖((3 : 𝕂)⁻¹ • y ^ 3)‖ ≤ (Real.exp s - 1) ^ 3 / 3 := by
    apply h3.trans; gcongr
  have hy4 : ‖((4 : 𝕂)⁻¹ • y ^ 4)‖ ≤ (Real.exp s - 1) ^ 4 / 4 := by
    apply h4.trans; gcongr
  have hy5 : ‖((5 : 𝕂)⁻¹ • y ^ 5)‖ ≤ (Real.exp s - 1) ^ 5 / 5 := by
    apply h5.trans; gcongr
  have hy6 : ‖((6 : 𝕂)⁻¹ • y ^ 6)‖ ≤ (Real.exp s - 1) ^ 6 / 6 := by
    apply h6.trans; gcongr
  -- Triangle inequality on the 6-term sum: chain norm_add_le manually.
  set A := y - (a + b)
  set B := -((2 : 𝕂)⁻¹ • y ^ 2)
  set C := (3 : 𝕂)⁻¹ • y ^ 3
  set D := -((4 : 𝕂)⁻¹ • y ^ 4)
  set E := (5 : 𝕂)⁻¹ • y ^ 5
  set F := -((6 : 𝕂)⁻¹ • y ^ 6)
  have hAB := norm_add_le A B
  have hABC := norm_add_le (A + B) C
  have hABCD := norm_add_le (A + B + C) D
  have hABCDE := norm_add_le (A + B + C + D) E
  have hABCDEF := norm_add_le (A + B + C + D + E) F
  have hB_eq : ‖B‖ = ‖((2 : 𝕂)⁻¹ • y ^ 2)‖ := norm_neg _
  have hD_eq : ‖D‖ = ‖((4 : 𝕂)⁻¹ • y ^ 4)‖ := norm_neg _
  have hF_eq : ‖F‖ = ‖((6 : 𝕂)⁻¹ • y ^ 6)‖ := norm_neg _
  linarith

include 𝕂 in
/-- **Bridge: 3-factor BCH composition equals `logOnePlus` of the product − 1**.

For `‖a‖ + ‖b‖ < 1/4` (so the inner BCH `bch(½a, b)` converges):

    bch(bch(½a, b), ½a) = logOnePlus(exp(½a) · exp(b) · exp(½a) − 1)

This is the foundational identity for T2-F: it lets us bound the deg-7+ tail
of `bch(bch(½a, b), ½a)` directly via the log series, avoiding the per-piece
sextic decomposition (which gives O(s⁶) per piece, insufficient for O(s⁷)).

Proof: unfold the outer `bch`, then apply `exp_bch` for the inner BCH to
rewrite `exp(bch(½a, b))` as `exp(½a) · exp(b)`. -/
lemma bch_bch_half_eq_logOnePlus_strangBlock_sub_one (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) =
      logOnePlus (𝕂 := 𝕂)
        (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) := by
  -- Setup: the inner BCH converges since ‖½a‖ + ‖b‖ < log 2.
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
  have ha_half_le : ‖((2 : 𝕂)⁻¹ • a)‖ ≤ ‖a‖ / 2 := by
    calc ‖((2 : 𝕂)⁻¹ • a)‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  have hln2_quarter : (1 : ℝ) / 4 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hs₁_lt : ‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖ < Real.log 2 := by
    calc ‖((2 : 𝕂)⁻¹ • a)‖ + ‖b‖ ≤ ‖a‖ / 2 + ‖b‖ := by linarith
      _ ≤ ‖a‖ + ‖b‖ := by linarith [norm_nonneg a]
      _ < 1 / 4 := hab
      _ < Real.log 2 := hln2_quarter
  -- Unfold outer bch, apply exp_bch on inner.
  unfold bch
  congr 1
  rw [show exp (logOnePlus (𝕂 := 𝕂) (exp ((2 : 𝕂)⁻¹ • a) * exp b - 1)) =
        exp ((2 : 𝕂)⁻¹ • a) * exp b from by
    have := exp_bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b hs₁_lt
    unfold bch at this; exact this]

include 𝕂 in
/-- **Combined T2-F framework bound** (T2-F6): bounds the difference between
`symmetric_bch_cubic(a, b)` and the polynomial-in-`y` expansion truncated
at degree 6:

  ‖symmetric_bch_cubic(a, b) − (y − y²/2 + y³/3 − y⁴/4 + y⁵/5 − y⁶/6) + (a+b)‖ ≤ tail

where y = exp(½a)·exp(b)·exp(½a) − 1 and tail = (exp(s)−1)⁷/(2−exp(s)).

Combines T2-F4 (bch composition equals logOnePlus(P-1)) with T2-F5
(deg-7 tail bound on logOnePlus). The remaining gap to the parent bound
`‖sym_bch_cubic − sym_E₃ − sym_E₅‖ ≤ K·s⁷` is the algebraic identity:

  trunc_to_deg_6(y − y²/2 + ... − y⁶/6) = (a+b) + sym_E₃ + sym_E₅
  (deg 2, 4, 6 vanish palindromically — CAS-verified)

This identity is T2-F7 and remains pending. -/
lemma symmetric_bch_cubic_sub_polynomial_in_y_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 a b -
        ((exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1)
         - (2 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 2
         + (3 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 3
         - (4 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 4
         + (5 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 5
         - (6 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 6)
       + (a + b)‖ ≤
      (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set y := exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 with hy_def
  have hln2_quarter : (1 : ℝ) / 4 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hab_log2 : ‖a‖ + ‖b‖ < Real.log 2 := lt_trans hab hln2_quarter
  have hbridge := bch_bch_half_eq_logOnePlus_strangBlock_sub_one (𝕂 := 𝕂) a b hab
  have htail := norm_logOnePlus_strangBlock_sub_through_deg_6_le (𝕂 := 𝕂) a b hab_log2
  unfold symmetric_bch_cubic
  rw [hbridge]
  -- LHS = (logOnePlus y - (a+b)) - (y - y²/2 + ... - y⁶/6) + (a+b)
  --     = logOnePlus y - y + y²/2 - y³/3 + y⁴/4 - y⁵/5 + y⁶/6
  have heq : logOnePlus (𝕂 := 𝕂) y - (a + b) -
        (y - (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 +
         (5 : 𝕂)⁻¹ • y ^ 5 - (6 : 𝕂)⁻¹ • y ^ 6) + (a + b) =
      logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
        (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 + (6 : 𝕂)⁻¹ • y ^ 6 := by
    abel
  rw [heq]
  exact htail

include 𝕂 in
/-- **T2-F7-prelim2** (deg-4+ residual): combines T2-F6 (framework) with the
existing cubic template `norm_symmetric_bch_cubic_sub_poly_le` to bound:

  ‖polynomial_in_y(y) − (a+b) − sym_E₃‖ ≤ 10⁷ · s⁵ + (exp(s)−1)⁷ / (2−exp(s))

where polynomial_in_y(y) = y − y²/2 + y³/3 − y⁴/4 + y⁵/5 − y⁶/6 and
y = exp(½a)·exp(b)·exp(½a) − 1. The first term is the cubic template's
O(s⁵) bound; the second is the deg-7+ logOnePlus tail (O(s⁷) for s ≤ 1/4).

Tighter than T2-F7-prelim (O(s²)). One degree closer to T2's target O(s⁷).
Final step requires identifying the deg-5 contribution as sym_E₅ (T2-F7e). -/
lemma norm_polynomial_in_y_sub_add_sub_E3_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖((exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) -
        (2 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 2 +
        (3 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 3 -
        (4 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 4 +
        (5 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 5 -
        (6 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 6) -
        (a + b) - symmetric_bch_cubic_poly 𝕂 a b‖ ≤
      10000000 * (‖a‖ + ‖b‖) ^ 5 +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  have h_cubic := norm_symmetric_bch_cubic_sub_poly_le (𝕂 := 𝕂) a b hab
  have h_framework := symmetric_bch_cubic_sub_polynomial_in_y_le (𝕂 := 𝕂) a b hab
  set s := ‖a‖ + ‖b‖ with hs_def
  set y := exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 with hy_def
  set poly_in_y := y - (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 +
      (5 : 𝕂)⁻¹ • y ^ 5 - (6 : 𝕂)⁻¹ • y ^ 6 with hpoly_def
  -- Triangle: poly_in_y - (a+b) - sym_E₃ = (sym_bch_cubic - sym_E₃) - (sym_bch_cubic - poly_in_y + (a+b))
  have h_diff : poly_in_y - (a + b) - symmetric_bch_cubic_poly 𝕂 a b =
      (symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b) -
        (symmetric_bch_cubic 𝕂 a b - poly_in_y + (a + b)) := by abel
  rw [h_diff]
  refine (norm_sub_le _ _).trans ?_
  linarith

include 𝕂 in
/-- **T2-F7g-coarse**: a coarser O(s⁵) version of the final T2-F7 target.
Provable using existing infrastructure (NO algebraic deg-5 identification
required). Useful as a stepping stone:

  ‖polynomial_in_y(y) − (a+b) − sym_E₃ − sym_E₅‖ ≤
    (10⁷ + 1) · s⁵ + (exp(s)−1)⁷ / (2 − exp(s))

where polynomial_in_y(y) = y − y²/2 + y³/3 − y⁴/4 + y⁵/5 − y⁶/6,
y = exp(½a)·exp(b)·exp(½a) − 1, s = ‖a‖+‖b‖.

Combines T2-F7-prelim2 (gives 10⁷·s⁵ + tail) with `norm_symmetric_bch_quintic_poly_le`
(gives ‖sym_E₅‖ ≤ s⁵) via triangle inequality. Subtracting sym_E₅ from the
prelim2 bound costs at most ‖sym_E₅‖ ≤ s⁵ on the RHS.

Final O(s⁷) target requires the deg-5 algebraic identification (T2-F7e),
which is the only remaining mathematical bottleneck for parent-axiom discharge. -/
lemma norm_polynomial_in_y_sub_add_sub_E3_sub_E5_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖((exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) -
        (2 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 2 +
        (3 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 3 -
        (4 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 4 +
        (5 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 5 -
        (6 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 6) -
        (a + b) - symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_quintic_poly 𝕂 a b‖ ≤
      (10000000 + 1) * (‖a‖ + ‖b‖) ^ 5 +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  have h_prelim2 := norm_polynomial_in_y_sub_add_sub_E3_le (𝕂 := 𝕂) a b hab
  have h_E5 := norm_symmetric_bch_quintic_poly_le (𝕂 := 𝕂) a b
  -- Apply triangle inequality: the goal is ‖X - sym_E₅‖ where X = poly_in_y - (a+b) - sym_E₃.
  exact (norm_sub_le _ _).trans (by linarith)

include 𝕂 in
/-- **T2-F7g-tight** (consequence of parent axiom): the O(s⁷) version of
T2-F7g, derivable from `norm_symmetric_bch_quintic_sub_poly_le` (which
currently uses the parent Tier-2 axiom) + T2-F6 framework via triangle
inequality.

  ‖polynomial_in_y(y) − (a+b) − sym_E₃ − sym_E₅‖ ≤
    10⁹ · s⁷ + (exp(s)−1)⁷ / (2 − exp(s))

This shows T2-F7g is EQUIVALENT to the parent (modulo a small tail term).
The "→" direction (parent ⟹ T2-F7g): proved here.
The "←" direction (T2-F7g ⟹ parent): would discharge the parent — requires
T2-F7e (algebraic deg-5 identification) to actually prove T2-F7g
independently of the parent. -/
lemma norm_polynomial_in_y_sub_add_sub_E3_sub_E5_via_parent (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖((exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) -
        (2 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 2 +
        (3 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 3 -
        (4 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 4 +
        (5 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 5 -
        (6 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 6) -
        (a + b) - symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_quintic_poly 𝕂 a b‖ ≤
      20000000000 * (‖a‖ + ‖b‖) ^ 7 +
        (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  -- Use the parent (currently axiom-derived): ‖sym_bch_cubic - sym_E₃ - sym_E₅‖ ≤ 10⁹·s⁷.
  have h_parent := norm_symmetric_bch_quintic_sub_poly_le (𝕂 := 𝕂) a b hab
  have h_framework := symmetric_bch_cubic_sub_polynomial_in_y_le (𝕂 := 𝕂) a b hab
  set y := exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 with hy_def
  set poly_in_y := y - (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 +
      (5 : 𝕂)⁻¹ • y ^ 5 - (6 : 𝕂)⁻¹ • y ^ 6 with hpoly_def
  -- poly_in_y - (a+b) - sym_E₃ - sym_E₅ =
  --   (sym_bch_cubic - sym_E₃ - sym_E₅) - (sym_bch_cubic - poly_in_y + (a+b))
  have h_diff : poly_in_y - (a + b) - symmetric_bch_cubic_poly 𝕂 a b -
        symmetric_bch_quintic_poly 𝕂 a b =
      (symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b -
        symmetric_bch_quintic_poly 𝕂 a b) -
        (symmetric_bch_cubic 𝕂 a b - poly_in_y + (a + b)) := by abel
  rw [h_diff]
  exact (norm_sub_le _ _).trans (by linarith)

include 𝕂 in
/-- **T2-F equivalence (reverse direction)**: any sufficiently tight bound
on `‖polynomial_in_y - (a+b) - sym_E₃ - sym_E₅‖` of the form `K · s⁷`
implies the parent Tier-2 bound `‖sym_bch_cubic - sym_E₃ - sym_E₅‖ ≤ (K+K')·s⁷`
where K' bounds the deg-7+ tail.

This is the converse of T2-F7g-tight. Together they show:

  T2-F7g  ⟺  parent Tier-2 axiom

This documents the structural equivalence: the T2-F framework (T2-F1-F6)
has reduced the parent axiom to T2-F7g, an equivalent inequality. Since
T2-F7g is a more "concrete" statement (directly about a polynomial in y),
it's a more tractable target for future work via T2-F7e (algebraic deg-5
identification).

For practical use: pass any user-provided T2-F7g witness to derive the
parent. Currently, T2-F7g is itself unproved (modulo the alt-form axiom);
T2-F7e is the sole missing piece. -/
lemma symmetric_bch_quintic_sub_poly_le_via_T2F7g (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) {K : ℝ}
    (h_T2F7g : ‖((exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) -
        (2 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 2 +
        (3 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 3 -
        (4 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 4 +
        (5 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 5 -
        (6 : 𝕂)⁻¹ • (exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1) ^ 6) -
        (a + b) - symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_quintic_poly 𝕂 a b‖ ≤ K) :
    ‖symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b -
        symmetric_bch_quintic_poly 𝕂 a b‖ ≤
      K + (Real.exp (‖a‖ + ‖b‖) - 1) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  have h_framework := symmetric_bch_cubic_sub_polynomial_in_y_le (𝕂 := 𝕂) a b hab
  set y := exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) - 1 with hy_def
  set poly_in_y := y - (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 +
      (5 : 𝕂)⁻¹ • y ^ 5 - (6 : 𝕂)⁻¹ • y ^ 6 with hpoly_def
  -- sym_bch_cubic - sym_E₃ - sym_E₅ =
  --   (poly_in_y - (a+b) - sym_E₃ - sym_E₅) + (sym_bch_cubic - poly_in_y + (a+b))
  have h_diff : symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b -
        symmetric_bch_quintic_poly 𝕂 a b =
      (poly_in_y - (a + b) - symmetric_bch_cubic_poly 𝕂 a b -
        symmetric_bch_quintic_poly 𝕂 a b) +
        (symmetric_bch_cubic 𝕂 a b - poly_in_y + (a + b)) := by abel
  rw [h_diff]
  exact (norm_add_le _ _).trans (by linarith)

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

/-! ### Quintic-order refinement of the per-block bound (B1.d)

Extends `norm_strangBlock_log_sub_target_le` (cubic polynomial subtraction with
`O(σ⁵)` residual) by one higher degree: after subtracting both the cubic
polynomial `(cτ)³•symmetric_bch_cubic_poly` and the quintic polynomial
`(cτ)⁵•symmetric_bch_quintic_poly`, the residual is `O(σ⁷)`.

Reduction: apply `norm_symmetric_bch_quintic_sub_poly_le` to `(a, b) = (cτ•A, cτ•B)`,
then use the `c⁵` / `c³` homogeneity lemmas for the two polynomials to pull the
`(cτ)³` / `(cτ)⁵` scalars outside.

This is the building block for the symbolic 5-factor composition in
`Suzuki5Quintic.lean` (B2): summing over the 5 Strang blocks gives the τ⁵
residual in Childs 4-fold basis.
-/

include 𝕂 in
/-- **Per-block quintic bound (B1.d)**: each Strang block's log differs from the
extended target `cτ•V + (cτ)³•E_sym + (cτ)⁵•E₅_sym` by at most `K·σ⁷` where
`σ = ‖cτ•A‖+‖cτ•B‖`. Direct application of
`norm_symmetric_bch_quintic_sub_poly_le` to the Strang composition `cτ•A, cτ•B`,
then pulling `(cτ)³` and `(cτ)⁵` through via `symmetric_bch_cubic_poly_smul` and
`symmetric_bch_quintic_poly_smul`. -/
theorem norm_strangBlock_log_sub_quintic_target_le (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4) :
    ‖strangBlock_log 𝕂 A B c τ - (c * τ) • (A + B)
        - (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B
        - (c * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B‖ ≤
      20000000000 * (‖(c * τ) • A‖ + ‖(c * τ) • B‖) ^ 7 := by
  unfold strangBlock_log
  -- Apply `norm_symmetric_bch_quintic_sub_poly_le` with a = cτ•A, b = cτ•B.
  have key := norm_symmetric_bch_quintic_sub_poly_le
    (𝕂 := 𝕂) ((c * τ) • A) ((c * τ) • B) h
  unfold symmetric_bch_cubic at key
  -- Regroup (cτA+cτB) as cτ•(A+B), factor (cτ)³ / (cτ)⁵ scalars outside.
  have hsmul_dist : (c * τ) • A + (c * τ) • B = (c * τ) • (A + B) := by rw [smul_add]
  have hcub_hom : symmetric_bch_cubic_poly 𝕂 ((c * τ) • A) ((c * τ) • B) =
      (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B :=
    symmetric_bch_cubic_poly_smul A B (c * τ)
  have hquint_hom : symmetric_bch_quintic_poly 𝕂 ((c * τ) • A) ((c * τ) • B) =
      (c * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B :=
    symmetric_bch_quintic_poly_smul A B (c * τ)
  rw [hsmul_dist, hcub_hom, hquint_hom] at key
  -- Match the goal: `key` already matches after the rewrites above.
  exact key

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
    simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
      mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
    match_scalars <;> ring
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

/-! ### B2.2.d — Lipschitz bound for `symmetric_bch_cubic_poly` on (α•V + δa, β•V + δb)

Analog of `norm_symmetric_bch_quintic_poly_apply_smul_add_smul_add_le` (B2.2.c)
for the cubic polynomial. The bound is `O(N²·(‖δa‖+‖δb‖) + N·(‖δa‖+‖δb‖)²)` rather
than the trivial `(‖α•V+δa‖+‖β•V+δb‖)³ = O(N³)`.

Proof: combine `norm_commutator_near_V_le` (slice 8) — which gives
`‖[fA, fB]‖ ≤ 2·N·D + 2·D²` from the structural cancellation `[α•V, β•V] = 0` —
with `norm_symmetric_bch_cubic_poly_le_commutator` —
`‖sym_cubic_poly(a, b)‖ ≤ (1/6)·(‖a‖+‖b‖)·‖a*b - b*a‖`. The product gives:

  `‖sym_cubic_poly(fA, fB)‖ ≤ (1/6)·2N·(2N·D + 2·D²) = (2/3)·(N²·D + N·D²)`.

For Suzuki τ⁵ identification: `N = O(τ)`, `D = O(τ³)`, so the bound is
`O(τ²·τ³ + τ·τ⁶) = O(τ⁵)` — matching the τ⁵ leading order. -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
theorem norm_symmetric_bch_cubic_poly_apply_smul_add_smul_add_le
    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) (N : ℝ)
    (hα_le : ‖α • V‖ ≤ N) (hβ_le : ‖β • V‖ ≤ N)
    (hα_δa_le : ‖α • V + δa‖ ≤ N) (hβ_δb_le : ‖β • V + δb‖ ≤ N)
    (hN_nn : 0 ≤ N) :
    ‖symmetric_bch_cubic_poly 𝕂 (α • V + δa) (β • V + δb)‖ ≤
      (2 / 3) * (N ^ 2 * (‖δa‖ + ‖δb‖) + N * (‖δa‖ + ‖δb‖) ^ 2) := by
  set fA := α • V + δa with hfA_def
  set fB := β • V + δb with hfB_def
  set D := ‖δa‖ + ‖δb‖ with hD_def
  have hD_nn : 0 ≤ D := by rw [hD_def]; positivity
  have hda_nn : 0 ≤ ‖δa‖ := norm_nonneg _
  have hdb_nn : 0 ≤ ‖δb‖ := norm_nonneg _
  have hda_eq : ‖fA - α • V‖ = ‖δa‖ := by rw [hfA_def]; congr 1; abel
  have hdb_eq : ‖fB - β • V‖ = ‖δb‖ := by rw [hfB_def]; congr 1; abel
  have hda_le_D : ‖δa‖ ≤ D := by rw [hD_def]; linarith
  have hdb_le_D : ‖δb‖ ≤ D := by rw [hD_def]; linarith
  -- ‖[fA, fB]‖ ≤ 2·N·D + 2·D² via norm_commutator_near_V_le.
  have hcomm_bnd := norm_commutator_near_V_le (𝕂 := 𝕂) V fA fB α β
  rw [hda_eq, hdb_eq] at hcomm_bnd
  have hbracket : ‖fA * fB - fB * fA‖ ≤ 2 * N * D + 2 * D ^ 2 := by
    have h1 : 2 * ‖α • V‖ * ‖δb‖ ≤ 2 * N * ‖δb‖ := by gcongr
    have h2 : 2 * ‖β • V‖ * ‖δa‖ ≤ 2 * N * ‖δa‖ := by gcongr
    have h3 : 2 * ‖δa‖ * ‖δb‖ ≤ 2 * D * D := by
      have := mul_le_mul hda_le_D hdb_le_D hdb_nn hD_nn
      linarith
    calc ‖fA * fB - fB * fA‖
        ≤ 2 * ‖α • V‖ * ‖δb‖ + 2 * ‖β • V‖ * ‖δa‖ + 2 * ‖δa‖ * ‖δb‖ := hcomm_bnd
      _ ≤ 2 * N * ‖δb‖ + 2 * N * ‖δa‖ + 2 * D * D := by linarith
      _ = 2 * N * (‖δa‖ + ‖δb‖) + 2 * D ^ 2 := by ring
      _ = 2 * N * D + 2 * D ^ 2 := by rw [hD_def]
  -- Apply norm_symmetric_bch_cubic_poly_le_commutator: ‖sym_cubic_poly(fA, fB)‖
  --   ≤ (1/6) · (‖fA‖ + ‖fB‖) · ‖fA*fB - fB*fA‖.
  have hcubic := norm_symmetric_bch_cubic_poly_le_commutator (𝕂 := 𝕂) fA fB
  have hsum : ‖fA‖ + ‖fB‖ ≤ 2 * N := by linarith
  have hsum_nn : 0 ≤ ‖fA‖ + ‖fB‖ := by positivity
  have hbracket_nn : 0 ≤ ‖fA * fB - fB * fA‖ := norm_nonneg _
  have h6inv_nn : (0 : ℝ) ≤ (6 : ℝ)⁻¹ := by norm_num
  have hRHS_nn : 0 ≤ 2 * N * D + 2 * D ^ 2 := by positivity
  calc ‖symmetric_bch_cubic_poly 𝕂 fA fB‖
      ≤ (6 : ℝ)⁻¹ * (‖fA‖ + ‖fB‖) * ‖fA * fB - fB * fA‖ := hcubic
    _ ≤ (6 : ℝ)⁻¹ * (2 * N) * (2 * N * D + 2 * D ^ 2) := by
        have hcoef_nn : 0 ≤ (6 : ℝ)⁻¹ * (‖fA‖ + ‖fB‖) := mul_nonneg h6inv_nn hsum_nn
        have hcoef_le : (6 : ℝ)⁻¹ * (‖fA‖ + ‖fB‖) ≤ (6 : ℝ)⁻¹ * (2 * N) :=
          mul_le_mul_of_nonneg_left hsum h6inv_nn
        exact mul_le_mul hcoef_le hbracket hbracket_nn
                (mul_nonneg h6inv_nn (by linarith))
    _ = (2 / 3) * (N ^ 2 * D + N * D ^ 2) := by ring

/-! ### B2.2.e foundation — linear-in-residual part of `sym_cubic_poly` on (α•V+δa, β•V+δb)

By multilinear expansion of `sym_cubic_poly = -(1/24)·[a,[a,b]] + (1/12)·[b,[b,a]]`
at `a = α•V + δa, b = β•V + δb`, the polynomial decomposes by δ-degree as

  `sym_cubic_poly = 0 (δ⁰, vanishing per B2.2.b) + L (δ¹) + Q (δ²) + C (δ³)`

The **linear part L** has the closed form (verified by CAS at
`/tmp/verify_linear_part.py`):

  `L = ((α+2β)/24) • (β • [V,[V,δa]] - α • [V,[V,δb]])`

This is the τ⁵ leading content of `sym_cubic_poly(4X, Y)` once we substitute
`δa = 4·(pτ)³ • E_3 + O(τ⁵)` and `δb = ((1-4p)τ)³ • E_3 + O(τ⁵)`. The
expansion of `[V,[V,E_3]]` (with `V = A+B`, `E_3 = sym_cubic_poly(A,B)`)
projects onto the 8 Childs commutators with `βᵢ(p)`-polynomial coefficients —
this is the symbolic content of B2.2.e.

The **quadratic part Q** has 6 4-fold-commutator terms with mixed `(α,β,V,δ)`
content; the **cubic part C** is `-(1/24)·[δa,[δa,δb]] + (1/12)·[δb,[δb,δa]]`.
Both are bounded by combinations of `N·D²` and `D³`.
-/

/-- **Linear-in-residual part of `sym_cubic_poly(α•V + δa, β•V + δb)`**.

Closed form: `((24⁻¹) * (α + 2β)) • (β • [V,[V,δa]] - α • [V,[V,δb]])`. The
substitution `α = 4pτ, β = (1-4p)τ, δa = 4·(pτ)³·E_3, δb = ((1-4p)τ)³·E_3`
turns this into the τ⁵ Childs-basis contribution of `sym_cubic_poly(4X, Y)`. -/
noncomputable def sym_cubic_poly_linear_part_smul_V
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) : 𝔸 :=
  ((24 : 𝕂)⁻¹ * (α + 2 * β)) •
    (β • commBr V (commBr V δa) - α • commBr V (commBr V δb))

/-- **Quadratic-in-residual part of `sym_cubic_poly(α•V + δa, β•V + δb)`**. -/
noncomputable def sym_cubic_poly_quadratic_part_smul_V
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) : 𝔸 :=
  -((24 : 𝕂)⁻¹ • (commBr (α • V) (commBr δa δb) +
                    α • commBr δa (commBr V δb) +
                    β • commBr δa (commBr δa V))) +
  (12 : 𝕂)⁻¹ • (commBr (β • V) (commBr δb δa) +
                  β • commBr δb (commBr V δa) +
                  α • commBr δb (commBr δb V))

/-- **Cubic-in-residual part of `sym_cubic_poly(α•V + δa, β•V + δb)`**.

Closed form: `-(1/24)·[δa,[δa,δb]] + (1/12)·[δb,[δb,δa]]`. -/
noncomputable def sym_cubic_poly_cubic_part_smul_V
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (δa δb : 𝔸) : 𝔸 :=
  -((24 : 𝕂)⁻¹ • commBr δa (commBr δa δb)) +
  (12 : 𝕂)⁻¹ • commBr δb (commBr δb δa)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Algebraic decomposition of `sym_cubic_poly(α•V + δa, β•V + δb)`**:

  `sym_cubic_poly(α•V + δa, β•V + δb) = L + Q + C`

where `L` is the linear-in-δ part (B2.2.e foundation), `Q` is quadratic, and
`C` is cubic. Verified by CAS expansion (see header docstring) and proved
here via `noncomm_ring` after scalar clearing. -/
theorem symmetric_bch_cubic_poly_smul_V_decomp
    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) :
    symmetric_bch_cubic_poly 𝕂 (α • V + δa) (β • V + δb) =
      sym_cubic_poly_linear_part_smul_V V α β δa δb +
      sym_cubic_poly_quadratic_part_smul_V V α β δa δb +
      sym_cubic_poly_cubic_part_smul_V (𝕂 := 𝕂) δa δb := by
  -- Multiply both sides by 24 to clear the inverse scalars.
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  have h12ne : (12 : 𝕂) ≠ 0 := by exact_mod_cast (show (12 : ℕ) ≠ 0 by norm_num)
  have h24ne : (24 : 𝕂) ≠ 0 := by exact_mod_cast (show (24 : ℕ) ≠ 0 by norm_num)
  have hinj : Function.Injective ((24 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x y hxy
    have := congrArg ((24 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h24ne, one_smul] at this; exact this
  -- Helper scalar identities (needed during simp).
  have h24mul24inv : (24 : 𝕂) * (24 : 𝕂)⁻¹ = 1 := mul_inv_cancel₀ h24ne
  have h24mul12inv : (24 : 𝕂) * (12 : 𝕂)⁻¹ = 2 := by
    have h12_2 : (12 : 𝕂) * 2 = 24 := by norm_num
    have : (24 : 𝕂) * (12 : 𝕂)⁻¹ = (12 * 2) * (12 : 𝕂)⁻¹ := by rw [h12_2]
    rw [this, mul_comm (12 : 𝕂) 2, mul_assoc, mul_inv_cancel₀ h12ne, mul_one]
  have h24mul12inv_assoc : ∀ (X : 𝕂), (24 : 𝕂) * ((12 : 𝕂)⁻¹ * X) = 2 * X :=
    fun X => by rw [← mul_assoc, h24mul12inv]
  apply hinj
  -- Unfold all definitions.
  unfold symmetric_bch_cubic_poly sym_cubic_poly_linear_part_smul_V
    sym_cubic_poly_quadratic_part_smul_V sym_cubic_poly_cubic_part_smul_V commBr
  -- Distribute scalar smul; collapse 24·24⁻¹ = 1 and 24·12⁻¹·X = 2·X patterns.
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    mul_inv_cancel_left₀ h24ne, h24mul24inv, h24mul12inv_assoc, h24mul12inv,
    one_smul, mul_one, one_mul]
  module

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Norm bound for the cubic-in-residual part**:
  `‖sym_cubic_poly_cubic_part_smul_V δa δb‖ ≤ (1/2) · (‖δa‖+‖δb‖)³`.

Each summand is a 3-fold commutator (depth 3) bounded by triangle inequality:
  `‖[δa,[δa,δb]]‖ ≤ 4·‖δa‖²·‖δb‖`, `‖[δb,[δb,δa]]‖ ≤ 4·‖δb‖²·‖δa‖`.
Combined with the scalars 1/24 and 1/12: `(1/24)·4 + (1/12)·4 = 1/2`. -/
theorem norm_sym_cubic_poly_cubic_part_smul_V_le (δa δb : 𝔸) :
    ‖sym_cubic_poly_cubic_part_smul_V (𝕂 := 𝕂) δa δb‖ ≤
      (1 / 2 : ℝ) * (‖δa‖ + ‖δb‖) ^ 3 := by
  unfold sym_cubic_poly_cubic_part_smul_V commBr
  set D := ‖δa‖ + ‖δb‖ with hD_def
  have hda_nn : 0 ≤ ‖δa‖ := norm_nonneg _
  have hdb_nn : 0 ≤ ‖δb‖ := norm_nonneg _
  have hda_le_D : ‖δa‖ ≤ D := by rw [hD_def]; linarith
  have hdb_le_D : ‖δb‖ ≤ D := by rw [hD_def]; linarith
  have hD_nn : 0 ≤ D := by rw [hD_def]; positivity
  -- ‖(24:𝕂)⁻¹‖ = 1/24, ‖(12:𝕂)⁻¹‖ = 1/12 in any RCLike 𝕂.
  have h24_norm : ‖((24 : 𝕂)⁻¹ : 𝕂)‖ = (1 / 24 : ℝ) := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h12_norm : ‖((12 : 𝕂)⁻¹ : 𝕂)‖ = (1 / 12 : ℝ) := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  -- Bound each scalar•commutator term via triangle inequality on 3-fold commutators.
  have hCa : ‖δa * (δa * δb - δb * δa) - (δa * δb - δb * δa) * δa‖ ≤ 4 * ‖δa‖ ^ 2 * ‖δb‖ := by
    calc _ ≤ ‖δa * (δa * δb - δb * δa)‖ + ‖(δa * δb - δb * δa) * δa‖ := norm_sub_le _ _
      _ ≤ ‖δa‖ * ‖δa * δb - δb * δa‖ + ‖δa * δb - δb * δa‖ * ‖δa‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ ≤ ‖δa‖ * (2 * ‖δa‖ * ‖δb‖) + (2 * ‖δa‖ * ‖δb‖) * ‖δa‖ := by
          have h_ab : ‖δa * δb - δb * δa‖ ≤ 2 * ‖δa‖ * ‖δb‖ := by
            calc _ ≤ ‖δa * δb‖ + ‖δb * δa‖ := norm_sub_le _ _
              _ ≤ ‖δa‖ * ‖δb‖ + ‖δb‖ * ‖δa‖ := by gcongr <;> exact norm_mul_le _ _
              _ = 2 * ‖δa‖ * ‖δb‖ := by ring
          gcongr
      _ = 4 * ‖δa‖ ^ 2 * ‖δb‖ := by ring
  have hCb : ‖δb * (δb * δa - δa * δb) - (δb * δa - δa * δb) * δb‖ ≤ 4 * ‖δb‖ ^ 2 * ‖δa‖ := by
    calc _ ≤ ‖δb * (δb * δa - δa * δb)‖ + ‖(δb * δa - δa * δb) * δb‖ := norm_sub_le _ _
      _ ≤ ‖δb‖ * ‖δb * δa - δa * δb‖ + ‖δb * δa - δa * δb‖ * ‖δb‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ ≤ ‖δb‖ * (2 * ‖δb‖ * ‖δa‖) + (2 * ‖δb‖ * ‖δa‖) * ‖δb‖ := by
          have h_ba : ‖δb * δa - δa * δb‖ ≤ 2 * ‖δb‖ * ‖δa‖ := by
            calc _ ≤ ‖δb * δa‖ + ‖δa * δb‖ := norm_sub_le _ _
              _ ≤ ‖δb‖ * ‖δa‖ + ‖δa‖ * ‖δb‖ := by gcongr <;> exact norm_mul_le _ _
              _ = 2 * ‖δb‖ * ‖δa‖ := by ring
          gcongr
      _ = 4 * ‖δb‖ ^ 2 * ‖δa‖ := by ring
  -- Combine via norm bound on each smul'd commutator.
  have h1 : ‖(24 : 𝕂)⁻¹ • (δa * (δa * δb - δb * δa) - (δa * δb - δb * δa) * δa)‖ ≤
      (1/24 : ℝ) * (4 * ‖δa‖ ^ 2 * ‖δb‖) := by
    calc _ ≤ ‖((24 : 𝕂)⁻¹ : 𝕂)‖ * _ := norm_smul_le _ _
      _ = (1/24 : ℝ) * _ := by rw [h24_norm]
      _ ≤ (1/24 : ℝ) * (4 * ‖δa‖ ^ 2 * ‖δb‖) := by
          apply mul_le_mul_of_nonneg_left hCa (by norm_num)
  have h2 : ‖(12 : 𝕂)⁻¹ • (δb * (δb * δa - δa * δb) - (δb * δa - δa * δb) * δb)‖ ≤
      (1/12 : ℝ) * (4 * ‖δb‖ ^ 2 * ‖δa‖) := by
    calc _ ≤ ‖((12 : 𝕂)⁻¹ : 𝕂)‖ * _ := norm_smul_le _ _
      _ = (1/12 : ℝ) * _ := by rw [h12_norm]
      _ ≤ (1/12 : ℝ) * (4 * ‖δb‖ ^ 2 * ‖δa‖) := by
          apply mul_le_mul_of_nonneg_left hCb (by norm_num)
  -- Bound ‖da²·db‖ and ‖db²·da‖ by D³.
  have ha2b_le : ‖δa‖ ^ 2 * ‖δb‖ ≤ D ^ 3 := by
    calc ‖δa‖ ^ 2 * ‖δb‖ ≤ D ^ 2 * D := by
          apply mul_le_mul _ hdb_le_D hdb_nn (by positivity)
          exact pow_le_pow_left₀ hda_nn hda_le_D 2
      _ = D ^ 3 := by ring
  have hb2a_le : ‖δb‖ ^ 2 * ‖δa‖ ≤ D ^ 3 := by
    calc ‖δb‖ ^ 2 * ‖δa‖ ≤ D ^ 2 * D := by
          apply mul_le_mul _ hda_le_D hda_nn (by positivity)
          exact pow_le_pow_left₀ hdb_nn hdb_le_D 2
      _ = D ^ 3 := by ring
  -- Final: triangle inequality.
  calc ‖-((24 : 𝕂)⁻¹ • (δa * (δa * δb - δb * δa) - (δa * δb - δb * δa) * δa)) +
          (12 : 𝕂)⁻¹ • (δb * (δb * δa - δa * δb) - (δb * δa - δa * δb) * δb)‖
      ≤ ‖-((24 : 𝕂)⁻¹ • (δa * (δa * δb - δb * δa) - (δa * δb - δb * δa) * δa))‖ +
        ‖(12 : 𝕂)⁻¹ • (δb * (δb * δa - δa * δb) - (δb * δa - δa * δb) * δb)‖ :=
            norm_add_le _ _
    _ = ‖(24 : 𝕂)⁻¹ • (δa * (δa * δb - δb * δa) - (δa * δb - δb * δa) * δa)‖ +
        ‖(12 : 𝕂)⁻¹ • (δb * (δb * δa - δa * δb) - (δb * δa - δa * δb) * δb)‖ := by
            rw [norm_neg]
    _ ≤ (1/24 : ℝ) * (4 * ‖δa‖ ^ 2 * ‖δb‖) +
        (1/12 : ℝ) * (4 * ‖δb‖ ^ 2 * ‖δa‖) := by linarith
    _ ≤ (1/24 : ℝ) * (4 * D ^ 3) + (1/12 : ℝ) * (4 * D ^ 3) := by
        have h1 : (1/24 : ℝ) * (4 * ‖δa‖ ^ 2 * ‖δb‖) ≤ (1/24 : ℝ) * (4 * D ^ 3) := by
          have h_ab_le : 4 * ‖δa‖ ^ 2 * ‖δb‖ ≤ 4 * D ^ 3 := by
            have := ha2b_le; linarith
          linarith
        have h2 : (1/12 : ℝ) * (4 * ‖δb‖ ^ 2 * ‖δa‖) ≤ (1/12 : ℝ) * (4 * D ^ 3) := by
          have h_ba_le : 4 * ‖δb‖ ^ 2 * ‖δa‖ ≤ 4 * D ^ 3 := by
            have := hb2a_le; linarith
          linarith
        linarith
    _ = (1 / 2 : ℝ) * D ^ 3 := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **3-fold-product norm bound**: `‖X·Y·Z‖ ≤ ‖X‖·‖Y‖·‖Z‖`. -/
private lemma norm_three_word_le (X Y Z : 𝔸) :
    ‖X * Y * Z‖ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ := by
  calc ‖X * Y * Z‖ ≤ ‖X * Y‖ * ‖Z‖ := norm_mul_le _ _
    _ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ := by gcongr; exact norm_mul_le _ _

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **3-fold commutator bound**: `‖[X, [Y, Z]]‖ ≤ 4·‖X‖·‖Y‖·‖Z‖`. -/
private lemma norm_three_commBr_le (X Y Z : 𝔸) :
    ‖commBr X (commBr Y Z)‖ ≤ 4 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
  unfold commBr
  -- [X, [Y,Z]] = X(YZ - ZY) - (YZ - ZY)X = XYZ - XZY - YZX + ZYX
  have hid : X * (Y * Z - Z * Y) - (Y * Z - Z * Y) * X =
      X * Y * Z - X * Z * Y - Y * Z * X + Z * Y * X := by noncomm_ring
  rw [hid]
  calc _ ≤ ‖X * Y * Z - X * Z * Y - Y * Z * X‖ + ‖Z * Y * X‖ := norm_add_le _ _
    _ ≤ (‖X * Y * Z - X * Z * Y‖ + ‖Y * Z * X‖) + ‖Z * Y * X‖ := by
        gcongr
        calc _ ≤ ‖X * Y * Z - X * Z * Y‖ + ‖-(Y * Z * X)‖ := by
              rw [show X * Y * Z - X * Z * Y - Y * Z * X =
                  X * Y * Z - X * Z * Y + -(Y * Z * X) from by abel]
              exact norm_add_le _ _
          _ = ‖X * Y * Z - X * Z * Y‖ + ‖Y * Z * X‖ := by rw [norm_neg]
    _ ≤ ((‖X * Y * Z‖ + ‖X * Z * Y‖) + ‖Y * Z * X‖) + ‖Z * Y * X‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ((‖X‖ * ‖Y‖ * ‖Z‖ + ‖X‖ * ‖Z‖ * ‖Y‖) + ‖Y‖ * ‖Z‖ * ‖X‖) + ‖Z‖ * ‖Y‖ * ‖X‖ := by
        gcongr <;> exact norm_three_word_le _ _ _
    _ = 4 * ‖X‖ * ‖Y‖ * ‖Z‖ := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **commBr is 𝕂-linear in the right slot**: `[X, c•Y] = c•[X, Y]`. -/
private lemma commBr_smul_right_eq (c : 𝕂) (X Y : 𝔸) :
    commBr X (c • Y) = c • commBr X Y := by
  unfold commBr
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **commBr is 𝕂-linear in the left slot**: `[c•X, Y] = c•[X, Y]`. -/
private lemma commBr_smul_left_eq (c : 𝕂) (X Y : 𝔸) :
    commBr (c • X) Y = c • commBr X Y := by
  unfold commBr
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Smul through 3-fold commutator (rearrange to inner-left slot)**:
  `c • [X, [Y, Z]] = [X, [c•Y, Z]]`. -/
private lemma smul_commBr_inner_left (c : 𝕂) (X Y Z : 𝔸) :
    c • commBr X (commBr Y Z) = commBr X (commBr (c • Y) Z) := by
  rw [commBr_smul_left_eq, commBr_smul_right_eq]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Smul through 3-fold commutator (rearrange to inner-right slot)**:
  `c • [X, [Y, Z]] = [X, [Y, c•Z]]`. -/
private lemma smul_commBr_inner_right (c : 𝕂) (X Y Z : 𝔸) :
    c • commBr X (commBr Y Z) = commBr X (commBr Y (c • Z)) := by
  rw [commBr_smul_right_eq, commBr_smul_right_eq]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Norm bound for the quadratic-in-residual part**:
  `‖sym_cubic_poly_quadratic_part_smul_V V α β δa δb‖ ≤ (3/2)·N·(‖δa‖+‖δb‖)²`

when `‖α•V‖, ‖β•V‖ ≤ N`. Each summand is a 3-fold commutator with one
`scalar•V` factor and two δ-factors. Rearranging via `smul_commBr_inner_*`,
each is bounded by `4·N·D²`; the 6 terms together with scalars 1/24, 1/12
give `(3/2)·N·D²`. -/
theorem norm_sym_cubic_poly_quadratic_part_smul_V_le
    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) (N : ℝ)
    (hα_le : ‖α • V‖ ≤ N) (hβ_le : ‖β • V‖ ≤ N) (hN_nn : 0 ≤ N) :
    ‖sym_cubic_poly_quadratic_part_smul_V V α β δa δb‖ ≤
      (3 / 2 : ℝ) * (N * (‖δa‖ + ‖δb‖) ^ 2) := by
  unfold sym_cubic_poly_quadratic_part_smul_V
  set D := ‖δa‖ + ‖δb‖ with hD_def
  have hda_nn : 0 ≤ ‖δa‖ := norm_nonneg _
  have hdb_nn : 0 ≤ ‖δb‖ := norm_nonneg _
  have hda_le_D : ‖δa‖ ≤ D := by rw [hD_def]; linarith
  have hdb_le_D : ‖δb‖ ≤ D := by rw [hD_def]; linarith
  have hD_nn : 0 ≤ D := by rw [hD_def]; positivity
  have hND_nn : 0 ≤ N * D ^ 2 := by positivity
  have h24_norm : ‖((24 : 𝕂)⁻¹ : 𝕂)‖ = (1 / 24 : ℝ) := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h12_norm : ‖((12 : 𝕂)⁻¹ : 𝕂)‖ = (1 / 12 : ℝ) := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  -- Rearrange the α• and β• into the inner V-slot.
  have hT2 : α • commBr δa (commBr V δb) = commBr δa (commBr (α • V) δb) :=
    smul_commBr_inner_left α δa V δb
  have hT3 : β • commBr δa (commBr δa V) = commBr δa (commBr δa (β • V)) :=
    smul_commBr_inner_right β δa δa V
  have hT5 : β • commBr δb (commBr V δa) = commBr δb (commBr (β • V) δa) :=
    smul_commBr_inner_left β δb V δa
  have hT6 : α • commBr δb (commBr δb V) = commBr δb (commBr δb (α • V)) :=
    smul_commBr_inner_right α δb δb V
  rw [hT2, hT3, hT5, hT6]
  -- Each of the 6 inner expressions is a 3-fold commutator [X, [Y, Z]].
  -- Bound each by 4·(scalar•V's norm)·(δ's norms) ≤ 4·N·D².
  have b1 : ‖commBr (α • V) (commBr δa δb)‖ ≤ 4 * N * D ^ 2 := by
    have := norm_three_commBr_le (α • V) δa δb
    calc _ ≤ 4 * ‖α • V‖ * ‖δa‖ * ‖δb‖ := this
      _ ≤ 4 * N * D * D := by gcongr
      _ = 4 * N * D ^ 2 := by ring
  have b2 : ‖commBr δa (commBr (α • V) δb)‖ ≤ 4 * N * D ^ 2 := by
    have := norm_three_commBr_le δa (α • V) δb
    calc _ ≤ 4 * ‖δa‖ * ‖α • V‖ * ‖δb‖ := this
      _ ≤ 4 * D * N * D := by gcongr
      _ = 4 * N * D ^ 2 := by ring
  have b3 : ‖commBr δa (commBr δa (β • V))‖ ≤ 4 * N * D ^ 2 := by
    have := norm_three_commBr_le δa δa (β • V)
    calc _ ≤ 4 * ‖δa‖ * ‖δa‖ * ‖β • V‖ := this
      _ ≤ 4 * D * D * N := by gcongr
      _ = 4 * N * D ^ 2 := by ring
  have b4 : ‖commBr (β • V) (commBr δb δa)‖ ≤ 4 * N * D ^ 2 := by
    have := norm_three_commBr_le (β • V) δb δa
    calc _ ≤ 4 * ‖β • V‖ * ‖δb‖ * ‖δa‖ := this
      _ ≤ 4 * N * D * D := by gcongr
      _ = 4 * N * D ^ 2 := by ring
  have b5 : ‖commBr δb (commBr (β • V) δa)‖ ≤ 4 * N * D ^ 2 := by
    have := norm_three_commBr_le δb (β • V) δa
    calc _ ≤ 4 * ‖δb‖ * ‖β • V‖ * ‖δa‖ := this
      _ ≤ 4 * D * N * D := by gcongr
      _ = 4 * N * D ^ 2 := by ring
  have b6 : ‖commBr δb (commBr δb (α • V))‖ ≤ 4 * N * D ^ 2 := by
    have := norm_three_commBr_le δb δb (α • V)
    calc _ ≤ 4 * ‖δb‖ * ‖δb‖ * ‖α • V‖ := this
      _ ≤ 4 * D * D * N := by gcongr
      _ = 4 * N * D ^ 2 := by ring
  -- Triangle inequality + scalar bounds.
  set T1 := commBr (α • V) (commBr δa δb)
  set T2 := commBr δa (commBr (α • V) δb)
  set T3 := commBr δa (commBr δa (β • V))
  set T4 := commBr (β • V) (commBr δb δa)
  set T5 := commBr δb (commBr (β • V) δa)
  set T6 := commBr δb (commBr δb (α • V))
  -- ‖-(c⁻¹ • (T1 + T2 + T3)) + c'⁻¹ • (T4 + T5 + T6)‖
  -- ≤ |c⁻¹|·(‖T1‖ + ‖T2‖ + ‖T3‖) + |c'⁻¹|·(‖T4‖ + ‖T5‖ + ‖T6‖)
  have hsmul1 : ‖(24 : 𝕂)⁻¹ • (T1 + T2 + T3)‖ ≤
      (1/24 : ℝ) * (4 * N * D ^ 2 + 4 * N * D ^ 2 + 4 * N * D ^ 2) := by
    calc _ ≤ ‖((24 : 𝕂)⁻¹ : 𝕂)‖ * ‖T1 + T2 + T3‖ := norm_smul_le _ _
      _ = (1/24 : ℝ) * ‖T1 + T2 + T3‖ := by rw [h24_norm]
      _ ≤ (1/24 : ℝ) * (‖T1‖ + ‖T2‖ + ‖T3‖) := by
          have h12 : ‖T1 + T2‖ ≤ ‖T1‖ + ‖T2‖ := norm_add_le _ _
          have h123 : ‖T1 + T2 + T3‖ ≤ ‖T1 + T2‖ + ‖T3‖ := norm_add_le _ _
          have : ‖T1 + T2 + T3‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ := by linarith
          linarith
      _ ≤ (1/24 : ℝ) * (4 * N * D ^ 2 + 4 * N * D ^ 2 + 4 * N * D ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith
  have hsmul2 : ‖(12 : 𝕂)⁻¹ • (T4 + T5 + T6)‖ ≤
      (1/12 : ℝ) * (4 * N * D ^ 2 + 4 * N * D ^ 2 + 4 * N * D ^ 2) := by
    calc _ ≤ ‖((12 : 𝕂)⁻¹ : 𝕂)‖ * ‖T4 + T5 + T6‖ := norm_smul_le _ _
      _ = (1/12 : ℝ) * ‖T4 + T5 + T6‖ := by rw [h12_norm]
      _ ≤ (1/12 : ℝ) * (‖T4‖ + ‖T5‖ + ‖T6‖) := by
          have h45 : ‖T4 + T5‖ ≤ ‖T4‖ + ‖T5‖ := norm_add_le _ _
          have h456 : ‖T4 + T5 + T6‖ ≤ ‖T4 + T5‖ + ‖T6‖ := norm_add_le _ _
          have : ‖T4 + T5 + T6‖ ≤ ‖T4‖ + ‖T5‖ + ‖T6‖ := by linarith
          linarith
      _ ≤ (1/12 : ℝ) * (4 * N * D ^ 2 + 4 * N * D ^ 2 + 4 * N * D ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith
  -- Final triangle inequality.
  calc ‖-((24 : 𝕂)⁻¹ • (T1 + T2 + T3)) + (12 : 𝕂)⁻¹ • (T4 + T5 + T6)‖
      ≤ ‖-((24 : 𝕂)⁻¹ • (T1 + T2 + T3))‖ + ‖(12 : 𝕂)⁻¹ • (T4 + T5 + T6)‖ :=
            norm_add_le _ _
    _ = ‖(24 : 𝕂)⁻¹ • (T1 + T2 + T3)‖ + ‖(12 : 𝕂)⁻¹ • (T4 + T5 + T6)‖ := by rw [norm_neg]
    _ ≤ (1/24 : ℝ) * (4 * N * D ^ 2 + 4 * N * D ^ 2 + 4 * N * D ^ 2) +
        (1/12 : ℝ) * (4 * N * D ^ 2 + 4 * N * D ^ 2 + 4 * N * D ^ 2) := by linarith
    _ = (3 / 2 : ℝ) * (N * D ^ 2) := by ring

/-! ### B2.2.e key identity: `[V, [V, sym_cubic_poly]]` projection on Childs basis

This is the **central symbolic content of B2.2.e**: the 5-fold commutator
`[A+B, [A+B, sym_cubic_poly(A, B)]]` decomposes onto the Childs 4-fold
commutator basis as

  `24 • [A+B, [A+B, sym_cubic_poly(A, B)]] =
     (C₁ + C₃ + C₅ + C₇) + 2 • (C₂ + C₄ + C₆ + C₈)`

where `Cᵢ = childsCommᵢ A B`. Equivalently (multiplying both sides by `1/24`),

  `[A+B, [A+B, sym_cubic_poly(A, B)]] =
     (1/24)·(C₁ + C₃ + C₅ + C₇) + (1/12)·(C₂ + C₄ + C₆ + C₈)`.

**Strategy** (closed in session 9): The proof factors into three small
ring-identity lemmas, each tractable by `noncomm_ring`:

1. `comm_AB_AB_ABA`: `[A+B, [A+B, [A, [B, A]]]] = C₁ + C₃ + C₅ + C₇`
   (direct expansion of both sides; ~64 monomials each).
2. `comm_AB_AB_BBA`: `[A+B, [A+B, [B, [B, A]]]] = C₂ + C₄ + C₆ + C₈`
   (similar).
3. `smul_24_symmetric_bch_cubic_poly`:
   `24 • sym_cubic_poly(A, B) = -[A,[A,B]] + 2 • [B,[B,A]]`
   (clear inverse scalars 1/24, 1/12 in the def).

Combined with bilinearity of `commBr` and `[A,[A,B]] = -[A,[B,A]]`. -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e step 1**: `[A+B, [A+B, [A, [B, A]]]] = C₁ + C₃ + C₅ + C₇`.

By full ring expansion: both sides reduce to the same length-5 polynomial in
`(A, B)` after expanding `commBr X Y = X*Y - Y*X`. -/
private lemma comm_AB_AB_ABA_eq_childs_basis_odd (A B : 𝔸) :
    commBr (A + B) (commBr (A + B) (commBr A (commBr B A))) =
      childsComm₁ A B + childsComm₃ A B + childsComm₅ A B + childsComm₇ A B := by
  unfold childsComm₁ childsComm₃ childsComm₅ childsComm₇ commBr
  noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e step 2**: `[A+B, [A+B, [B, [B, A]]]] = C₂ + C₄ + C₆ + C₈`. -/
private lemma comm_AB_AB_BBA_eq_childs_basis_even (A B : 𝔸) :
    commBr (A + B) (commBr (A + B) (commBr B (commBr B A))) =
      childsComm₂ A B + childsComm₄ A B + childsComm₆ A B + childsComm₈ A B := by
  unfold childsComm₂ childsComm₄ childsComm₆ childsComm₈ commBr
  noncomm_ring

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e step 3**: `24 • sym_cubic_poly = -[A,[A,B]] + 2 • [B,[B,A]]`.

Clears the inverse scalars `1/24` and `1/12` in `symmetric_bch_cubic_poly`. -/
private lemma smul_24_symmetric_bch_cubic_poly (A B : 𝔸) :
    (24 : 𝕂) • symmetric_bch_cubic_poly 𝕂 A B =
      -commBr A (commBr A B) + (2 : 𝕂) • commBr B (commBr B A) := by
  have h24ne : (24 : 𝕂) ≠ 0 := by exact_mod_cast (show (24 : ℕ) ≠ 0 by norm_num)
  have h12ne : (12 : 𝕂) ≠ 0 := by exact_mod_cast (show (12 : ℕ) ≠ 0 by norm_num)
  unfold symmetric_bch_cubic_poly commBr
  rw [smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ h24ne]
  congr 1
  · simp [smul_sub]
  · have h24mul12inv : (24 : 𝕂) * (12 : 𝕂)⁻¹ = 2 := by
      have h12_2 : (12 : 𝕂) * 2 = 24 := by norm_num
      have : (24 : 𝕂) * (12 : 𝕂)⁻¹ = (12 * 2) * (12 : 𝕂)⁻¹ := by rw [h12_2]
      rw [this, mul_comm (12 : 𝕂) 2, mul_assoc, mul_inv_cancel₀ h12ne, mul_one]
    rw [h24mul12inv]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e step 4 (helper)**: `[A, [A, B]] = -[A, [B, A]]`. -/
private lemma comm_A_A_B_eq_neg_comm_A_B_A (A B : 𝔸) :
    commBr A (commBr A B) = -commBr A (commBr B A) := by
  unfold commBr; noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e step 5 (helper)**: `commBr X (Y₁ + Y₂) = commBr X Y₁ + commBr X Y₂`. -/
private lemma commBr_add_right_eq (X Y₁ Y₂ : 𝔸) :
    commBr X (Y₁ + Y₂) = commBr X Y₁ + commBr X Y₂ := by
  unfold commBr; noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e step 6 (helper)**: `commBr X (-Y) = -commBr X Y`. -/
private lemma commBr_neg_right_eq (X Y : 𝔸) :
    commBr X (-Y) = -commBr X Y := by
  unfold commBr; noncomm_ring

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e key identity**: `[V, [V, sym_cubic_poly]]` projection on Childs basis,
with the inverse scalars cleared (multiplied by 24).

  `24 • [A+B, [A+B, sym_cubic_poly(A, B)]] =
     (C₁ + C₃ + C₅ + C₇) + 2 • (C₂ + C₄ + C₆ + C₈)`

This is the projection identity that, after substituting `δa, δb` from B1.d
into `sym_cubic_poly_linear_part_smul_V`, gives the τ⁵ leading content of
the Suzuki-5 BCH formula on the Childs basis. The `βᵢ(p)` polynomial
prefactors emerge from this substitution combined with the `α + 2β` factor
in `sym_cubic_poly_linear_part_smul_V`. -/
theorem comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis (A B : 𝔸) :
    (24 : 𝕂) • commBr (A + B) (commBr (A + B) (symmetric_bch_cubic_poly 𝕂 A B)) =
      (childsComm₁ A B + childsComm₃ A B + childsComm₅ A B + childsComm₇ A B) +
      (2 : 𝕂) • (childsComm₂ A B + childsComm₄ A B + childsComm₆ A B + childsComm₈ A B) := by
  -- Build chain of intermediate equalities.
  have h1 : commBr (A + B) (commBr (A + B) ((24 : 𝕂) • symmetric_bch_cubic_poly 𝕂 A B)) =
            commBr (A + B) (commBr (A + B)
              (-commBr A (commBr A B) + (2 : 𝕂) • commBr B (commBr B A))) := by
    rw [smul_24_symmetric_bch_cubic_poly (𝕂 := 𝕂)]
  have h2 : commBr (A + B) (commBr (A + B)
              (-commBr A (commBr A B) + (2 : 𝕂) • commBr B (commBr B A))) =
            commBr (A + B) (commBr (A + B) (-commBr A (commBr A B))) +
            commBr (A + B) (commBr (A + B) ((2 : 𝕂) • commBr B (commBr B A))) := by
    rw [commBr_add_right_eq, commBr_add_right_eq]
  have h3 : commBr (A + B) (commBr (A + B) (-commBr A (commBr A B))) =
            -commBr (A + B) (commBr (A + B) (commBr A (commBr A B))) := by
    rw [commBr_neg_right_eq, commBr_neg_right_eq]
  have h4 : commBr (A + B) (commBr (A + B) ((2 : 𝕂) • commBr B (commBr B A))) =
            (2 : 𝕂) • commBr (A + B) (commBr (A + B) (commBr B (commBr B A))) := by
    rw [commBr_smul_right_eq (𝕂 := 𝕂), commBr_smul_right_eq (𝕂 := 𝕂)]
  have h5 : commBr A (commBr A B) = -commBr A (commBr B A) := comm_A_A_B_eq_neg_comm_A_B_A A B
  -- Push `24 •` inside via right-linearity (twice).
  rw [← commBr_smul_right_eq (𝕂 := 𝕂), ← commBr_smul_right_eq (𝕂 := 𝕂)]
  -- Apply the chain.
  rw [h1, h2, h3, h4, h5]
  -- Push the inner negation out through both outer commBrs.
  rw [commBr_neg_right_eq, commBr_neg_right_eq, neg_neg]
  -- Apply Step 1 and Step 2.
  rw [comm_AB_AB_ABA_eq_childs_basis_odd, comm_AB_AB_BBA_eq_childs_basis_even]

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e substitution lemma**: when `δa = γ • E_3` and `δb = δ • E_3` for
some shared `E_3 = symmetric_bch_cubic_poly A B`, the linear-in-residual part
of `sym_cubic_poly(α•V + δa, β•V + δb)` simplifies to a scalar multiple of
`[V, [V, E_3]]`:

  `sym_cubic_poly_linear_part_smul_V V α β (γ•E_3) (δ•E_3) =
     ((24)⁻¹ * (α + 2β) * (β·γ - α·δ)) • [V, [V, E_3]]`.

This isolates the "shape coefficient" `(α + 2β)·(β·γ - α·δ)/24` from the
underlying Lie polynomial `[V, [V, E_3]]`, ready for the Childs-basis
projection theorem. -/
theorem sym_cubic_poly_linear_part_at_smul_E3 (A B V : 𝔸) (α β γ δ : 𝕂) :
    sym_cubic_poly_linear_part_smul_V V α β
        (γ • symmetric_bch_cubic_poly 𝕂 A B)
        (δ • symmetric_bch_cubic_poly 𝕂 A B) =
      ((24 : 𝕂)⁻¹ * (α + 2 * β) * (β * γ - α * δ)) •
        commBr V (commBr V (symmetric_bch_cubic_poly 𝕂 A B)) := by
  unfold sym_cubic_poly_linear_part_smul_V
  -- δa = γ • E_3, δb = δ • E_3. Push γ, δ out, combine scalars.
  rw [show (β • commBr V (commBr V (γ • symmetric_bch_cubic_poly 𝕂 A B)) -
            α • commBr V (commBr V (δ • symmetric_bch_cubic_poly 𝕂 A B))) =
        (β * γ - α * δ) • commBr V (commBr V (symmetric_bch_cubic_poly 𝕂 A B)) from by
    simp only [commBr_smul_right_eq (𝕂 := 𝕂), smul_smul, ← sub_smul]]
  rw [smul_smul]

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e linear-part-on-Childs-basis theorem**: combining the substitution
lemma with the Childs-basis projection identity, when `δa = γ • E_3` and
`δb = δ • E_3` (with `V = A + B`), the linear part `L` is a specific
combination of the 8 Childs commutators:

  `24 • sym_cubic_poly_linear_part_smul_V (A+B) α β (γ•E_3) (δ•E_3) =
     ((24)⁻¹ * (α + 2β) * (β·γ - α·δ)) •
       [(C₁ + C₃ + C₅ + C₇) + 2 • (C₂ + C₄ + C₆ + C₈)]`

(Multiplying both sides by 24 clears the inverse scalar in the projection
identity.) This is the key τ⁵ Childs-basis content of `sym_cubic_poly(4X, Y)`
when `δa, δb` come from the cubic part of the per-block residual. -/
theorem smul_24_sym_cubic_poly_linear_part_at_smul_E3_eq_childs_basis
    (A B : 𝔸) (α β γ δ : 𝕂) :
    (24 : 𝕂) • sym_cubic_poly_linear_part_smul_V (A + B) α β
        (γ • symmetric_bch_cubic_poly 𝕂 A B)
        (δ • symmetric_bch_cubic_poly 𝕂 A B) =
      ((24 : 𝕂)⁻¹ * (α + 2 * β) * (β * γ - α * δ)) •
        ((childsComm₁ A B + childsComm₃ A B + childsComm₅ A B + childsComm₇ A B) +
         (2 : 𝕂) • (childsComm₂ A B + childsComm₄ A B + childsComm₆ A B + childsComm₈ A B)) := by
  rw [sym_cubic_poly_linear_part_at_smul_E3 (𝕂 := 𝕂) A B (A + B) α β γ δ]
  -- Now: 24 • (s • [V,[V,E₃]]) = s • (24 • [V,[V,E₃]]) via smul_comm.
  rw [smul_comm (24 : 𝕂) ((24 : 𝕂)⁻¹ * (α + 2 * β) * (β * γ - α * δ)) _]
  -- Apply the projection identity.
  rw [comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis (𝕂 := 𝕂) A B]

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e scalar instantiation**: substituting α = 4pτ, β = (1-4p)τ,
γ = 4(pτ)³, δ = ((1-4p)τ)³ (the τ³-leading parts of B1.d's per-block
residuals 4·strangBlock_log_p − (4pτ)•V and strangBlock_log_(1-4p) − ((1-4p)τ)•V),
the linear part L collapses to a closed form with τ⁵ factored out:

  `L = ((1/3) * p * (1-4p) * (1-2p) * (p² - (1-4p)²) * τ⁵) • [V,[V,E_3]]`.

The coefficient `(1/3)·p(1-4p)(1-2p)(p²-(1-4p)²)` is the polynomial-in-p
prefactor of the τ⁵ contribution of the linear part. -/
theorem sym_cubic_poly_linear_part_at_strangBlock_E3 (A B : 𝔸) (p τ : 𝕂) :
    sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
        ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
        (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B) =
      ((1 / 3 : 𝕂) * p * (1 - 4 * p) * (1 - 2 * p) * (p ^ 2 - (1 - 4 * p) ^ 2) * τ ^ 5) •
        commBr (A + B) (commBr (A + B) (symmetric_bch_cubic_poly 𝕂 A B)) := by
  rw [sym_cubic_poly_linear_part_at_smul_E3 (𝕂 := 𝕂) A B (A + B)
        (4 * p * τ) ((1 - 4 * p) * τ) (4 * (p * τ) ^ 3) (((1 - 4 * p) * τ) ^ 3)]
  congr 1
  ring

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e closed-form L_leading on Childs basis**: combines the scalar
instantiation with the Childs-basis projection identity. The leading τ⁵
content of the linear-in-residual part (when both `δa, δb` take their
B1.d τ³-leading values) is, with the inverse-scalar `1/24` cleared:

  `24 • L_leading = ((1/3)·p(1-4p)(1-2p)(p²-(1-4p)²)·τ⁵) •
                       [(C₁+C₃+C₅+C₇) + 2 • (C₂+C₄+C₆+C₈)]`

Equivalently
`L_leading = (1/72)·poly_p·τ⁵ • (C₁+C₃+C₅+C₇)
              + (1/36)·poly_p·τ⁵ • (C₂+C₄+C₆+C₈)`
where `poly_p := p(1-4p)(1-2p)(p²-(1-4p)²)`.

The polynomial `poly_p` matches (up to additional contributions from
`E_5 = sym_quintic_poly` and the higher-order BCH sym_quintic_poly term)
the βᵢ(p) prefactors of `BCH.suzuki5_R5`. -/
theorem smul_24_sym_cubic_poly_linear_part_at_strangBlock_E3_eq_childs_basis
    (A B : 𝔸) (p τ : 𝕂) :
    (24 : 𝕂) • sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
        ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
        (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B) =
      ((1 / 3 : 𝕂) * p * (1 - 4 * p) * (1 - 2 * p) * (p ^ 2 - (1 - 4 * p) ^ 2) * τ ^ 5) •
        ((childsComm₁ A B + childsComm₃ A B + childsComm₅ A B + childsComm₇ A B) +
         (2 : 𝕂) • (childsComm₂ A B + childsComm₄ A B + childsComm₆ A B + childsComm₈ A B)) := by
  rw [sym_cubic_poly_linear_part_at_strangBlock_E3 (𝕂 := 𝕂) A B p τ]
  -- Now: 24 • (poly_p·τ⁵) • [V,[V,E₃]] = (poly_p·τ⁵) • (24 • [V,[V,E₃]])
  rw [smul_comm (24 : 𝕂) _ _]
  rw [comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis (𝕂 := 𝕂) A B]

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e: E_5 → Childs basis projection**.

The 30-term polynomial `symmetric_bch_quintic_poly` decomposes onto the
Childs 4-fold commutator basis (with free Jacobi parameters set to 0 —
verified by Gauss-Jordan symbolic solving in
`Lean-Trotter/scripts/compute_bch_prefactors.py`):

  `5760 • E_5 = -7·C₁ - 12·C₂ + 16·C₄ - 16·C₅ - 48·C₆ - 8·C₈`

(`C₃, C₇` coefficients are 0 — same sparsity pattern as `β₃, β₇` in
`suzuki5_R5`.) Note: 5760 = lcm of denominators (5760, 480, 360, 120, 720)
so the integer-coefficient form clears all rational scalars.

Combined with `comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis` (the
[V,[V,E_3]] projection), this is the second piece needed to express the
τ⁵ content of `suzuki5_bch` on the Childs basis as `R₅(A,B,p)`.

**Strategy**: clear the `5760` factor on LHS via `field_simp`-like
cancellation, then convert all 𝕂-smul to multiplications via
`Algebra.smul_def + map_intCast/map_ofNat`, finally `noncomm_ring` on
the ~126-monomial identity. -/
theorem smul_5760_symmetric_bch_quintic_poly_eq_childs_basis (A B : 𝔸) :
    (5760 : 𝕂) • symmetric_bch_quintic_poly 𝕂 A B =
      (-7 : 𝕂) • childsComm₁ A B +
      (-12 : 𝕂) • childsComm₂ A B +
      (16 : 𝕂) • childsComm₄ A B +
      (-16 : 𝕂) • childsComm₅ A B +
      (-48 : 𝕂) • childsComm₆ A B +
      (-8 : 𝕂) • childsComm₈ A B := by
  unfold symmetric_bch_quintic_poly childsComm₁ childsComm₂ childsComm₄ childsComm₅
    childsComm₆ childsComm₈ commBr
  have h5760ne : (5760 : 𝕂) ≠ 0 := by exact_mod_cast (show (5760 : ℕ) ≠ 0 by norm_num)
  -- Push 5760 • inside the 30-term sum, then collapse 5760·(k/5760) = k.
  simp only [smul_add, smul_smul]
  have hcancel : ∀ (k : 𝕂), (5760 : 𝕂) * (k / 5760) = k := by
    intro k; field_simp
  simp only [hcancel]
  -- Convert all 𝕂-smul to multiplication via algebraMap; collapse the algebraMap on
  -- integer/natural constants so noncomm_ring sees a pure ring expression.
  simp only [Algebra.smul_def, map_intCast, map_ofNat, Int.cast_neg, Int.cast_ofNat,
             Int.cast_natCast, Nat.cast_ofNat, map_neg, map_natCast]
  noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Jacobi relation**: `childsComm₂ A B = childsComm₃ A B`.

By Jacobi: `[A, [B, [B, A]]] - [B, [A, [B, A]]] = [[A, B], [B, A]] = 0`,
so `[A, [B, [B, A]]] = [B, [A, [B, A]]]`. Applying `[A, _]` to both sides
gives `[A, [A, [B, [B, A]]]] = [A, [B, [A, [B, A]]]]`, which is `C₂ = C₃`.

Verified directly by ring expansion. -/
theorem childsComm₂_eq_childsComm₃ (A B : 𝔸) :
    childsComm₂ A B = childsComm₃ A B := by
  unfold childsComm₂ childsComm₃ commBr
  noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Jacobi relation**: `childsComm₆ A B = childsComm₇ A B`.

By the same argument as `childsComm₂_eq_childsComm₃` but with the outer
bracket `[B, _]` instead of `[A, _]`. -/
theorem childsComm₆_eq_childsComm₇ (A B : 𝔸) :
    childsComm₆ A B = childsComm₇ A B := by
  unfold childsComm₆ childsComm₇ commBr
  noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.2.e residual bound**: combining the algebraic decomposition with the
quadratic and cubic norm bounds, the residual `sym_cubic_poly(α•V+δa, β•V+δb)
− linear_part(V, α, β, δa, δb)` is bounded by `(3/2)·N·D² + (1/2)·D³`.

This identifies the linear-in-residual part as the "leading O(τ⁵) content" in
the Suzuki τ⁵ identification, with everything else being O(τ⁶) or smaller.
With N = O(τ), D = O(τ³), the residual bound gives O(τ⁷). -/
theorem norm_sym_cubic_poly_sub_linear_part_le
    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) (N : ℝ)
    (hα_le : ‖α • V‖ ≤ N) (hβ_le : ‖β • V‖ ≤ N) (hN_nn : 0 ≤ N) :
    ‖symmetric_bch_cubic_poly 𝕂 (α • V + δa) (β • V + δb) -
        sym_cubic_poly_linear_part_smul_V V α β δa δb‖ ≤
      (3 / 2 : ℝ) * (N * (‖δa‖ + ‖δb‖) ^ 2) + (1 / 2 : ℝ) * (‖δa‖ + ‖δb‖) ^ 3 := by
  -- Use the decomposition: sym_cubic_poly = linear + quad + cubic.
  -- Then sym_cubic_poly - linear = quad + cubic, bounded by triangle inequality.
  rw [symmetric_bch_cubic_poly_smul_V_decomp V α β δa δb]
  rw [show (sym_cubic_poly_linear_part_smul_V V α β δa δb +
            sym_cubic_poly_quadratic_part_smul_V V α β δa δb +
            sym_cubic_poly_cubic_part_smul_V (𝕂 := 𝕂) δa δb) -
            sym_cubic_poly_linear_part_smul_V V α β δa δb =
        sym_cubic_poly_quadratic_part_smul_V V α β δa δb +
        sym_cubic_poly_cubic_part_smul_V (𝕂 := 𝕂) δa δb from by abel]
  calc _ ≤ ‖sym_cubic_poly_quadratic_part_smul_V V α β δa δb‖ +
          ‖sym_cubic_poly_cubic_part_smul_V (𝕂 := 𝕂) δa δb‖ := norm_add_le _ _
    _ ≤ (3/2 : ℝ) * (N * (‖δa‖ + ‖δb‖) ^ 2) +
        (1/2 : ℝ) * (‖δa‖ + ‖δb‖) ^ 3 := by
        have h1 := norm_sym_cubic_poly_quadratic_part_smul_V_le
                    (𝕂 := 𝕂) V α β δa δb N hα_le hβ_le hN_nn
        have h2 := norm_sym_cubic_poly_cubic_part_smul_V_le (𝕂 := 𝕂) δa δb
        linarith

/-! ### B2.5 helpers: bilinearity and norm bound for the linear-in-residual part

These are the building blocks of the `T₂` bound for the τ⁶ assembly:

- Bilinearity (subtraction form) lets us express
    `L(δa_actual, δb_actual) − L(δa_lead, δb_lead) = L(δa_actual − δa_lead,
    δb_actual − δb_lead)`, isolating the per-block sub-residuals
    `R_p = X − strangBlock_log_target_p`.
- Norm bound `‖L(V, α, β, δa, δb)‖ ≤ (1/6)·‖α + 2β‖·‖V‖²·(‖β‖·‖δa‖ + ‖α‖·‖δb‖)`
  combines `norm_smul_le` with the existing 3-fold commutator bound
  `norm_three_commBr_le`.

Combined, these give an O(τ⁷) bound on `‖L_extra‖ = ‖L(V, α, β, 4·R_p, R_q)‖`
when α = O(τ), β = O(τ), R_p = O(τ⁵), R_q = O(τ⁵). -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **commBr is additive in the right slot (subtraction form)**:
  `[X, Y₁ - Y₂] = [X, Y₁] - [X, Y₂]`. -/
private lemma commBr_sub_right_eq (X Y₁ Y₂ : 𝔸) :
    commBr X (Y₁ - Y₂) = commBr X Y₁ - commBr X Y₂ := by
  unfold commBr; noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **L is bilinear in (δa, δb) — subtraction form**:
  `L(V, α, β, δa1, δb1) - L(V, α, β, δa2, δb2) = L(V, α, β, δa1 - δa2, δb1 - δb2)`.

Packages bilinearity for the residual decomposition `L_actual − L_leading =
L(δa_actual − δa_lead, δb_actual − δb_lead)` used in B2.5. -/
theorem sym_cubic_poly_linear_part_smul_V_sub_eq
    (V : 𝔸) (α β : 𝕂) (δa1 δb1 δa2 δb2 : 𝔸) :
    sym_cubic_poly_linear_part_smul_V V α β δa1 δb1 -
        sym_cubic_poly_linear_part_smul_V V α β δa2 δb2 =
      sym_cubic_poly_linear_part_smul_V V α β (δa1 - δa2) (δb1 - δb2) := by
  unfold sym_cubic_poly_linear_part_smul_V
  -- Push `commBr V (commBr V _)` through the subtractions on the RHS.
  have h_a : commBr V (commBr V (δa1 - δa2)) =
             commBr V (commBr V δa1) - commBr V (commBr V δa2) := by
    rw [commBr_sub_right_eq, commBr_sub_right_eq]
  have h_b : commBr V (commBr V (δb1 - δb2)) =
             commBr V (commBr V δb1) - commBr V (commBr V δb2) := by
    rw [commBr_sub_right_eq, commBr_sub_right_eq]
  rw [h_a, h_b]
  -- Now the identity is module-theoretic in the four commutators.
  module

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Norm bound on the linear-in-residual part**:
  `‖L(V, α, β, δa, δb)‖ ≤ (1/6)·‖α + 2β‖·‖V‖²·(‖β‖·‖δa‖ + ‖α‖·‖δb‖)`.

Direct application of `norm_smul_le` for the leading scalar `(24)⁻¹·(α+2β)`,
then `norm_sub_le` + `norm_smul_le` on the inner combination, then
`norm_three_commBr_le` on each 3-fold commutator. The `4` from the 3-fold
commutator bound combines with `1/24` to give the leading `1/6`. -/
theorem norm_sym_cubic_poly_linear_part_smul_V_le (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) :
    ‖sym_cubic_poly_linear_part_smul_V V α β δa δb‖ ≤
      (1 / 6 : ℝ) * ‖α + 2 * β‖ * ‖V‖ ^ 2 * (‖β‖ * ‖δa‖ + ‖α‖ * ‖δb‖) := by
  unfold sym_cubic_poly_linear_part_smul_V
  have h_K_norm : ‖((24 : 𝕂)⁻¹ * (α + 2 * β) : 𝕂)‖ = (1 / 24 : ℝ) * ‖α + 2 * β‖ := by
    rw [norm_mul, norm_inv, RCLike.norm_ofNat]; norm_num
  have h_AB_nn : (0 : ℝ) ≤ ‖α + 2 * β‖ := norm_nonneg _
  have h_α_nn : (0 : ℝ) ≤ ‖α‖ := norm_nonneg _
  have h_β_nn : (0 : ℝ) ≤ ‖β‖ := norm_nonneg _
  have h_δa_nn : (0 : ℝ) ≤ ‖δa‖ := norm_nonneg _
  have h_δb_nn : (0 : ℝ) ≤ ‖δb‖ := norm_nonneg _
  have h_V_nn : (0 : ℝ) ≤ ‖V‖ := norm_nonneg _
  calc ‖((24 : 𝕂)⁻¹ * (α + 2 * β)) •
          (β • commBr V (commBr V δa) - α • commBr V (commBr V δb))‖
      ≤ ‖((24 : 𝕂)⁻¹ * (α + 2 * β) : 𝕂)‖ *
          ‖β • commBr V (commBr V δa) - α • commBr V (commBr V δb)‖ := norm_smul_le _ _
    _ = (1 / 24 : ℝ) * ‖α + 2 * β‖ *
          ‖β • commBr V (commBr V δa) - α • commBr V (commBr V δb)‖ := by rw [h_K_norm]
    _ ≤ (1 / 24 : ℝ) * ‖α + 2 * β‖ *
          (‖β • commBr V (commBr V δa)‖ + ‖α • commBr V (commBr V δb)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (1 / 24 : ℝ) * ‖α + 2 * β‖ *
          (‖β‖ * ‖commBr V (commBr V δa)‖ + ‖α‖ * ‖commBr V (commBr V δb)‖) := by
        gcongr <;> exact norm_smul_le _ _
    _ ≤ (1 / 24 : ℝ) * ‖α + 2 * β‖ *
          (‖β‖ * (4 * ‖V‖ * ‖V‖ * ‖δa‖) + ‖α‖ * (4 * ‖V‖ * ‖V‖ * ‖δb‖)) := by
        gcongr <;> exact norm_three_commBr_le _ _ _
    _ = (1 / 6 : ℝ) * ‖α + 2 * β‖ * ‖V‖ ^ 2 * (‖β‖ * ‖δa‖ + ‖α‖ * ‖δb‖) := by ring

/-! ### B2.5 T₂ residue equality: per-block residual identification

For the strangBlock case with α = 4pτ, β = (1-4p)τ, the per-block residual
differences are:
- `δa − δa_lead = (4 : 𝕂) • (X − strangBlock_log_target_p)`
- `δb − δb_lead = Y − strangBlock_log_target_q`

These identities support the τ⁶ assembly: combined with B1.a's `O(σ⁵)` per-block
cubic bound, the L_extra term is `O(τ⁷)`. -/

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **B2.5 helper**: identify the strangBlock residue
`(4 : 𝕂) • X - (4 * p * τ) • V - (4 * (p * τ) ^ 3) • E` with
`(4 : 𝕂) • (X - strangBlock_log_target_p)`. Pure algebraic identity. -/
theorem strangBlock_residue_eq_smul_X_sub_target (A B : 𝔸) (X : 𝔸) (p τ : 𝕂) :
    (4 : 𝕂) • X - (4 * p * τ) • (A + B) -
        (4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B =
      (4 : 𝕂) • (X - strangBlock_log_target 𝕂 A B p τ) := by
  unfold strangBlock_log_target
  have h1 : (4 * p * τ : 𝕂) • (A + B) = (4 : 𝕂) • ((p * τ) • (A + B)) := by
    rw [show (4 * p * τ : 𝕂) = (4 : 𝕂) * (p * τ) from by ring, ← smul_smul]
  have h2 : (4 * (p * τ) ^ 3 : 𝕂) • symmetric_bch_cubic_poly 𝕂 A B =
            (4 : 𝕂) • ((p * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B) := by
    rw [← smul_smul]
  rw [h1, h2, smul_sub, smul_add]
  module

include 𝕂 in
/-- **B2.5 T₂ bound (assembly form)**: residual `sym_cubic_poly(4X, Y) − L_leading_τ⁵`
bounded by QC + L_extra terms. Derived from `norm_sym_cubic_poly_sub_linear_part_le`
+ bilinearity (`sym_cubic_poly_linear_part_smul_V_sub_eq`) +
`norm_sym_cubic_poly_linear_part_smul_V_le` + per-block cubic bound
(`norm_strangBlock_log_sub_target_le`).

The bound has two pieces:
- **QC part**: `(3/2)·N·D² + (1/2)·D³` with N = ‖α•V‖+‖β•V‖, D = ‖4X−α•V‖+‖Y−β•V‖.
- **L_extra part**: `(1/6)·‖α+2β‖·‖V‖²·(‖β‖·4·R_p_bound + ‖α‖·R_q_bound)` with
  R_p_bound = `10⁷·σ_p⁵`, R_q_bound = `10⁷·σ_q⁵`.

For the τ⁶ assembly: with α = 4pτ, β = (1-4p)τ, the QC part is O(τ⁷) (since
N = O(τ), D = O(τ³)) and the L_extra part is O(τ⁷) (since ‖α+2β‖ = O(τ),
‖α‖, ‖β‖ = O(τ), R_p, R_q = O(τ⁵)). -/
theorem norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le (A B : 𝔸) (p τ : 𝕂)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖symmetric_bch_cubic_poly 𝕂
        ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
      sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
        ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
        (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)‖ ≤
      (3 / 2 : ℝ) *
        ((‖((4 * p * τ : 𝕂)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖) *
         (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ - ((4 * p * τ : 𝕂)) • (A + B)‖ +
          ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ -
            (((1 - 4 * p) * τ : 𝕂)) • (A + B)‖) ^ 2) +
      (1 / 2 : ℝ) *
        (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ - ((4 * p * τ : 𝕂)) • (A + B)‖ +
         ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ -
           (((1 - 4 * p) * τ : 𝕂)) • (A + B)‖) ^ 3 +
      (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : 𝕂)‖ * ‖A + B‖ ^ 2 *
        (‖(((1 - 4 * p) * τ) : 𝕂)‖ *
            (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
         ‖((4 * p * τ) : 𝕂)‖ *
            (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5)) := by
  -- Setup: just abbreviate the strangBlock_logs (NOT the scalars).
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  -- The crucial algebraic step: rewrite (4 : 𝕂) • X and Y in α•V + δa, β•V + δb form.
  -- Show this directly via `abel` after rewriting.
  have key : symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
      sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
        ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
        (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B) =
      (symmetric_bch_cubic_poly 𝕂
          ((4 * p * τ) • (A + B) + ((4 : 𝕂) • X - (4 * p * τ) • (A + B)))
          (((1 - 4 * p) * τ) • (A + B) +
            (Y - ((1 - 4 * p) * τ) • (A + B))) -
        sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
          ((4 : 𝕂) • X - (4 * p * τ) • (A + B))
          (Y - ((1 - 4 * p) * τ) • (A + B))) +
      sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
        ((4 : 𝕂) • X - (4 * p * τ) • (A + B) -
          (4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
        (Y - ((1 - 4 * p) * τ) • (A + B) -
          ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B) := by
    have h1 : (4 : 𝕂) • X = (4 * p * τ) • (A + B) +
        ((4 : 𝕂) • X - (4 * p * τ) • (A + B)) := by abel
    have h2 : Y = ((1 - 4 * p) * τ) • (A + B) +
        (Y - ((1 - 4 * p) * τ) • (A + B)) := by abel
    have h_bilin := sym_cubic_poly_linear_part_smul_V_sub_eq (𝕂 := 𝕂)
      (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
      ((4 : 𝕂) • X - (4 * p * τ) • (A + B))
      (Y - ((1 - 4 * p) * τ) • (A + B))
      ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
      (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)
    -- h_bilin: L(δa,δb) - L(δa_lead,δb_lead) = L(δa - δa_lead, δb - δb_lead)
    -- Goal after substituting h1, h2: rearrange to use h_bilin.
    conv_lhs => rw [h1, h2]
    rw [← h_bilin]
    abel
  rw [key]
  -- Now apply triangle inequality.
  refine le_trans (norm_add_le _ _) ?_
  -- Bound each term.
  have hα_le : ‖((4 * p * τ : 𝕂)) • (A + B)‖ ≤
      ‖((4 * p * τ : 𝕂)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ := by
    linarith [norm_nonneg ((((1 - 4 * p) * τ : 𝕂)) • (A + B))]
  have hβ_le : ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ ≤
      ‖((4 * p * τ : 𝕂)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ := by
    linarith [norm_nonneg ((((4 * p * τ : 𝕂))) • (A + B))]
  have hN_nn : (0 : ℝ) ≤ ‖((4 * p * τ : 𝕂)) • (A + B)‖ +
      ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ := by positivity
  have h_QC := norm_sym_cubic_poly_sub_linear_part_le (𝕂 := 𝕂) (A + B)
      (4 * p * τ) ((1 - 4 * p) * τ)
      ((4 : 𝕂) • X - (4 * p * τ) • (A + B))
      (Y - ((1 - 4 * p) * τ) • (A + B))
      (‖((4 * p * τ : 𝕂)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖)
      hα_le hβ_le hN_nn
  have h_L_extra := norm_sym_cubic_poly_linear_part_smul_V_le (𝕂 := 𝕂)
      (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
      ((4 : 𝕂) • X - (4 * p * τ) • (A + B) -
        (4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
      (Y - ((1 - 4 * p) * τ) • (A + B) -
        ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)
  -- Now bound the per-block residuals.
  have h_res_eq : (4 : 𝕂) • X - (4 * p * τ) • (A + B) -
      (4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B =
      (4 : 𝕂) • (X - strangBlock_log_target 𝕂 A B p τ) := by
    rw [hX_def]
    exact strangBlock_residue_eq_smul_X_sub_target (𝕂 := 𝕂) A B
      (strangBlock_log 𝕂 A B p τ) p τ
  have h_resq_eq : Y - ((1 - 4 * p) * τ) • (A + B) -
      ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B =
      Y - strangBlock_log_target 𝕂 A B (1 - 4 * p) τ := by
    unfold strangBlock_log_target
    abel
  have h_4_norm : ‖(4 : 𝕂)‖ = 4 := by rw [RCLike.norm_ofNat]
  have h_Rp_bound : ‖(4 : 𝕂) • X - (4 * p * τ) • (A + B) -
      (4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B‖ ≤
      4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) := by
    rw [h_res_eq]
    have hRp := norm_strangBlock_log_sub_target_le (𝕂 := 𝕂) A B p τ hp
    rw [hX_def] at *
    calc ‖(4 : 𝕂) • (strangBlock_log 𝕂 A B p τ - strangBlock_log_target 𝕂 A B p τ)‖
        ≤ ‖(4 : 𝕂)‖ *
            ‖strangBlock_log 𝕂 A B p τ - strangBlock_log_target 𝕂 A B p τ‖ :=
          norm_smul_le _ _
      _ = 4 * ‖strangBlock_log 𝕂 A B p τ - strangBlock_log_target 𝕂 A B p τ‖ := by
          rw [h_4_norm]
      _ ≤ 4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) := by gcongr
  have h_Rq_bound : ‖Y - ((1 - 4 * p) * τ) • (A + B) -
      ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B‖ ≤
      10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5 := by
    rw [h_resq_eq]
    rw [hY_def]
    exact norm_strangBlock_log_sub_target_le (𝕂 := 𝕂) A B (1 - 4 * p) τ h1m4p
  -- Apply norm bounds in the L_extra term.
  have h_L_extra_bnd :
      ‖sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
          ((4 : 𝕂) • X - (4 * p * τ) • (A + B) -
            (4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
          (Y - ((1 - 4 * p) * τ) • (A + B) -
            ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)‖ ≤
      (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : 𝕂)‖ * ‖A + B‖ ^ 2 *
        (‖(((1 - 4 * p) * τ) : 𝕂)‖ *
            (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
         ‖((4 * p * τ) : 𝕂)‖ *
            (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5)) := by
    refine le_trans h_L_extra ?_
    have hCoef_nn : (0 : ℝ) ≤ (1 / 6 : ℝ) *
        ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : 𝕂)‖ * ‖A + B‖ ^ 2 := by positivity
    apply mul_le_mul_of_nonneg_left _ hCoef_nn
    have hβ_nn : (0 : ℝ) ≤ ‖(((1 - 4 * p) * τ) : 𝕂)‖ := norm_nonneg _
    have hα_nn : (0 : ℝ) ≤ ‖((4 * p * τ) : 𝕂)‖ := norm_nonneg _
    have h1 := mul_le_mul_of_nonneg_left h_Rp_bound hβ_nn
    have h2 := mul_le_mul_of_nonneg_left h_Rq_bound hα_nn
    linarith
  -- Combine via linarith.
  linarith

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

/-! ### Quintic-order target infrastructure (B2.1)

Extends the cubic target machinery to track the τ⁵ contribution. The
algebraic structure mirrors the cubic case:

* `suzuki5_bch_quintic_coeff p := 4·p⁵ + (1-4p)⁵` — the τ⁵ scalar coefficient
  (sum of fifth powers of the 5 Strang block coefficients).
* `strangBlock_log_target_quintic` — per-block linear + cubic + quintic
  polynomial: `(cτ)•V + (cτ)³•E_sym + (cτ)⁵•E_quintic_sym`.
* `suzuki5_targets_sum_quintic` — algebraic identity: sum of 5 per-block
  quintic targets = `τ•V + C₃·τ³•E_sym + C₅·τ⁵•E_quintic_sym`.
* `target_quintic_sum_4_form` — convenient `4•T_p + T_{1-4p}` restatement.

These pieces together with B1.d (`norm_strangBlock_log_sub_quintic_target_le`)
unblock the per-block decomposition of `4X+Y` at τ⁵ precision.
-/

/-- The τ⁵ scalar coefficient of `suzuki5_bch`: `C₅(p) := 4p⁵ + (1-4p)⁵`.
This is the sum of fifth powers of the 5 Strang coefficients
`(p, p, 1-4p, p, p)`. Unlike `suzuki5_bch_cubic_coeff`, this does NOT vanish
under the Suzuki cubic-cancellation condition — its non-vanishing is what
makes the τ⁵ residual non-trivial. -/
def suzuki5_bch_quintic_coeff (𝕂 : Type*) [Field 𝕂] (p : 𝕂) : 𝕂 :=
  4 * p ^ 5 + (1 - 4 * p) ^ 5

/-- The "ideal" τ⁵-precision log of a Strang block: the polynomial
`cτ•(A+B) + (cτ)³•E_sym(A,B) + (cτ)⁵•E_quintic_sym(A,B)` that approximates
the actual log up to O(s⁷). Extends `strangBlock_log_target` by one degree. -/
noncomputable def strangBlock_log_target_quintic (𝕂 : Type*) [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (A B : 𝔸) (c τ : 𝕂) : 𝔸 :=
  (c * τ) • (A + B) + (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B
    + (c * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B

include 𝕂 in
/-- The sum of per-block quintic targets equals the τ⁵-precision target.

Linear sum: `Σc_i = 1`, giving `τ•V`.
Cubic sum: `Σc_i³ = 4p³+(1-4p)³ = C₃(p)`, giving `τ³·C₃·E_sym`.
Quintic sum: `Σc_i⁵ = 4p⁵+(1-4p)⁵ = C₅(p)`, giving `τ⁵·C₅·E_quintic`. -/
theorem suzuki5_targets_sum_quintic (A B : 𝔸) (p τ : 𝕂) :
    strangBlock_log_target_quintic 𝕂 A B p τ +
    strangBlock_log_target_quintic 𝕂 A B p τ +
    strangBlock_log_target_quintic 𝕂 A B (1 - 4 * p) τ +
    strangBlock_log_target_quintic 𝕂 A B p τ +
    strangBlock_log_target_quintic 𝕂 A B p τ =
    τ • (A + B) +
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
      (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B := by
  unfold strangBlock_log_target_quintic suzuki5_bch_cubic_coeff suzuki5_bch_quintic_coeff
  set V := A + B with hV_def
  set E := symmetric_bch_cubic_poly 𝕂 A B with hE_def
  set E5 := symmetric_bch_quintic_poly 𝕂 A B with hE5_def
  -- Linear/cubic/quintic coefficient sums.
  have h_lin_sum : (p * τ) + (p * τ) + ((1 - 4 * p) * τ) + (p * τ) + (p * τ) = τ := by ring
  have h_cub_sum : (p * τ) ^ 3 + (p * τ) ^ 3 + ((1 - 4 * p) * τ) ^ 3 + (p * τ) ^ 3 +
      (p * τ) ^ 3 = τ ^ 3 * (4 * p ^ 3 + (1 - 4 * p) ^ 3) := by ring
  have h_quint_sum : (p * τ) ^ 5 + (p * τ) ^ 5 + ((1 - 4 * p) * τ) ^ 5 + (p * τ) ^ 5 +
      (p * τ) ^ 5 = τ ^ 5 * (4 * p ^ 5 + (1 - 4 * p) ^ 5) := by ring
  -- Group LHS into linear + cubic + quintic.
  have hsplit :
      ((p * τ) • V + (p * τ) ^ 3 • E + (p * τ) ^ 5 • E5) +
      ((p * τ) • V + (p * τ) ^ 3 • E + (p * τ) ^ 5 • E5) +
      (((1 - 4 * p) * τ) • V + ((1 - 4 * p) * τ) ^ 3 • E +
         ((1 - 4 * p) * τ) ^ 5 • E5) +
      ((p * τ) • V + (p * τ) ^ 3 • E + (p * τ) ^ 5 • E5) +
      ((p * τ) • V + (p * τ) ^ 3 • E + (p * τ) ^ 5 • E5) =
      ((p * τ) • V + (p * τ) • V + ((1 - 4 * p) * τ) • V + (p * τ) • V + (p * τ) • V) +
      ((p * τ) ^ 3 • E + (p * τ) ^ 3 • E + ((1 - 4 * p) * τ) ^ 3 • E + (p * τ) ^ 3 • E +
        (p * τ) ^ 3 • E) +
      ((p * τ) ^ 5 • E5 + (p * τ) ^ 5 • E5 + ((1 - 4 * p) * τ) ^ 5 • E5 +
        (p * τ) ^ 5 • E5 + (p * τ) ^ 5 • E5) := by abel
  rw [hsplit]
  rw [show (p * τ) • V + (p * τ) • V + ((1 - 4 * p) * τ) • V + (p * τ) • V +
          (p * τ) • V =
          ((p * τ) + (p * τ) + ((1 - 4 * p) * τ) + (p * τ) + (p * τ)) • V from by
        simp only [add_smul],
      h_lin_sum]
  rw [show (p * τ) ^ 3 • E + (p * τ) ^ 3 • E + ((1 - 4 * p) * τ) ^ 3 • E + (p * τ) ^ 3 • E +
          (p * τ) ^ 3 • E =
          ((p * τ) ^ 3 + (p * τ) ^ 3 + ((1 - 4 * p) * τ) ^ 3 + (p * τ) ^ 3 +
            (p * τ) ^ 3) • E from by simp only [add_smul],
      h_cub_sum]
  rw [show (p * τ) ^ 5 • E5 + (p * τ) ^ 5 • E5 + ((1 - 4 * p) * τ) ^ 5 • E5 +
          (p * τ) ^ 5 • E5 + (p * τ) ^ 5 • E5 =
          ((p * τ) ^ 5 + (p * τ) ^ 5 + ((1 - 4 * p) * τ) ^ 5 + (p * τ) ^ 5 +
            (p * τ) ^ 5) • E5 from by simp only [add_smul],
      h_quint_sum]

include 𝕂 in
/-- Quintic target decomposition: `4•T_p^q + T_{1-4p}^q = τ•V + C₃·τ³•E + C₅·τ⁵•E5`.
Restatement of `suzuki5_targets_sum_quintic` using `(4:𝕂) • T_p` instead of
the repeated-addition form. -/
theorem target_quintic_sum_4_form (A B : 𝔸) (p τ : 𝕂) :
    (4 : 𝕂) • strangBlock_log_target_quintic 𝕂 A B p τ +
      strangBlock_log_target_quintic 𝕂 A B (1 - 4 * p) τ =
    τ • (A + B) +
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
      (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
        symmetric_bch_quintic_poly 𝕂 A B := by
  unfold strangBlock_log_target_quintic suzuki5_bch_cubic_coeff suzuki5_bch_quintic_coeff
  set V := A + B with hV_def
  set E := symmetric_bch_cubic_poly 𝕂 A B with hE_def
  set E5 := symmetric_bch_quintic_poly 𝕂 A B with hE5_def
  -- 4•((p·τ)•V + (p·τ)³•E + (p·τ)⁵•E5) = (4·(p·τ))•V + (4·(p·τ)³)•E + (4·(p·τ)⁵)•E5
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  -- Goal: (4·(p·τ))•V + (4·(p·τ)³)•E + (4·(p·τ)⁵)•E5 +
  --       (((1-4p)·τ)•V + ((1-4p)·τ)³•E + ((1-4p)·τ)⁵•E5) = ...
  have h1 : ((4 : 𝕂) * (p * τ)) • V + ((4 : 𝕂) * (p * τ) ^ 3) • E +
            ((4 : 𝕂) * (p * τ) ^ 5) • E5 +
            (((1 - 4 * p) * τ) • V + ((1 - 4 * p) * τ) ^ 3 • E +
             ((1 - 4 * p) * τ) ^ 5 • E5) =
            (((4 : 𝕂) * (p * τ)) + ((1 - 4 * p) * τ)) • V +
            (((4 : 𝕂) * (p * τ) ^ 3) + ((1 - 4 * p) * τ) ^ 3) • E +
            (((4 : 𝕂) * (p * τ) ^ 5) + ((1 - 4 * p) * τ) ^ 5) • E5 := by
    rw [add_smul, add_smul, add_smul]; abel
  rw [h1]
  -- Simplify scalar coefficients.
  congr 1
  · congr 1
    · congr 1; ring   -- (4·(p·τ)) + ((1-4p)·τ) = τ
    · congr 1; ring   -- (4·(p·τ)³) + ((1-4p)·τ)³ = τ³ · (4p³ + (1-4p)³)
  · congr 1; ring     -- (4·(p·τ)⁵) + ((1-4p)·τ)⁵ = τ⁵ · (4p⁵ + (1-4p)⁵)

/-! ### Septic-precision target (Stage 2 foundation)

Deg-7 analog of `strangBlock_log_target_quintic`. Used in Stage 2's
5-factor BCH septic remainder bound (the analog of B2.1 at one degree higher).
-/

/-- The τ⁷ scalar coefficient of `suzuki5_bch`: `C₇(p) := 4p⁷ + (1-4p)⁷`.
Sum of seventh powers of the 5 Strang coefficients `(p, p, 1-4p, p, p)`. -/
def suzuki5_bch_septic_coeff (𝕂 : Type*) [Field 𝕂] (p : 𝕂) : 𝕂 :=
  4 * p ^ 7 + (1 - 4 * p) ^ 7

/-- The "ideal" τ⁷-precision log of a Strang block: extends `strangBlock_log_target_quintic`
by one degree, adding `(cτ)⁷•E₇_sym`. -/
noncomputable def strangBlock_log_target_septic (𝕂 : Type*) [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (A B : 𝔸) (c τ : 𝕂) : 𝔸 :=
  (c * τ) • (A + B) + (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B
    + (c * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B
    + (c * τ) ^ 7 • symmetric_bch_septic_poly 𝕂 A B

include 𝕂 in
/-- Per-block septic targets sum to the τ⁷-precision target.

Septic sum: `Σc_i⁷ = 4p⁷ + (1-4p)⁷ = C₇(p)`, giving the new `τ⁷·C₇·E₇` term. -/
theorem suzuki5_targets_sum_septic (A B : 𝔸) (p τ : 𝕂) :
    strangBlock_log_target_septic 𝕂 A B p τ +
    strangBlock_log_target_septic 𝕂 A B p τ +
    strangBlock_log_target_septic 𝕂 A B (1 - 4 * p) τ +
    strangBlock_log_target_septic 𝕂 A B p τ +
    strangBlock_log_target_septic 𝕂 A B p τ =
    τ • (A + B) +
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
      (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B +
      (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B := by
  unfold strangBlock_log_target_septic suzuki5_bch_cubic_coeff suzuki5_bch_quintic_coeff
    suzuki5_bch_septic_coeff
  set V := A + B with hV_def
  set E := symmetric_bch_cubic_poly 𝕂 A B with hE_def
  set E5 := symmetric_bch_quintic_poly 𝕂 A B with hE5_def
  set E7 := symmetric_bch_septic_poly 𝕂 A B with hE7_def
  match_scalars <;> ring

include 𝕂 in
/-- Septic target decomposition: `4•T_p^s + T_{1-4p}^s = τ•V + C₃·τ³•E + C₅·τ⁵•E5 + C₇·τ⁷·E7`. -/
theorem target_septic_sum_4_form (A B : 𝔸) (p τ : 𝕂) :
    (4 : 𝕂) • strangBlock_log_target_septic 𝕂 A B p τ +
      strangBlock_log_target_septic 𝕂 A B (1 - 4 * p) τ =
    τ • (A + B) +
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
      (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B +
      (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B := by
  unfold strangBlock_log_target_septic suzuki5_bch_cubic_coeff suzuki5_bch_quintic_coeff
    suzuki5_bch_septic_coeff
  set V := A + B with hV_def
  set E := symmetric_bch_cubic_poly 𝕂 A B with hE_def
  set E5 := symmetric_bch_quintic_poly 𝕂 A B with hE5_def
  set E7 := symmetric_bch_septic_poly 𝕂 A B with hE7_def
  match_scalars <;> ring

include 𝕂 in
/-- **Per-block septic bound (B1.d-septic)**: each Strang block's log differs
from the extended target `cτ•V + (cτ)³•E_sym + (cτ)⁵•E₅_sym + (cτ)⁷•E₇_sym`
by at most `K·σ⁹` where `σ = ‖cτ•A‖+‖cτ•B‖`. Direct application of
`norm_symmetric_bch_septic_sub_poly_le` to the Strang composition `cτ•A, cτ•B`,
then pulling `(cτ)³`, `(cτ)⁵`, `(cτ)⁷` through via the homogeneity lemmas
`symmetric_bch_cubic_poly_smul`, `symmetric_bch_quintic_poly_smul`,
`symmetric_bch_septic_poly_smul`.

Analog of `norm_strangBlock_log_sub_quintic_target_le` at one degree higher;
foundation for `norm_4X_plus_Y_sub_septic_target_le` (B2.1-septic). -/
theorem norm_strangBlock_log_sub_septic_target_le (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1 / 4) :
    ‖strangBlock_log 𝕂 A B c τ - (c * τ) • (A + B)
        - (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B
        - (c * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B
        - (c * τ) ^ 7 • symmetric_bch_septic_poly 𝕂 A B‖ ≤
      1000000000000 * (‖(c * τ) • A‖ + ‖(c * τ) • B‖) ^ 9 := by
  unfold strangBlock_log
  -- Apply `norm_symmetric_bch_septic_sub_poly_le` with a = cτ•A, b = cτ•B.
  have key := norm_symmetric_bch_septic_sub_poly_le
    (𝕂 := 𝕂) ((c * τ) • A) ((c * τ) • B) h
  unfold symmetric_bch_cubic at key
  -- Regroup (cτA+cτB) as cτ•(A+B), factor (cτ)³ / (cτ)⁵ / (cτ)⁷ scalars outside.
  have hsmul_dist : (c * τ) • A + (c * τ) • B = (c * τ) • (A + B) := by rw [smul_add]
  have hcub_hom : symmetric_bch_cubic_poly 𝕂 ((c * τ) • A) ((c * τ) • B) =
      (c * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B :=
    symmetric_bch_cubic_poly_smul A B (c * τ)
  have hquint_hom : symmetric_bch_quintic_poly 𝕂 ((c * τ) • A) ((c * τ) • B) =
      (c * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B :=
    symmetric_bch_quintic_poly_smul A B (c * τ)
  have hsept_hom : symmetric_bch_septic_poly 𝕂 ((c * τ) • A) ((c * τ) • B) =
      (c * τ) ^ 7 • symmetric_bch_septic_poly 𝕂 A B :=
    symmetric_bch_septic_poly_smul A B (c * τ)
  rw [hsmul_dist, hcub_hom, hquint_hom, hsept_hom] at key
  exact key

include 𝕂 in
/-- **Per-block decomposition at quintic precision (B2.1)**: bound on
`‖4•X + Y − τ•V − C₃·τ³•E_sym − C₅·τ⁵•E_quintic_sym‖`.

Combines the per-block quintic bound (B1.d, `norm_strangBlock_log_sub_quintic_target_le`)
with the algebraic identity `target_quintic_sum_4_form` to give the
"linear+cubic+quintic" precision approximation of the per-block sum
`4X+Y` (where X, Y are the two distinct strangBlock_log instances). -/
theorem norm_4X_plus_Y_sub_quintic_target_le (A B : 𝔸) (p τ : 𝕂)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ +
        strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B‖ ≤
      4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
      20000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 := by
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  set T_p := strangBlock_log_target_quintic 𝕂 A B p τ with hTp_def
  set T_q := strangBlock_log_target_quintic 𝕂 A B (1 - 4 * p) τ with hTq_def
  -- B1.d per-block bounds.
  have hX_le : ‖X - T_p‖ ≤ 20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7 := by
    have := norm_strangBlock_log_sub_quintic_target_le (𝕂 := 𝕂) A B p τ hp
    -- The target unfolds as `T_p = (cτ)•V + (cτ)³•E + (cτ)⁵•E5`; B1.d's signature
    -- has the three subtracted parts written separately; collapse into T_p.
    have hT_eq : T_p =
        (p * τ) • (A + B) + (p * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B +
        (p * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B := by
      rw [hTp_def]; rfl
    have h_sub_eq :
        X - T_p =
        X - (p * τ) • (A + B) - (p * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B
          - (p * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B := by
      rw [hT_eq]; abel
    rw [h_sub_eq]; exact this
  have hY_le : ‖Y - T_q‖ ≤
      20000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 := by
    have := norm_strangBlock_log_sub_quintic_target_le (𝕂 := 𝕂) A B (1 - 4 * p) τ h1m4p
    have hT_eq : T_q =
        ((1 - 4 * p) * τ) • (A + B) +
          ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B +
          ((1 - 4 * p) * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B := by
      rw [hTq_def]; rfl
    have h_sub_eq :
        Y - T_q =
        Y - ((1 - 4 * p) * τ) • (A + B) -
          ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B -
          ((1 - 4 * p) * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B := by
      rw [hT_eq]; abel
    rw [h_sub_eq]; exact this
  -- Bound for 4•(X - T_p)
  have h4_norm_eq : ‖(4 : 𝕂)‖ = 4 := by rw [RCLike.norm_ofNat]
  have h4X_le : ‖(4 : 𝕂) • (X - T_p)‖ ≤
      4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) := by
    calc ‖(4 : 𝕂) • (X - T_p)‖ ≤ ‖(4 : 𝕂)‖ * ‖X - T_p‖ := norm_smul_le _ _
      _ = 4 * ‖X - T_p‖ := by rw [h4_norm_eq]
      _ ≤ 4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) := by gcongr
  -- Algebraic decomposition: rewrite (4•X + Y - target) = 4•(X - T_p) + (Y - T_q).
  have h_target_eq :
      τ • (A + B) +
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
          symmetric_bch_quintic_poly 𝕂 A B =
      (4 : 𝕂) • T_p + T_q := by
    rw [hTp_def, hTq_def]
    exact (target_quintic_sum_4_form (𝕂 := 𝕂) A B p τ).symm
  have h_rearrange :
      (4 : 𝕂) • X + Y - τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
          symmetric_bch_quintic_poly 𝕂 A B =
      (4 : 𝕂) • (X - T_p) + (Y - T_q) := by
    have h_to_sum : (4 : 𝕂) • X + Y - τ • (A + B) -
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
            symmetric_bch_quintic_poly 𝕂 A B =
        (4 : 𝕂) • X + Y - (τ • (A + B) +
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
            symmetric_bch_quintic_poly 𝕂 A B) := by abel
    rw [h_to_sum, h_target_eq, smul_sub]; abel
  rw [h_rearrange]
  -- Triangle inequality.
  calc ‖(4 : 𝕂) • (X - T_p) + (Y - T_q)‖
      ≤ ‖(4 : 𝕂) • (X - T_p)‖ + ‖Y - T_q‖ := norm_add_le _ _
    _ ≤ 4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
        20000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 := by
        linarith

include 𝕂 in
/-- **B2.2.e prep — `4X + Y` quintic identification under IsSuzukiCubic**:
under `IsSuzukiCubic p`, the τ³ term in `4X + Y` vanishes, and the τ⁵
contribution is exactly `(τ⁵ * (4p⁵ + (1-4p)⁵)) • E_5`:

  `‖4•X + Y - τ•V - (τ⁵ * (4p⁵+(1-4p)⁵)) • E_5‖ ≤ K·σ⁷`.

Direct corollary of `norm_4X_plus_Y_sub_quintic_target_le` after applying
`IsSuzukiCubic_iff` to set the cubic_coeff to 0. -/
theorem norm_4X_plus_Y_sub_quintic_target_of_IsSuzukiCubic_le
    (A B : 𝔸) (p τ : 𝕂) (hp_suzuki : IsSuzukiCubic p)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ +
        strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B‖ ≤
      4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
      20000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 := by
  have hcubic := hp_suzuki  -- 4p³ + (1-4p)³ = 0
  unfold IsSuzukiCubic suzuki5_bch_cubic_coeff at hcubic
  have h_main := norm_4X_plus_Y_sub_quintic_target_le (𝕂 := 𝕂) A B p τ hp h1m4p
  -- Substitute cubic_coeff = 0 ⇒ τ³•cubic_coeff•E_3 = 0.
  have h_zero_term :
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B = 0 := by
    have : suzuki5_bch_cubic_coeff 𝕂 p = 0 := hp_suzuki
    rw [this, mul_zero, zero_smul]
  -- Rewrite by removing the zero term.
  have h_rearrange :
      (4 : 𝕂) • strangBlock_log 𝕂 A B p τ + strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B =
      (4 : 𝕂) • strangBlock_log 𝕂 A B p τ + strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B := by
    rw [h_zero_term]; abel
  rw [h_rearrange] at h_main
  exact h_main

include 𝕂 in
/-- **Per-block decomposition at septic precision (B2.1-septic)**: bound on
`‖4•X + Y − τ•V − C₃·τ³•E − C₅·τ⁵•E₅ − C₇·τ⁷·E₇‖`.

Combines the per-block septic bound (B1.d-septic,
`norm_strangBlock_log_sub_septic_target_le`) with the algebraic identity
`target_septic_sum_4_form` to give the "linear+cubic+quintic+septic" precision
approximation of the per-block sum `4X+Y` (where X, Y are the two distinct
strangBlock_log instances).

Analog of `norm_4X_plus_Y_sub_quintic_target_le` at one degree higher.
Foundation for the τ⁸-tail bound in the Stage 2 chain (septic axiom
discharge). -/
theorem norm_4X_plus_Y_sub_septic_target_le (A B : 𝔸) (p τ : 𝕂)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ +
        strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B‖ ≤
      4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) +
      1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9 := by
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  set T_p := strangBlock_log_target_septic 𝕂 A B p τ with hTp_def
  set T_q := strangBlock_log_target_septic 𝕂 A B (1 - 4 * p) τ with hTq_def
  -- B1.d-septic per-block bounds.
  have hX_le : ‖X - T_p‖ ≤ 1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9 := by
    have := norm_strangBlock_log_sub_septic_target_le (𝕂 := 𝕂) A B p τ hp
    have hT_eq : T_p =
        (p * τ) • (A + B) + (p * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B +
        (p * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B +
        (p * τ) ^ 7 • symmetric_bch_septic_poly 𝕂 A B := by
      rw [hTp_def]; rfl
    have h_sub_eq :
        X - T_p =
        X - (p * τ) • (A + B) - (p * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B
          - (p * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B
          - (p * τ) ^ 7 • symmetric_bch_septic_poly 𝕂 A B := by
      rw [hT_eq]; abel
    rw [h_sub_eq]; exact this
  have hY_le : ‖Y - T_q‖ ≤
      1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9 := by
    have := norm_strangBlock_log_sub_septic_target_le (𝕂 := 𝕂) A B (1 - 4 * p) τ h1m4p
    have hT_eq : T_q =
        ((1 - 4 * p) * τ) • (A + B) +
          ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B +
          ((1 - 4 * p) * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B +
          ((1 - 4 * p) * τ) ^ 7 • symmetric_bch_septic_poly 𝕂 A B := by
      rw [hTq_def]; rfl
    have h_sub_eq :
        Y - T_q =
        Y - ((1 - 4 * p) * τ) • (A + B) -
          ((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B -
          ((1 - 4 * p) * τ) ^ 5 • symmetric_bch_quintic_poly 𝕂 A B -
          ((1 - 4 * p) * τ) ^ 7 • symmetric_bch_septic_poly 𝕂 A B := by
      rw [hT_eq]; abel
    rw [h_sub_eq]; exact this
  -- Bound for 4•(X - T_p)
  have h4_norm_eq : ‖(4 : 𝕂)‖ = 4 := by rw [RCLike.norm_ofNat]
  have h4X_le : ‖(4 : 𝕂) • (X - T_p)‖ ≤
      4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) := by
    calc ‖(4 : 𝕂) • (X - T_p)‖ ≤ ‖(4 : 𝕂)‖ * ‖X - T_p‖ := norm_smul_le _ _
      _ = 4 * ‖X - T_p‖ := by rw [h4_norm_eq]
      _ ≤ 4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) := by gcongr
  -- Algebraic decomposition: rewrite (4•X + Y - target) = 4•(X - T_p) + (Y - T_q).
  have h_target_eq :
      τ • (A + B) +
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B +
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B =
      (4 : 𝕂) • T_p + T_q := by
    rw [hTp_def, hTq_def]
    exact (target_septic_sum_4_form (𝕂 := 𝕂) A B p τ).symm
  have h_rearrange :
      (4 : 𝕂) • X + Y - τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B =
      (4 : 𝕂) • (X - T_p) + (Y - T_q) := by
    have h_to_sum : (4 : 𝕂) • X + Y - τ • (A + B) -
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B -
          (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B =
        (4 : 𝕂) • X + Y - (τ • (A + B) +
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B +
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B +
          (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B) := by
      abel
    rw [h_to_sum, h_target_eq, smul_sub]; abel
  rw [h_rearrange]
  -- Triangle inequality.
  calc ‖(4 : 𝕂) • (X - T_p) + (Y - T_q)‖
      ≤ ‖(4 : 𝕂) • (X - T_p)‖ + ‖Y - T_q‖ := norm_add_le _ _
    _ ≤ 4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) +
        1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9 := by
        linarith

include 𝕂 in
/-- **B2.1-septic under IsSuzukiCubic**: under `IsSuzukiCubic p`, the τ³ term
in `4X + Y` vanishes, leaving τ⁵·C₅·E₅ + τ⁷·C₇·E₇ + O(σ⁹):

  `‖4•X + Y - τ•V - (τ⁵·C₅)•E₅ - (τ⁷·C₇)•E₇‖ ≤ K·σ⁹`.

Direct corollary of `norm_4X_plus_Y_sub_septic_target_le`; the
`IsSuzukiCubic` hypothesis sets the τ³·C₃·E term to zero. Analog of
`norm_4X_plus_Y_sub_quintic_target_of_IsSuzukiCubic_le` at septic precision. -/
theorem norm_4X_plus_Y_sub_septic_target_of_IsSuzukiCubic_le
    (A B : 𝔸) (p τ : 𝕂) (hp_suzuki : IsSuzukiCubic p)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ +
        strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B‖ ≤
      4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) +
      1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9 := by
  have h_main := norm_4X_plus_Y_sub_septic_target_le (𝕂 := 𝕂) A B p τ hp h1m4p
  have h_zero_term :
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B = 0 := by
    have : suzuki5_bch_cubic_coeff 𝕂 p = 0 := hp_suzuki
    rw [this, mul_zero, zero_smul]
  have h_rearrange :
      (4 : 𝕂) • strangBlock_log 𝕂 A B p τ + strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B =
      (4 : 𝕂) • strangBlock_log 𝕂 A B p τ + strangBlock_log 𝕂 A B (1 - 4 * p) τ -
        τ • (A + B) -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) • symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) • symmetric_bch_septic_poly 𝕂 A B := by
    rw [h_zero_term]; abel
  rw [h_rearrange] at h_main
  exact h_main

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

include 𝕂 in
/-- **Suzuki-5 BCH at quintic precision (B2 stepping stone)**: combines the
symmetric-BCH decomposition `suzuki5_bch = (4•X + Y) + symmetric_bch_cubic(4•X, Y)`
with B1.c (`norm_symmetric_bch_quintic_sub_poly_le`) and B2.1
(`norm_4X_plus_Y_sub_quintic_target_le`) to bound

```
‖suzuki5_bch − τ•V − C₃(p)·τ³•E_sym − C₅(p)·τ⁵•E5_sym
   − symmetric_bch_cubic_poly(4•X, Y) − symmetric_bch_quintic_poly(4•X, Y)‖
  ≤ explicit_τ⁷_bound
```

The remaining symbolic work for B2 (closing the P1 axiom) is to identify the
two unsubtracted polynomial-in-(4X, Y) terms with `τ⁵·suzuki5_R5 A B p`,
which requires expanding each of `4X` and `Y` to linear precision and
projecting the result onto the Childs 4-fold commutator basis (B2.2-B2.4
of the session prompt).

Hypotheses are inherited from `norm_suzuki5_bch_sub_smul_sub_cubic_le` plus
the quintic-precision B1.c regimes. -/
theorem norm_suzuki5_bch_sub_smul_sub_quintic_le (A B : 𝔸) (p τ : 𝕂)
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
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
          symmetric_bch_quintic_poly 𝕂 A B -
        symmetric_bch_cubic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_quintic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ)‖ ≤
      4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
      20000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 +
      20000000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 7 := by
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  -- Step 1: suzuki5_bch = bch(bch(2•X, Y), 2•X) (M4a key step).
  have h_sym_bch :=
    suzuki5_bch_eq_symmetric_bch (𝕂 := 𝕂) A B p τ hR hp h1m4p hreg hZ1 hZ2
  -- Step 2: bch(bch(2•X, Y), 2•X) = (4•X + Y) + symmetric_bch_cubic(4•X, Y).
  have h_sbc_def : bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂)
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • X)) Y) ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • X)) =
      ((4 : 𝕂) • X + Y) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y := by
    unfold symmetric_bch_cubic
    abel
  have h_decomp : suzuki5_bch 𝕂 A B p τ =
      ((4 : 𝕂) • X + Y) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y := by
    rw [h_sym_bch]; exact h_sbc_def
  -- Step 3: rearrange the LHS into per-block residual + sym_bch_cubic residual.
  have h_diff_eq :
      suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
            symmetric_bch_quintic_poly 𝕂 A B -
          symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y =
        ((4 : 𝕂) • X + Y - τ • (A + B) -
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
            symmetric_bch_quintic_poly 𝕂 A B) +
        (symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y) := by
    rw [h_decomp]; abel
  rw [h_diff_eq]
  -- B2.1: per-block residual bound.
  have h_perblock := norm_4X_plus_Y_sub_quintic_target_le (𝕂 := 𝕂) A B p τ hp h1m4p
  -- B1.c: symmetric_bch_cubic - poly residual bound.
  have h_b1c := norm_symmetric_bch_quintic_sub_poly_le (𝕂 := 𝕂)
    ((4 : 𝕂) • X) Y hreg
  -- Triangle inequality.
  calc ‖((4 : 𝕂) • X + Y - τ • (A + B) -
            (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
            (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
              symmetric_bch_quintic_poly 𝕂 A B) +
        (symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y)‖
      ≤ ‖(4 : 𝕂) • X + Y - τ • (A + B) -
            (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
            (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
              symmetric_bch_quintic_poly 𝕂 A B‖ +
        ‖symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y‖ := norm_add_le _ _
    _ ≤ (4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
         20000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7) +
        20000000000 * (‖(4 : 𝕂) • X‖ + ‖Y‖) ^ 7 := by
        linarith
    _ = 4 * (20000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
        20000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 +
        20000000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                      ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 7 := by
        rw [hX_def, hY_def]

/-! ### Septic-precision (Stage 2 main): `norm_suzuki5_bch_sub_smul_sub_septic_le`

One-degree-higher analog of `norm_suzuki5_bch_sub_smul_sub_quintic_le`. Combines:

* the M4a decomposition `suzuki5_bch = (4•X + Y) + symmetric_bch_cubic(4•X, Y)`;
* the B2.1-septic per-block bound `norm_4X_plus_Y_sub_septic_target_le` on
  `‖4•X + Y − τ•V − C₃·τ³·E − C₅·τ⁵·E₅ − C₇·τ⁷·E₇‖`;
* the B1.c-septic Tier-2 stepping-stone theorem
  `norm_symmetric_bch_septic_sub_poly_le` on
  `‖symmetric_bch_cubic − sym_E₃ − sym_E₅ − sym_E₇‖`.

The result bounds the residual after subtracting the explicit
`τ•V`, `(τ³·C₃)·E`, `(τ⁵·C₅)·E₅`, `(τ⁷·C₇)·E₇` per-block targets AND
the corresponding `(4X, Y)` polynomial pieces, by `K·σ⁹` in the three
norm-sums.

Foundation for the under-regime σ⁹ assembly (Stage 4) and the final
septic axiom discharge. -/

include 𝕂 in
/-- **Septic-precision combined bound (Stage 2 main)**.
See the section docstring. -/
theorem norm_suzuki5_bch_sub_smul_sub_septic_le (A B : 𝔸) (p τ : 𝕂)
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
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
          symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
          symmetric_bch_septic_poly 𝕂 A B -
        symmetric_bch_cubic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_quintic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_septic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ)‖ ≤
      4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) +
      1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9 +
      1000000000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 9 := by
  set X := strangBlock_log 𝕂 A B p τ with hX_def
  set Y := strangBlock_log 𝕂 A B (1 - 4 * p) τ with hY_def
  -- Step 1: suzuki5_bch = bch(bch(2•X, Y), 2•X) (M4a key step).
  have h_sym_bch :=
    suzuki5_bch_eq_symmetric_bch (𝕂 := 𝕂) A B p τ hR hp h1m4p hreg hZ1 hZ2
  -- Step 2: bch(bch(2•X, Y), 2•X) = (4•X + Y) + symmetric_bch_cubic(4•X, Y).
  have h_sbc_def : bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂)
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • X)) Y) ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • X)) =
      ((4 : 𝕂) • X + Y) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y := by
    unfold symmetric_bch_cubic
    abel
  have h_decomp : suzuki5_bch 𝕂 A B p τ =
      ((4 : 𝕂) • X + Y) + symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y := by
    rw [h_sym_bch]; exact h_sbc_def
  -- Step 3: rearrange the LHS into per-block residual + sym_bch_cubic residual.
  have h_diff_eq :
      suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
            symmetric_bch_quintic_poly 𝕂 A B -
          (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
            symmetric_bch_septic_poly 𝕂 A B -
          symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_septic_poly 𝕂 ((4 : 𝕂) • X) Y =
        ((4 : 𝕂) • X + Y - τ • (A + B) -
          (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
          (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
            symmetric_bch_quintic_poly 𝕂 A B -
          (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
            symmetric_bch_septic_poly 𝕂 A B) +
        (symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y -
          symmetric_bch_septic_poly 𝕂 ((4 : 𝕂) • X) Y) := by
    rw [h_decomp]; abel
  rw [h_diff_eq]
  -- B2.1-septic: per-block residual bound.
  have h_perblock := norm_4X_plus_Y_sub_septic_target_le (𝕂 := 𝕂) A B p τ hp h1m4p
  -- B1.c-septic: symmetric_bch_cubic - poly residual bound.
  have h_b1c := norm_symmetric_bch_septic_sub_poly_le (𝕂 := 𝕂)
    ((4 : 𝕂) • X) Y hreg
  -- Triangle inequality.
  calc ‖((4 : 𝕂) • X + Y - τ • (A + B) -
            (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
            (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
              symmetric_bch_quintic_poly 𝕂 A B -
            (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
              symmetric_bch_septic_poly 𝕂 A B) +
        (symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_septic_poly 𝕂 ((4 : 𝕂) • X) Y)‖
      ≤ ‖(4 : 𝕂) • X + Y - τ • (A + B) -
            (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
            (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
              symmetric_bch_quintic_poly 𝕂 A B -
            (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
              symmetric_bch_septic_poly 𝕂 A B‖ +
        ‖symmetric_bch_cubic 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_cubic_poly 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_quintic_poly 𝕂 ((4 : 𝕂) • X) Y -
            symmetric_bch_septic_poly 𝕂 ((4 : 𝕂) • X) Y‖ := norm_add_le _ _
    _ ≤ (4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) +
         1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9) +
        1000000000000 * (‖(4 : 𝕂) • X‖ + ‖Y‖) ^ 9 := by
        linarith
    _ = 4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) +
        1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9 +
        1000000000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                      ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 9 := by
        rw [hX_def, hY_def]

include 𝕂 in
/-- **Stage 2 main under `IsSuzukiCubic` p**: cubic-term-suppressed septic
combined bound. Under the Suzuki cubic-cancellation condition (`4p³ +
(1-4p)³ = 0`), the τ³·C₃(p)·E term drops out of the Stage 2 main bound,
leaving the cleaner form

```
‖suzuki5_bch - τ•V - (τ⁵·C₅)·E₅ - (τ⁷·C₇)·E₇ - sym_E₃(4X,Y) -
   sym_E₅(4X,Y) - sym_E₇(4X,Y)‖ ≤ K·σ⁹
```

Direct corollary of `norm_suzuki5_bch_sub_smul_sub_septic_le`. -/
theorem norm_suzuki5_bch_sub_smul_sub_septic_of_IsSuzukiCubic_le
    (A B : 𝔸) (p τ : 𝕂) (hSuzuki : IsSuzukiCubic p)
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
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
          symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
          symmetric_bch_septic_poly 𝕂 A B -
        symmetric_bch_cubic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_quintic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_septic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ)‖ ≤
      4 * (1000000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 9) +
      1000000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 9 +
      1000000000000 * (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 9 := by
  have h_main := norm_suzuki5_bch_sub_smul_sub_septic_le (𝕂 := 𝕂)
    A B p τ hR hp h1m4p hreg hZ1 hZ2
  have h_coef_zero : suzuki5_bch_cubic_coeff 𝕂 p = 0 :=
    suzuki5_bch_cubic_coeff_eq_zero_of_IsSuzukiCubic hSuzuki
  have h_cubic_zero :
      (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B = 0 := by
    rw [h_coef_zero, mul_zero, zero_smul]
  have h_rearrange :
      suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
        (τ ^ 3 * suzuki5_bch_cubic_coeff 𝕂 p) • symmetric_bch_cubic_poly 𝕂 A B -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
          symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
          symmetric_bch_septic_poly 𝕂 A B -
        symmetric_bch_cubic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_quintic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_septic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) =
      suzuki5_bch 𝕂 A B p τ - τ • (A + B) -
        (τ ^ 5 * suzuki5_bch_quintic_coeff 𝕂 p) •
          symmetric_bch_quintic_poly 𝕂 A B -
        (τ ^ 7 * suzuki5_bch_septic_coeff 𝕂 p) •
          symmetric_bch_septic_poly 𝕂 A B -
        symmetric_bch_cubic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_quintic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
        symmetric_bch_septic_poly 𝕂
          ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
          (strangBlock_log 𝕂 A B (1 - 4 * p) τ) := by
    rw [h_cubic_zero]; abel
  rw [h_rearrange] at h_main
  exact h_main

/-! ### M4b: cubic vanishing under IsSuzukiCubic

Under the Suzuki condition `4p³ + (1-4p)³ = 0`, the cubic coefficient vanishes
and M4a collapses to a direct O(R⁴) bound on `suzuki5_bch - τ•(A+B)`.
-/

/-- The explicit polynomial RHS of the M4b bound under `IsSuzukiCubic`.
Abbreviates the ~40-term expression appearing in
`norm_suzuki5_bch_sub_smul_le_of_IsSuzukiCubic` so that downstream inequality
bounds avoid Lean kernel heartbeat timeouts during `whnf`/`isDefEq`/`Ring.evalAdd`
reductions on the full inlined expression. All existing theorems are restated
against this def; unfold it (`unfold suzuki5_bch_M4b_RHS`) only when you need
the explicit form (e.g. when bounding its terms). -/
noncomputable def suzuki5_bch_M4b_RHS (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (p τ : 𝕂) : ℝ :=
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
        10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))

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
    ‖suzuki5_bch 𝕂 A B p τ - τ • (A + B)‖ ≤ suzuki5_bch_M4b_RHS 𝕂 A B p τ := by
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
  unfold suzuki5_bch_M4b_RHS
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

/-! ### Exp-Lipschitz lemma

Bound on `‖exp(X + δ) - exp(X)‖` in terms of `‖δ‖` and the exp of the maximum of
the two arguments. Proved by summing the telescoping bound over the exp series:

  `exp(X+δ) - exp(X) = ∑' n ≥ 1, (n!)⁻¹ • ((X+δ)^n - X^n)`

bounded term-by-term using `norm_pow_add_sub_pow_le`. The resulting series telescopes
to `‖δ‖ · Real.exp(‖X‖+‖δ‖)`. -/

include 𝕂 in
/-- **Exp-Lipschitz**: `‖exp(X + δ) - exp(X)‖ ≤ ‖δ‖ · Real.exp(‖X‖ + ‖δ‖)`. -/
theorem norm_exp_add_sub_exp_le (X δ : 𝔸) :
    ‖exp (X + δ) - exp X‖ ≤ ‖δ‖ * Real.exp (‖X‖ + ‖δ‖) := by
  have hMnn : 0 ≤ ‖X‖ + ‖δ‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hδnn : 0 ≤ ‖δ‖ := norm_nonneg _
  -- exp(X+δ) - exp(X) = ∑' n, (n!)⁻¹ • ((X+δ)^n - X^n)
  have hfXδ :
      Summable (fun n => ((Nat.factorial n)⁻¹ : 𝕂) • (X + δ) ^ n) := by
    simpa using NormedSpace.expSeries_summable' (𝕂 := 𝕂) (X + δ)
  have hfX :
      Summable (fun n => ((Nat.factorial n)⁻¹ : 𝕂) • X ^ n) := by
    simpa using NormedSpace.expSeries_summable' (𝕂 := 𝕂) X
  have hf_summ :
      Summable (fun n => ((Nat.factorial n)⁻¹ : 𝕂) • ((X + δ) ^ n - X ^ n)) := by
    have := hfXδ.sub hfX
    refine this.congr (fun n => ?_)
    rw [smul_sub]
  have hexp_sub : exp (X + δ) - exp X =
      ∑' n, ((Nat.factorial n)⁻¹ : 𝕂) • ((X + δ) ^ n - X ^ n) := by
    have h1 :
        exp (X + δ) = ∑' n, (((Nat.factorial n)⁻¹ : 𝕂) • (X + δ) ^ n) := by
      have h :=
        (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) (X + δ)).tsum_eq.symm
      simpa using h
    have h2 :
        exp X = ∑' n, (((Nat.factorial n)⁻¹ : 𝕂) • X ^ n) := by
      have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) X).tsum_eq.symm
      simpa using h
    rw [h1, h2, ← hfXδ.tsum_sub hfX]
    congr 1
    funext n
    rw [smul_sub]
  rw [hexp_sub]
  -- Shift: the n=0 term vanishes, so ∑' n, f n = ∑' n, f (n+1)
  have hf0 :
      ((Nat.factorial 0)⁻¹ : 𝕂) • ((X + δ) ^ 0 - X ^ 0) = (0 : 𝔸) := by simp
  have h_shift :
      ∑' n, ((Nat.factorial n)⁻¹ : 𝕂) • ((X + δ) ^ n - X ^ n) =
      ∑' n, ((Nat.factorial (n + 1))⁻¹ : 𝕂) •
        ((X + δ) ^ (n + 1) - X ^ (n + 1)) := by
    rw [hf_summ.tsum_eq_zero_add, hf0, zero_add]
  rw [h_shift]
  -- Bound term-by-term.
  have h_term : ∀ n : ℕ,
      ‖((Nat.factorial (n + 1))⁻¹ : 𝕂) •
        ((X + δ) ^ (n + 1) - X ^ (n + 1))‖ ≤
        ((Nat.factorial n)⁻¹ : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n := by
    intro n
    have h_fact_eq :
        ((Nat.factorial (n + 1)) : ℝ) = (n + 1 : ℝ) * ((Nat.factorial n) : ℝ) := by
      push_cast [Nat.factorial_succ]; ring
    have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    have hnfact_pos : (0 : ℝ) < ((Nat.factorial n) : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have h_n1_fact_pos : (0 : ℝ) < ((Nat.factorial (n + 1)) : ℝ) := by
      rw [h_fact_eq]; positivity
    calc ‖((Nat.factorial (n + 1))⁻¹ : 𝕂) •
            ((X + δ) ^ (n + 1) - X ^ (n + 1))‖
        ≤ ‖((Nat.factorial (n + 1))⁻¹ : 𝕂)‖ *
            ‖(X + δ) ^ (n + 1) - X ^ (n + 1)‖ := norm_smul_le _ _
      _ = ((Nat.factorial (n + 1))⁻¹ : ℝ) *
            ‖(X + δ) ^ (n + 1) - X ^ (n + 1)‖ := by
          congr 1
          rw [norm_inv, RCLike.norm_natCast]
      _ ≤ ((Nat.factorial (n + 1))⁻¹ : ℝ) *
            ((n + 1 : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n) := by
          gcongr
          exact norm_pow_add_sub_pow_le X δ n
      _ = ((Nat.factorial n)⁻¹ : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n := by
          rw [h_fact_eq]
          field_simp
  -- Real.exp series.
  have h_real_exp :
      HasSum (fun n => ((Nat.factorial n)⁻¹ : ℝ) * (‖X‖ + ‖δ‖) ^ n)
        (Real.exp (‖X‖ + ‖δ‖)) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) (‖X‖ + ‖δ‖)
    simp only [smul_eq_mul] at h
    rwa [congr_fun Real.exp_eq_exp_ℝ (‖X‖ + ‖δ‖)]
  have h_exp_sum :
      HasSum (fun n => ((Nat.factorial n)⁻¹ : ℝ) * ‖δ‖ * (‖X‖ + ‖δ‖) ^ n)
        (‖δ‖ * Real.exp (‖X‖ + ‖δ‖)) := by
    have := h_real_exp.mul_left ‖δ‖
    refine this.congr_fun ?_
    intro n; ring
  exact tsum_of_norm_bounded h_exp_sum h_term

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
      (n : ℝ) * suzuki5_bch_M4b_RHS 𝕂 A B p τ := by
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

/-! ### M4b RHS is `O(‖τ‖⁵)` near zero

Payoff lemma for downstream Lean-Trotter. Asserts the existence of a radius
`δ > 0` and constant `K ≥ 0` such that `suzuki5_bch_M4b_RHS 𝕂 A B p τ ≤ K·‖τ‖⁵`
for all τ with `‖τ‖ < δ`. Closing `bch_iteratedDeriv_s4Func_order4` in
Lean-Trotter reduces to combining this with `norm_exp_add_sub_exp_le` and
`exp_suzuki5_bch` to obtain a single-step `O(‖τ‖⁵)` product bound, then
applying a Taylor-match-from-norm-bound lemma.

Proof outline (deferred; each term of the unfolded RHS is analyzed separately,
which only the opacity of `suzuki5_bch_M4b_RHS` makes feasible in Lean):
- Term 1 (`4·10⁷·(‖(p·τ)•A‖+‖(p·τ)•B‖)⁵`): exact ‖τ‖⁵ using
  `‖(c·τ)•X‖ = ‖c‖·‖τ‖·‖X‖`.
- Term 2 (`10⁷·(‖((1-4p)·τ)•A‖+‖((1-4p)·τ)•B‖)⁵`): same, with `c = 1-4p`.
- Term 3 (`10⁷·(‖4•strangBlock_log p τ‖+‖strangBlock_log (1-4p) τ‖)⁵`):
  use `norm_strangBlock_log_le` (η + η³ + 10⁷·η⁵ ≤ 40002·η for η ≤ 1/4)
  to linearize, then quintic. Needs `‖τ‖ ≤ δ_reg` small enough for the
  `1/4` regime hypotheses.
- Term 4 (the `(6)⁻¹·(‖4X‖+‖Y‖)·(sub-products)` term): each sub-product
  is O(τ⁴), and the outer factor contributes ‖τ‖, giving O(τ⁵). Bounds
  via the slice-9 commutator structure already established.

For `‖τ‖ ≤ 1`, `‖τ‖^k ≤ ‖τ‖^5` for `k ≥ 5` by monotonicity, which handles
the higher-order tails uniformly. -/

include 𝕂 in
/-- Helper: linearizes `norm_strangBlock_log_le` to a single-term bound
`‖strangBlock_log‖ ≤ 40002·η` for η ≤ 1/4. The constant `40002` covers
`1 + 1/16 + 10⁷/256` (since η² ≤ 1/16, η⁴ ≤ 1/256). -/
lemma norm_strangBlock_log_linear
    (A B : 𝔸) (c τ : 𝕂)
    (h : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ < 1/4) :
    ‖strangBlock_log 𝕂 A B c τ‖ ≤
      40002 * (‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) := by
  have hbase := norm_strangBlock_log_le (𝕂 := 𝕂) A B c τ h
  have heqA : ‖(c * τ) • A‖ = ‖(c * τ : 𝕂)‖ * ‖A‖ := norm_smul _ _
  have heqB : ‖(c * τ) • B‖ = ‖(c * τ : 𝕂)‖ * ‖B‖ := norm_smul _ _
  have hsum : ‖(c * τ) • A‖ + ‖(c * τ) • B‖ = ‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖) := by
    rw [heqA, heqB]; ring
  set η : ℝ := ‖(c * τ : 𝕂)‖ * (‖A‖ + ‖B‖) with hη_def
  have hη_le : η ≤ 1/4 := by linarith
  have hη_nn : 0 ≤ η := by rw [hη_def]; positivity
  have hη2 : η ^ 2 ≤ 1/16 := by nlinarith
  have hη4 : η ^ 4 ≤ 1/256 := by
    have hsq : η ^ 4 = (η ^ 2) ^ 2 := by ring
    rw [hsq]
    calc (η ^ 2) ^ 2 ≤ (1/16) ^ 2 := by
          exact pow_le_pow_left₀ (sq_nonneg η) hη2 2
      _ = 1/256 := by norm_num
  have hη3_le : η ^ 3 ≤ (1/16) * η := by
    have heq3 : η ^ 3 = η ^ 2 * η := by ring
    rw [heq3]
    exact mul_le_mul_of_nonneg_right hη2 hη_nn
  have hη5_le : 10000000 * η ^ 5 ≤ 40000 * η := by
    have heq5 : 10000000 * η ^ 5 = (10000000 * η ^ 4) * η := by ring
    rw [heq5]
    have hq : 10000000 * η ^ 4 ≤ 40000 := by nlinarith
    exact mul_le_mul_of_nonneg_right hq hη_nn
  linarith

set_option maxHeartbeats 16000000 in
include 𝕂 in
/-- Auxiliary quintic bound for the M4b RHS with explicit polynomial constants.
Takes `pn ≥ ‖p‖+1`, `qn ≥ ‖1-4p‖+1`, `s ≥ ‖A‖+‖B‖+1` and `‖τ‖ < 1/(5·pn·qn·s)`
as inputs. Extracted from the main theorem to avoid kernel whnf blowup. -/
private lemma suzuki5_bch_M4b_RHS_le_t5_aux
    (A B : 𝔸) (p τ : 𝕂) (pn qn s : ℝ)
    (hpn_ge : (1:ℝ) ≤ pn) (hqn_ge : (1:ℝ) ≤ qn) (hs_ge : (1:ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : 𝕂) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (5 * pn * qn * s)) :
    suzuki5_bch_M4b_RHS 𝕂 A B p τ ≤
      (4 * 10000000 * pn^5 * s^5
       + 10000000 * qn^5 * s^5
       + 10000000 * 40002^5 * (4*pn + qn)^5 * s^5
       + (1/6) * 40002 * (4*pn + qn) * s *
           (16 * 10000000 * pn * qn^5 * s^6)
       + (1/6) * 40002 * (4*pn + qn) * s *
           (16 * 10000000 * pn^5 * qn * s^6)
       + (1/6) * 40002 * (4*pn + qn) * s *
           (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10)) * ‖τ‖^5 := by
  have hpn_pos : (0:ℝ) < pn := by linarith
  have hqn_pos : (0:ℝ) < qn := by linarith
  have hs_pos  : (0:ℝ) < s  := by linarith
  -- Derive ‖τ‖ < 1/5 ≤ 1.
  have hτ_nn : (0:ℝ) ≤ ‖τ‖ := norm_nonneg _
  have h5pqs_pos : (0:ℝ) < 5 * pn * qn * s := by positivity
  have h_pqs_ge : (1:ℝ) ≤ pn * qn * s := by
    have h1 : (1:ℝ) ≤ pn * qn := by nlinarith [hpn_ge, hqn_ge, hpn_pos.le]
    nlinarith [h1, hs_ge, mul_pos hpn_pos hqn_pos]
  have h5pqs_ge : (5:ℝ) ≤ 5 * pn * qn * s := by nlinarith [h_pqs_ge]
  have hδ_le_one_fifth : 1 / (5 * pn * qn * s) ≤ 1/5 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 5) h5pqs_ge
  have hτ_lt_fifth : ‖τ‖ < 1/5 := lt_of_lt_of_le hτ_lt hδ_le_one_fifth
  have hτ_le_one : ‖τ‖ ≤ 1 := by linarith
  have hτ_le_fifth : ‖τ‖ ≤ 1/5 := le_of_lt hτ_lt_fifth
  -- Power monotonicity helpers.
  have hτ7_le_5 : ‖τ‖ ^ 7 ≤ ‖τ‖ ^ 5 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 5 ≤ 7)
  have hτ5_le_3 : ‖τ‖ ^ 5 ≤ ‖τ‖ ^ 3 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 3 ≤ 5)
  have hτ5_nn : (0:ℝ) ≤ ‖τ‖ ^ 5 := by positivity
  have hτ3_nn : (0:ℝ) ≤ ‖τ‖ ^ 3 := by positivity
  -- Norm equalities for products and smul.
  have hpτ_norm : ‖(p * τ : 𝕂)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hqτ_norm : ‖((1 - 4 * p) * τ : 𝕂)‖ = ‖((1:𝕂) - 4 * p)‖ * ‖τ‖ :=
    norm_mul _ _
  have hsmul_pτA : ‖(p * τ) • A‖ = ‖(p * τ : 𝕂)‖ * ‖A‖ := norm_smul _ _
  have hsmul_pτB : ‖(p * τ) • B‖ = ‖(p * τ : 𝕂)‖ * ‖B‖ := norm_smul _ _
  have hsmul_qτA : ‖((1 - 4 * p) * τ) • A‖ = ‖((1 - 4 * p) * τ : 𝕂)‖ * ‖A‖ :=
    norm_smul _ _
  have hsmul_qτB : ‖((1 - 4 * p) * τ) • B‖ = ‖((1 - 4 * p) * τ : 𝕂)‖ * ‖B‖ :=
    norm_smul _ _
  have hηp_eq : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ = ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_pτA, hsmul_pτB, hpτ_norm]; ring
  have hηq_eq : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ =
                ‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_qτA, hsmul_qτB, hqτ_norm]; ring
  -- Bound η_p ≤ pn·s·‖τ‖, η_q ≤ qn·s·‖τ‖.
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have h_p_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have h_q_nn : 0 ≤ ‖((1:𝕂) - 4 * p)‖ := norm_nonneg _
  have hηp_le : ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_pn_τ_nn : 0 ≤ pn * ‖τ‖ := by positivity
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hp_le h_τAB_nn
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_pn_τ_nn
      _ = pn * s * ‖τ‖ := by ring
  have hηq_le : ‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_qn_τ_nn : 0 ≤ qn * ‖τ‖ := by positivity
    calc ‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1:𝕂) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hq_le h_τAB_nn
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_qn_τ_nn
      _ = qn * s * ‖τ‖ := by ring
  have hηp_nn : 0 ≤ ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
  have hηq_nn : 0 ≤ ‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
  have hpnst_nn : 0 ≤ pn * s * ‖τ‖ := by positivity
  have hqnst_nn : 0 ≤ qn * s * ‖τ‖ := by positivity
  -- Regime hypotheses for `norm_strangBlock_log_linear`.
  have hpns_pos : (0:ℝ) < pn * s := by positivity
  have hqns_pos : (0:ℝ) < qn * s := by positivity
  have h1_5qn : 1 / (5 * qn) ≤ 1/5 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 5) (by nlinarith [hqn_ge])
  have h1_5pn : 1 / (5 * pn) ≤ 1/5 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 5) (by nlinarith [hpn_ge])
  have h_fifth_lt_quarter : (1:ℝ)/5 < 1/4 := by norm_num
  have hηp_lt_quarter : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1/4 := by
    rw [hηp_eq]
    have h1 : pn * s * ‖τ‖ < pn * s * (1 / (5 * pn * qn * s)) :=
      mul_lt_mul_of_pos_left hτ_lt hpns_pos
    have h2 : pn * s * (1 / (5 * pn * qn * s)) = 1 / (5 * qn) := by
      field_simp
    linarith
  have hηq_lt_quarter : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1/4 := by
    rw [hηq_eq]
    have h1 : qn * s * ‖τ‖ < qn * s * (1 / (5 * pn * qn * s)) :=
      mul_lt_mul_of_pos_left hτ_lt hqns_pos
    have h2 : qn * s * (1 / (5 * pn * qn * s)) = 1 / (5 * pn) := by
      field_simp
    linarith
  -- Linear ‖strangBlock_log‖ bounds.
  have hsbp_le := norm_strangBlock_log_linear (𝕂 := 𝕂) A B p τ hηp_lt_quarter
  have hsbq_le := norm_strangBlock_log_linear (𝕂 := 𝕂) A B (1 - 4 * p) τ hηq_lt_quarter
  have hsbp_bnd : ‖strangBlock_log 𝕂 A B p τ‖ ≤ 40002 * (pn * s * ‖τ‖) := by
    have h1 : 40002 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) =
              40002 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)) := by rw [hpτ_norm]
    have h2 : 40002 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)) ≤ 40002 * (pn * s * ‖τ‖) := by
      nlinarith [hηp_le]
    linarith
  have hsbq_bnd : ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ ≤ 40002 * (qn * s * ‖τ‖) := by
    have h1 : 40002 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) =
              40002 * (‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)) := by rw [hqτ_norm]
    have h2 : 40002 * (‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)) ≤ 40002 * (qn * s * ‖τ‖) := by
      nlinarith [hηq_le]
    linarith
  -- ‖4·sb_log‖ = 4·‖sb_log‖.
  have h4norm : ‖(4 : 𝕂)‖ = 4 := by simp
  have h4smul : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ =
                4 * ‖strangBlock_log 𝕂 A B p τ‖ := by
    rw [norm_smul, h4norm]
  have h4sbp_bnd : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ ≤
                    4 * 40002 * (pn * s * ‖τ‖) := by
    rw [h4smul]; nlinarith [hsbp_bnd, norm_nonneg (strangBlock_log 𝕂 A B p τ)]
  have hL_bnd : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ ≤
                40002 * (4*pn + qn) * s * ‖τ‖ := by
    have h := hsbq_bnd
    nlinarith [h4sbp_bnd, hsbq_bnd]
  have hL_nn : 0 ≤ ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖ := by positivity
  -- Now bound each of the four terms in the unfolded RHS.
  unfold suzuki5_bch_M4b_RHS
  -- Term 1: 4·10⁷·(η_p)^5 ≤ K1·‖τ‖^5 with K1 = 4·10⁷·pn⁵·s⁵
  have hT1 : 4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5) ≤
              (4 * 10000000 * pn^5 * s^5) * ‖τ‖^5 := by
    rw [hηp_eq]
    have h_pow : (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤ (pn * s * ‖τ‖)^5 :=
      pow_le_pow_left₀ hηp_nn hηp_le 5
    have hexpand : (pn * s * ‖τ‖)^5 = pn^5 * s^5 * ‖τ‖^5 := by ring
    calc 4 * (10000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5)
        ≤ 4 * (10000000 * (pn * s * ‖τ‖)^5) := by
          have h10nn : (0:ℝ) ≤ 10000000 := by norm_num
          nlinarith [h_pow, pow_nonneg hpnst_nn 5]
      _ = (4 * 10000000 * pn^5 * s^5) * ‖τ‖^5 := by rw [hexpand]; ring
  -- Term 2: 10⁷·(η_q)^5 ≤ K2·‖τ‖^5 with K2 = 10⁷·qn⁵·s⁵
  have hT2 : 10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5
              ≤ (10000000 * qn^5 * s^5) * ‖τ‖^5 := by
    rw [hηq_eq]
    have h_pow : (‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤ (qn * s * ‖τ‖)^5 :=
      pow_le_pow_left₀ hηq_nn hηq_le 5
    have hexpand : (qn * s * ‖τ‖)^5 = qn^5 * s^5 * ‖τ‖^5 := by ring
    calc 10000000 * (‖((1:𝕂) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5
        ≤ 10000000 * (qn * s * ‖τ‖)^5 := by
          nlinarith [h_pow, pow_nonneg hqnst_nn 5]
      _ = (10000000 * qn^5 * s^5) * ‖τ‖^5 := by rw [hexpand]; ring
  -- Term 3: 10⁷·(L)^5 ≤ K3·‖τ‖^5 with K3 = 10⁷·40002⁵·(4pn+qn)⁵·s⁵
  have hT3 : 10000000 *
              (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
               ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) ^ 5 ≤
              (10000000 * 40002^5 * (4*pn + qn)^5 * s^5) * ‖τ‖^5 := by
    have h_pow : (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                  ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖)^5 ≤
                 (40002 * (4*pn + qn) * s * ‖τ‖)^5 :=
      pow_le_pow_left₀ hL_nn hL_bnd 5
    have hexpand : (40002 * (4*pn + qn) * s * ‖τ‖)^5 =
                   40002^5 * (4*pn + qn)^5 * s^5 * ‖τ‖^5 := by ring
    have hbnd_nn : 0 ≤ (40002 * (4*pn + qn) * s * ‖τ‖)^5 := by positivity
    calc 10000000 *
         (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
          ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖)^5
        ≤ 10000000 * (40002 * (4*pn + qn) * s * ‖τ‖)^5 := by nlinarith [h_pow]
      _ = (10000000 * 40002^5 * (4*pn + qn)^5 * s^5) * ‖τ‖^5 := by rw [hexpand]; ring
  -- Term 4 sub-pieces.
  -- ‖(4*p*τ)•(A+B)‖ ≤ 4·pn·s·‖τ‖
  have h4pτ_eq : (4*p*τ : 𝕂) = (4 : 𝕂) * (p * τ) := by ring
  have h4pτ_norm : ‖(4*p*τ : 𝕂)‖ = 4 * ‖p‖ * ‖τ‖ := by
    rw [h4pτ_eq, norm_mul, h4norm, hpτ_norm]; ring
  have h4pτ_AB_le : ‖((4 * p * τ : 𝕂)) • (A + B)‖ ≤ 4 * (pn * s * ‖τ‖) := by
    rw [show ‖((4*p*τ : 𝕂)) • (A + B)‖ = ‖(4*p*τ : 𝕂)‖ * ‖A+B‖ from norm_smul _ _,
        h4pτ_norm]
    have hAB_norm : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    have hAB_le_s : ‖A + B‖ ≤ s := le_trans hAB_norm hAB_le
    have h4pn_τ_nn : 0 ≤ 4 * pn * ‖τ‖ := by positivity
    have h4_step : 4 * ‖p‖ ≤ 4 * pn := by linarith
    have h4_τ_nn : 0 ≤ 4 * ‖τ‖ := by positivity
    have h_AB_nonneg : 0 ≤ ‖A + B‖ := norm_nonneg _
    calc 4 * ‖p‖ * ‖τ‖ * ‖A + B‖
        = (4 * ‖p‖) * (‖τ‖ * ‖A + B‖) := by ring
      _ ≤ (4 * pn) * (‖τ‖ * ‖A + B‖) :=
          mul_le_mul_of_nonneg_right h4_step (by positivity)
      _ = 4 * pn * ‖τ‖ * ‖A + B‖ := by ring
      _ ≤ 4 * pn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le_s h4pn_τ_nn
      _ = 4 * (pn * s * ‖τ‖) := by ring
  -- ‖((1-4p)*τ)•(A+B)‖ ≤ qn·s·‖τ‖
  have hqτ_AB_le : ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ ≤ qn * s * ‖τ‖ := by
    rw [show ‖(((1-4*p)*τ : 𝕂)) • (A + B)‖ = ‖((1-4*p)*τ : 𝕂)‖ * ‖A+B‖ from norm_smul _ _,
        hqτ_norm]
    have hAB_norm : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    have hAB_le_s : ‖A + B‖ ≤ s := le_trans hAB_norm hAB_le
    have hqn_τ_nn : 0 ≤ qn * ‖τ‖ := by positivity
    have h_AB_nonneg : 0 ≤ ‖A + B‖ := norm_nonneg _
    calc ‖((1:𝕂) - 4*p)‖ * ‖τ‖ * ‖A + B‖
        = ‖((1:𝕂) - 4*p)‖ * (‖τ‖ * ‖A + B‖) := by ring
      _ ≤ qn * (‖τ‖ * ‖A + B‖) :=
          mul_le_mul_of_nonneg_right hq_le (by positivity)
      _ = qn * ‖τ‖ * ‖A + B‖ := by ring
      _ ≤ qn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le_s hqn_τ_nn
      _ = qn * s * ‖τ‖ := by ring
  -- BR1 := ‖(1-4p)τ‖^3·s^3 + 10⁷·(‖(1-4p)τ‖·s)^5  ≤ 2·10⁷·qn^5·s^5·‖τ‖^3
  have hBR1_bnd : ‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                  10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 ≤
                  2 * 10000000 * (qn^5 * s^5 * ‖τ‖^3) := by
    have h_qτ_s : ‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
      rw [hqτ_norm]; exact hηq_le
    have h_qτ_s_nn : 0 ≤ ‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖) := by positivity
    have h_pow5 : (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5 ≤ (qn * s * ‖τ‖)^5 :=
      pow_le_pow_left₀ h_qτ_s_nn h_qτ_s 5
    have h_pow3 : (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^3 ≤ (qn * s * ‖τ‖)^3 :=
      pow_le_pow_left₀ h_qτ_s_nn h_qτ_s 3
    have heq3_mix : ‖((1 - 4 * p) * τ : 𝕂)‖^3 * (‖A‖ + ‖B‖)^3 =
                    (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^3 := by ring
    have hexp3 : (qn * s * ‖τ‖)^3 = qn^3 * s^3 * ‖τ‖^3 := by ring
    have hexp5 : (qn * s * ‖τ‖)^5 = qn^5 * s^5 * ‖τ‖^5 := by ring
    have hqn3_le : qn^3 ≤ qn^5 := pow_le_pow_right₀ hqn_ge (by norm_num : 3 ≤ 5)
    have hs3_le : s^3 ≤ s^5 := pow_le_pow_right₀ hs_ge (by norm_num : 3 ≤ 5)
    have hqn5_nn : 0 ≤ qn^5 := by positivity
    have hs5_nn : 0 ≤ s^5 := by positivity
    have h_qns5_nn : 0 ≤ qn^5 * s^5 := by positivity
    -- Combine
    calc ‖((1 - 4 * p) * τ : 𝕂)‖^3 * (‖A‖ + ‖B‖)^3 +
         10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5
        = (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5 := by rw [heq3_mix]
      _ ≤ (qn * s * ‖τ‖)^3 + 10000000 * (qn * s * ‖τ‖)^5 := by
          have h10nn : (0:ℝ) ≤ 10000000 := by norm_num
          have h_5_step : 10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5 ≤
                          10000000 * (qn * s * ‖τ‖)^5 := by
            exact mul_le_mul_of_nonneg_left h_pow5 h10nn
          linarith [h_pow3, h_5_step]
      _ = qn^3 * s^3 * ‖τ‖^3 + 10000000 * (qn^5 * s^5 * ‖τ‖^5) := by
          rw [hexp3, hexp5]
      _ ≤ qn^5 * s^5 * ‖τ‖^3 + 10000000 * (qn^5 * s^5 * ‖τ‖^3) := by
          have h1 : qn^3 * s^3 * ‖τ‖^3 ≤ qn^5 * s^5 * ‖τ‖^3 := by
            have ha : qn^3 * s^3 ≤ qn^5 * s^5 := by
              have hh1 : qn^3 * s^3 ≤ qn^5 * s^3 :=
                mul_le_mul_of_nonneg_right hqn3_le (by positivity)
              have hh2 : qn^5 * s^3 ≤ qn^5 * s^5 :=
                mul_le_mul_of_nonneg_left hs3_le hqn5_nn
              linarith
            exact mul_le_mul_of_nonneg_right ha hτ3_nn
          have h2 : 10000000 * (qn^5 * s^5 * ‖τ‖^5) ≤ 10000000 * (qn^5 * s^5 * ‖τ‖^3) := by
            have hh : qn^5 * s^5 * ‖τ‖^5 ≤ qn^5 * s^5 * ‖τ‖^3 :=
              mul_le_mul_of_nonneg_left hτ5_le_3 h_qns5_nn
            exact mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 10000000)
          linarith
      _ = (1 + 10000000) * (qn^5 * s^5 * ‖τ‖^3) := by ring
      _ ≤ 2 * 10000000 * (qn^5 * s^5 * ‖τ‖^3) := by
          have hpos : 0 ≤ qn^5 * s^5 * ‖τ‖^3 := by positivity
          have hcoeff : (1 + 10000000 : ℝ) ≤ 2 * 10000000 := by norm_num
          exact mul_le_mul_of_nonneg_right hcoeff hpos
  -- BR2 := same with p in place of (1-4p)
  have hBR2_bnd : ‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                  10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 ≤
                  2 * 10000000 * (pn^5 * s^5 * ‖τ‖^3) := by
    have h_pτ_s : ‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
      rw [hpτ_norm]; exact hηp_le
    have h_pτ_s_nn : 0 ≤ ‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖) := by positivity
    have h_pow5 : (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5 ≤ (pn * s * ‖τ‖)^5 :=
      pow_le_pow_left₀ h_pτ_s_nn h_pτ_s 5
    have h_pow3 : (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^3 ≤ (pn * s * ‖τ‖)^3 :=
      pow_le_pow_left₀ h_pτ_s_nn h_pτ_s 3
    have heq3_mix : ‖(p * τ : 𝕂)‖^3 * (‖A‖ + ‖B‖)^3 =
                    (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^3 := by ring
    have hexp3 : (pn * s * ‖τ‖)^3 = pn^3 * s^3 * ‖τ‖^3 := by ring
    have hexp5 : (pn * s * ‖τ‖)^5 = pn^5 * s^5 * ‖τ‖^5 := by ring
    have hpn3_le : pn^3 ≤ pn^5 := pow_le_pow_right₀ hpn_ge (by norm_num : 3 ≤ 5)
    have hs3_le : s^3 ≤ s^5 := pow_le_pow_right₀ hs_ge (by norm_num : 3 ≤ 5)
    have h_pns5_nn : 0 ≤ pn^5 * s^5 := by positivity
    calc ‖(p * τ : 𝕂)‖^3 * (‖A‖ + ‖B‖)^3 +
         10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5
        = (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^3 +
          10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5 := by rw [heq3_mix]
      _ ≤ (pn * s * ‖τ‖)^3 + 10000000 * (pn * s * ‖τ‖)^5 := by
          have h10nn : (0:ℝ) ≤ 10000000 := by norm_num
          have h_5_step : 10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖))^5 ≤
                          10000000 * (pn * s * ‖τ‖)^5 :=
            mul_le_mul_of_nonneg_left h_pow5 h10nn
          linarith [h_pow3, h_5_step]
      _ = pn^3 * s^3 * ‖τ‖^3 + 10000000 * (pn^5 * s^5 * ‖τ‖^5) := by
          rw [hexp3, hexp5]
      _ ≤ pn^5 * s^5 * ‖τ‖^3 + 10000000 * (pn^5 * s^5 * ‖τ‖^3) := by
          have h1 : pn^3 * s^3 * ‖τ‖^3 ≤ pn^5 * s^5 * ‖τ‖^3 := by
            have ha : pn^3 * s^3 ≤ pn^5 * s^5 := by
              have hh1 : pn^3 * s^3 ≤ pn^5 * s^3 :=
                mul_le_mul_of_nonneg_right hpn3_le (by positivity)
              have hh2 : pn^5 * s^3 ≤ pn^5 * s^5 :=
                mul_le_mul_of_nonneg_left hs3_le (by positivity)
              linarith
            exact mul_le_mul_of_nonneg_right ha hτ3_nn
          have h2 : 10000000 * (pn^5 * s^5 * ‖τ‖^5) ≤ 10000000 * (pn^5 * s^5 * ‖τ‖^3) := by
            have hh : pn^5 * s^5 * ‖τ‖^5 ≤ pn^5 * s^5 * ‖τ‖^3 :=
              mul_le_mul_of_nonneg_left hτ5_le_3 h_pns5_nn
            exact mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 10000000)
          linarith
      _ = (1 + 10000000) * (pn^5 * s^5 * ‖τ‖^3) := by ring
      _ ≤ 2 * 10000000 * (pn^5 * s^5 * ‖τ‖^3) := by
          have hpos : 0 ≤ pn^5 * s^5 * ‖τ‖^3 := by positivity
          have hcoeff : (1 + 10000000 : ℝ) ≤ 2 * 10000000 := by norm_num
          exact mul_le_mul_of_nonneg_right hcoeff hpos
  -- BR1, BR2 nonneg
  have hBR1_nn : 0 ≤ ‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                     10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 := by positivity
  have hBR2_nn : 0 ≤ ‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                     10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5 := by positivity
  have h4BR2_nn : 0 ≤ 4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                            10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by positivity
  -- S1, S2, S3 bounds.
  have hS1_bnd : 2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
                 (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                  10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) ≤
                 16 * 10000000 * pn * qn^5 * s^6 * ‖τ‖^4 := by
    have h_4pτAB_nn : 0 ≤ ‖((4 * p * τ : 𝕂)) • (A + B)‖ := norm_nonneg _
    calc 2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
         (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)
        ≤ 2 * (4 * (pn * s * ‖τ‖)) *
          (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
           10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by
          gcongr
      _ ≤ 2 * (4 * (pn * s * ‖τ‖)) * (2 * 10000000 * (qn^5 * s^5 * ‖τ‖^3)) := by
          gcongr
      _ = 16 * 10000000 * pn * qn^5 * s^6 * ‖τ‖^4 := by ring
  have hS2_bnd : 2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
                 (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                       10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) ≤
                 16 * 10000000 * pn^5 * qn * s^6 * ‖τ‖^4 := by
    have h_qτAB_nn : 0 ≤ ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ := norm_nonneg _
    calc 2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
         (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
               10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))
        ≤ 2 * (qn * s * ‖τ‖) *
          (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) := by
          gcongr
      _ ≤ 2 * (qn * s * ‖τ‖) * (4 * (2 * 10000000 * (pn^5 * s^5 * ‖τ‖^3))) := by
          gcongr
      _ = 16 * 10000000 * pn^5 * qn * s^6 * ‖τ‖^4 := by ring
  have hS3_bnd : 2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                          10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
                 (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                  10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) ≤
                 32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10 * ‖τ‖^6 := by
    calc 2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                   10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
         (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)
        ≤ 2 * (4 * (2 * 10000000 * (pn^5 * s^5 * ‖τ‖^3))) *
          (2 * 10000000 * (qn^5 * s^5 * ‖τ‖^3)) := by
          gcongr
      _ = 32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10 * ‖τ‖^6 := by ring
  -- (1/6)·L·S_i bounds.
  have hL_eq_inv : ((6 : ℝ)⁻¹) = 1/6 := by norm_num
  -- Bound (1/6) · L · S1 ≤ K4_1 · ‖τ‖^5
  have hT4_1 : (6 : ℝ)⁻¹ *
               (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
               (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
                (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                 10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) ≤
               ((1/6) * 40002 * (4*pn + qn) * s *
                 (16 * 10000000 * pn * qn^5 * s^6)) * ‖τ‖^5 := by
    have hLS1_le : (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
                   (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
                    (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                     10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) ≤
                   (40002 * (4*pn + qn) * s * ‖τ‖) *
                    (16 * 10000000 * pn * qn^5 * s^6 * ‖τ‖^4) := by
      have hS1_nn : 0 ≤ 2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
                        (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                         10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by
        positivity
      gcongr
    have hexpand : (40002 * (4*pn + qn) * s * ‖τ‖) *
                   (16 * 10000000 * pn * qn^5 * s^6 * ‖τ‖^4) =
                   (40002 * (4*pn + qn) * s * (16 * 10000000 * pn * qn^5 * s^6)) * ‖τ‖^5 := by
      ring
    rw [hL_eq_inv]
    have h_assoc : (1/6 : ℝ) *
         (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
          ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
         (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
          (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
           10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) =
         (1/6 : ℝ) *
         ((‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
           ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
          (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
           (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))) := by ring
    rw [h_assoc]
    have hsix_nn : (0:ℝ) ≤ 1/6 := by norm_num
    calc (1/6 : ℝ) *
         ((‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
           ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
          (2 * ‖((4 * p * τ : 𝕂)) • (A + B)‖ *
           (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
            10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)))
        ≤ (1/6 : ℝ) * ((40002 * (4*pn + qn) * s * ‖τ‖) *
                       (16 * 10000000 * pn * qn^5 * s^6 * ‖τ‖^4)) :=
          mul_le_mul_of_nonneg_left hLS1_le hsix_nn
      _ = ((1/6) * 40002 * (4*pn + qn) * s *
            (16 * 10000000 * pn * qn^5 * s^6)) * ‖τ‖^5 := by rw [hexpand]; ring
  have hT4_2 : (6 : ℝ)⁻¹ *
               (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
               (2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
                (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                      10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))) ≤
               ((1/6) * 40002 * (4*pn + qn) * s *
                 (16 * 10000000 * pn^5 * qn * s^6)) * ‖τ‖^5 := by
    have hLS2_le : (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
                   (2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
                    (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                          10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))) ≤
                   (40002 * (4*pn + qn) * s * ‖τ‖) *
                    (16 * 10000000 * pn^5 * qn * s^6 * ‖τ‖^4) := by
      have hS2_nn : 0 ≤ 2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
                        (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                              10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) := by
        positivity
      gcongr
    have hexpand : (40002 * (4*pn + qn) * s * ‖τ‖) *
                   (16 * 10000000 * pn^5 * qn * s^6 * ‖τ‖^4) =
                   (40002 * (4*pn + qn) * s * (16 * 10000000 * pn^5 * qn * s^6)) * ‖τ‖^5 := by
      ring
    rw [hL_eq_inv]
    have h_assoc : (1/6 : ℝ) *
         (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
          ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
         (2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
          (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))) =
         (1/6 : ℝ) *
         ((‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
           ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
          (2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
           (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                 10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)))) := by ring
    rw [h_assoc]
    have hsix_nn : (0:ℝ) ≤ 1/6 := by norm_num
    calc (1/6 : ℝ) *
         ((‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
           ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
          (2 * ‖(((1 - 4 * p) * τ : 𝕂)) • (A + B)‖ *
           (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                 10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))))
        ≤ (1/6 : ℝ) * ((40002 * (4*pn + qn) * s * ‖τ‖) *
                       (16 * 10000000 * pn^5 * qn * s^6 * ‖τ‖^4)) :=
          mul_le_mul_of_nonneg_left hLS2_le hsix_nn
      _ = ((1/6) * 40002 * (4*pn + qn) * s *
            (16 * 10000000 * pn^5 * qn * s^6)) * ‖τ‖^5 := by rw [hexpand]; ring
  have hT4_3 : (6 : ℝ)⁻¹ *
               (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
               (2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                          10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
                (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                 10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) ≤
               ((1/6) * 40002 * (4*pn + qn) * s *
                 (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10)) * ‖τ‖^5 := by
    have hLS3_le : (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
                    ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
                   (2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                              10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
                    (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                     10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) ≤
                   (40002 * (4*pn + qn) * s * ‖τ‖) *
                    (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10 * ‖τ‖^6) := by
      have hS3_nn : 0 ≤ 2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                                  10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
                        (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                         10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5) := by
        positivity
      gcongr
    have hbig_pos : 0 ≤ 40002 * (4*pn + qn) * s *
                       (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10) := by positivity
    have hLS3_bnd' : (40002 * (4*pn + qn) * s * ‖τ‖) *
                     (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10 * ‖τ‖^6) ≤
                     40002 * (4*pn + qn) * s *
                     (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10) * ‖τ‖^5 := by
      have heq : (40002 * (4*pn + qn) * s * ‖τ‖) *
                 (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10 * ‖τ‖^6) =
                 40002 * (4*pn + qn) * s *
                 (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10) * ‖τ‖^7 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hτ7_le_5 hbig_pos
    rw [hL_eq_inv]
    have h_combined :
        (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
         ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
        (2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                   10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
         (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) ≤
        40002 * (4*pn + qn) * s *
        (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10) * ‖τ‖^5 :=
      le_trans hLS3_le hLS3_bnd'
    have h_assoc : (1/6 : ℝ) *
        (‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
         ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
        (2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                   10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
         (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) =
        (1/6 : ℝ) *
        ((‖(4 : 𝕂) • strangBlock_log 𝕂 A B p τ‖ +
          ‖strangBlock_log 𝕂 A B (1 - 4 * p) τ‖) *
         (2 * (4 * (‖(p * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
                    10000000 * (‖(p * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5)) *
          (‖((1 - 4 * p) * τ : 𝕂)‖ ^ 3 * (‖A‖ + ‖B‖) ^ 3 +
           10000000 * (‖((1 - 4 * p) * τ : 𝕂)‖ * (‖A‖ + ‖B‖)) ^ 5))) := by ring
    have heq_target :
        ((1/6) * 40002 * (4*pn + qn) * s *
          (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10)) * ‖τ‖^5 =
        (1/6 : ℝ) * (40002 * (4*pn + qn) * s *
          (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10) * ‖τ‖^5) := by ring
    rw [h_assoc, heq_target]
    exact mul_le_mul_of_nonneg_left h_combined (by norm_num : (0:ℝ) ≤ 1/6)
  -- Combine T1, T2, T3, T4_1, T4_2, T4_3 into the final bound.
  linarith [hT1, hT2, hT3, hT4_1, hT4_2, hT4_3]

include 𝕂 in
theorem suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic
    (A B : 𝔸) (p : 𝕂) (_hSuzuki : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : 𝕂, ‖τ‖ < δ →
      suzuki5_bch_M4b_RHS 𝕂 A B p τ ≤ K * ‖τ‖ ^ 5 := by
  -- Background constants ≥ 1.
  set pn : ℝ := ‖p‖ + 1 with hpn_def
  set qn : ℝ := ‖((1 : 𝕂) - 4 * p)‖ + 1 with hqn_def
  set s  : ℝ := ‖A‖ + ‖B‖ + 1 with hs_def
  have hpn_ge : (1:ℝ) ≤ pn := by rw [hpn_def]; linarith [norm_nonneg p]
  have hqn_ge : (1:ℝ) ≤ qn := by
    rw [hqn_def]; linarith [norm_nonneg ((1 : 𝕂) - 4 * p)]
  have hs_ge  : (1:ℝ) ≤ s  := by
    rw [hs_def]; linarith [norm_nonneg A, norm_nonneg B]
  have hp_le : ‖p‖ ≤ pn := by rw [hpn_def]; linarith
  have hq_le : ‖((1 : 𝕂) - 4 * p)‖ ≤ qn := by rw [hqn_def]; linarith
  have hAB_le : ‖A‖ + ‖B‖ ≤ s := by rw [hs_def]; linarith
  refine ⟨1 / (5 * pn * qn * s), by positivity,
          4 * 10000000 * pn^5 * s^5
          + 10000000 * qn^5 * s^5
          + 10000000 * 40002^5 * (4*pn + qn)^5 * s^5
          + (1/6) * 40002 * (4*pn + qn) * s *
              (16 * 10000000 * pn * qn^5 * s^6)
          + (1/6) * 40002 * (4*pn + qn) * s *
              (16 * 10000000 * pn^5 * qn * s^6)
          + (1/6) * 40002 * (4*pn + qn) * s *
              (32 * 10000000 * 10000000 * pn^5 * qn^5 * s^10),
          by positivity, ?_⟩
  intro τ hτ_lt
  exact suzuki5_bch_M4b_RHS_le_t5_aux A B p τ pn qn s
        hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt

/-! ### M6 main theorem: Trotter h4 bound for iterated Suzuki-5

Combining `s4Func_eq_exp_nsmul` (rewriting the iterated product as a single
exponential), exp-Lipschitz `norm_exp_add_sub_exp_le`, and the scaled M4b
bound `norm_nsmul_suzuki5_bch_sub_smul_le_of_IsSuzukiCubic`, we obtain the
Trotter h4 bound

  ‖s4Func A B p (t/n) n - exp(t•(A+B))‖ ≤ ‖δ‖ · exp(‖t•V‖ + ‖δ‖)

where `δ = n • (suzuki5_bch A B p (t/n) - (t/n) • (A+B))` is the cumulative
BCH error after n Suzuki steps. Under `IsSuzukiCubic p`, `‖δ‖ = O(|t|⁵·s⁵/n⁴)`
(from scaled M4b with τ = t/n), closing the O(1/n⁴) convergence rate.
-/

include 𝕂 in
/-- **M6 (exp-Lipschitz form)**: the iterated Suzuki-5 product is close to
`exp(t•(A+B))` with error bounded by the cumulative BCH discrepancy times an
exp-Lipschitz factor. This reduces Trotter h4 to the scaled M4b bound.

Strategy:
1. `s4Func A B p (t/n) n = exp(n • suzuki5_bch A B p (t/n))` via M2b round-trip.
2. `n • suzuki5_bch = t • V + δ` where `δ = n • (suzuki5_bch - (t/n) • V)`.
3. Apply `norm_exp_add_sub_exp_le`. -/
theorem norm_s4Func_sub_exp_le (A B : 𝔸) (p t : 𝕂) (n : ℕ) (hn : n ≠ 0)
    (hR : suzuki5ArgNormBound A B p (t / n) < Real.log 2) :
    ‖s4Func 𝕂 A B p (t / n) n - exp (t • (A + B))‖ ≤
      ‖(n : 𝕂) • (suzuki5_bch 𝕂 A B p (t / n) - (t / n) • (A + B))‖ *
      Real.exp (‖t • (A + B)‖ +
        ‖(n : 𝕂) • (suzuki5_bch 𝕂 A B p (t / n) - (t / n) • (A + B))‖) := by
  have hn_ne : (n : 𝕂) ≠ 0 := by exact_mod_cast hn
  -- Step 1: s4Func = exp((n : 𝕂) • suzuki5_bch)
  rw [s4Func_eq_exp_nsmul (𝕂 := 𝕂) A B p (t / n) n hR]
  -- Step 2: decompose (n : 𝕂) • Z = t • V + δ where δ := (n : 𝕂) • (Z - (t/n)•V)
  set Z := suzuki5_bch 𝕂 A B p (t / n) with hZ_def
  set V := A + B with hV_def
  set δ := (n : 𝕂) • (Z - (t / n) • V) with hδ_def
  have hcast : (n : 𝕂) * (t / n) = t := by field_simp
  have h_decomp : (n : 𝕂) • Z = t • V + δ := by
    rw [hδ_def, smul_sub, smul_smul, hcast]
    abel
  rw [h_decomp]
  exact norm_exp_add_sub_exp_le (𝕂 := 𝕂) (t • V) δ

include 𝕂 in
/-- **M6 Trotter h4 bound (IsSuzukiCubic form)**: combining M6 with the scaled M4b
bound yields an explicit O(1/n⁴) convergence rate for the Suzuki-5 splitting.

The bound is

  ‖s4Func A B p (t/n) n - exp(t•(A+B))‖ ≤ ‖δ‖ · exp(‖t•V‖ + ‖δ‖),  ‖δ‖ ≤ n · M4b

and with τ = t/n, `n · M4b = K(p) · |t|⁵ · s⁵ / n⁴` (after tracking constants). -/
theorem norm_s4Func_sub_exp_le_of_IsSuzukiCubic (A B : 𝔸) (p t : 𝕂) (n : ℕ)
    (hn : n ≠ 0)
    (hSuzuki : IsSuzukiCubic p)
    (hR : suzuki5ArgNormBound A B p (t / n) < Real.log 2)
    (hp : ‖(p * (t / n)) • A‖ + ‖(p * (t / n)) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * (t / n)) • A‖ + ‖((1 - 4 * p) * (t / n)) • B‖ < 1 / 4)
    (hreg : ‖(4 : 𝕂) • strangBlock_log 𝕂 A B p (t / n)‖ +
            ‖strangBlock_log 𝕂 A B (1 - 4 * p) (t / n)‖ < 1 / 4)
    (hZ1 : ‖suzuki5_bch 𝕂 A B p (t / n)‖ < Real.log 2)
    (hZ2 : ‖bch (𝕂 := 𝕂)
      (bch (𝕂 := 𝕂)
        ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p (t / n)))
        (strangBlock_log 𝕂 A B (1 - 4 * p) (t / n)))
      ((2 : 𝕂)⁻¹ • ((4 : 𝕂) • strangBlock_log 𝕂 A B p (t / n)))‖ < Real.log 2) :
    ‖s4Func 𝕂 A B p (t / n) n - exp (t • (A + B))‖ ≤
      ((n : ℝ) * suzuki5_bch_M4b_RHS 𝕂 A B p (t / n)) *
      Real.exp (‖t • (A + B)‖ +
        (n : ℝ) * suzuki5_bch_M4b_RHS 𝕂 A B p (t / n)) := by
  -- Apply M6 exp-Lipschitz form
  have h_m6 := norm_s4Func_sub_exp_le (𝕂 := 𝕂) A B p t n hn hR
  -- Bound ‖δ‖ via scaled M4b
  have h_scaled_m4b := norm_nsmul_suzuki5_bch_sub_smul_le_of_IsSuzukiCubic
    (𝕂 := 𝕂) A B p (t / n) n hSuzuki hR hp h1m4p hreg hZ1 hZ2
  -- Final bound: combine via monotonicity of exp
  set δ_norm := ‖(n : 𝕂) • (suzuki5_bch 𝕂 A B p (t / n) -
    (t / n) • (A + B))‖ with hδ_norm_def
  set M4b_bound := (n : ℝ) * suzuki5_bch_M4b_RHS 𝕂 A B p (t / n)
    with hM4b_bound_def
  have hδ_le : δ_norm ≤ M4b_bound := h_scaled_m4b
  have hδ_nn : 0 ≤ δ_norm := norm_nonneg _
  have hExp_pos : 0 < Real.exp (‖t • (A + B)‖ + δ_norm) := Real.exp_pos _
  have hExp_le :
      Real.exp (‖t • (A + B)‖ + δ_norm) ≤
      Real.exp (‖t • (A + B)‖ + M4b_bound) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hM4b_nn : 0 ≤ M4b_bound := le_trans hδ_nn hδ_le
  calc ‖s4Func 𝕂 A B p (t / n) n - exp (t • (A + B))‖
      ≤ δ_norm * Real.exp (‖t • (A + B)‖ + δ_norm) := h_m6
    _ ≤ M4b_bound * Real.exp (‖t • (A + B)‖ + M4b_bound) := by
        apply mul_le_mul hδ_le hExp_le hExp_pos.le hM4b_nn
