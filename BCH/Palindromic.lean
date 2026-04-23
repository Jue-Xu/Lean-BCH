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

end

end BCH
