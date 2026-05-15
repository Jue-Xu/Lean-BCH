/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH Remainder Bounds: T_k norm bounds + sextic/septic/octic remainder + symmetric BCH

This file extends `BCH.SmallSDischarge` with the per-degree T_k norm bounds,
P²/PzP/P³-residual cluster bounds, the public order-k BCH remainder bounds
(`norm_bch_sextic_remainder_le` through `norm_bch_octic_remainder_le`), and
the symmetric BCH cubic/quintic/septic polynomial-form definitions and norm
bounds.

Split from `BCH/SmallSDischarge.lean` (which formerly held both the algebraic
infrastructure and the heavy remainder-bound proofs) to enable parallel
compilation: edits to bottom-half code (T_k bounds, remainder bounds,
symmetric BCH) skip the expensive `pieceB_*_decomp` rebuilds in the
top half. -/

import BCH.SmallSDischarge
import Mathlib.Algebra.Lie.OfAssociative

namespace BCH

noncomputable section

open scoped Nat
open NormedSpace Topology Finset

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]


/-- Norm bound for the RHS of `I2_octic_residual_decomp_eq`.

Given precomputed bounds for the 4 input pieces (with parameterized constants
K_PmT5, K_P2', K_PzP', K_P3'), bounds the RHS by
`(3·K_PmT5 + 2·K_P2' + K_PzP' + K_P3')·s⁸`.

Per-term contributions:
- 3 weight-1 (P-T₂-T₃-T₄-T₅) middle terms: each ≤ K_PmT5·s⁸ (using s²·K·s⁶ etc.).
- 2 compound `z·(P²-T₂²-T₂T₃-T₃T₂-T₂T₄-T₃²-T₄T₂)`-style terms: each ≤ K_P2'·s⁸.
- 1 sandwich `PzP-T₂zT₂-T₂zT₃-T₃zT₂-T₂zT₄-T₃zT₃-T₄zT₂` term: ≤ K_PzP'·s⁸.
- 1 (P³-T₂³-T₂²T₃-T₂T₃T₂-T₃T₂²) term: ≤ K_P3'·s⁸.

The user supplies the parameterized bounds; this wrapper combines via
triangle inequality. Analog of `norm_I2_septic_residual_RHS_le` at one
degree higher. -/
private theorem norm_I2_octic_residual_RHS_le (z P T₂ T₃ T₄ T₅ : 𝔸)
    {s K_PmT5 K_P2' K_PzP' K_P3' : ℝ} (hs_nn : 0 ≤ s)
    (hK_PmT5_nn : 0 ≤ K_PmT5) (hK_P2'_nn : 0 ≤ K_P2')
    (hK_PzP'_nn : 0 ≤ K_PzP') (hK_P3'_nn : 0 ≤ K_P3')
    (hz : ‖z‖ ≤ s)
    (hPmT5_le : ‖P - T₂ - T₃ - T₄ - T₅‖ ≤ K_PmT5 * s ^ 6)
    (hP2'_le :
        ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
            T₂ * T₄ - T₃ * T₃ - T₄ * T₂‖ ≤ K_P2' * s ^ 7)
    (hPzP'_le :
        ‖P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
            T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂‖ ≤ K_PzP' * s ^ 8)
    (hP3'_le :
        ‖P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2‖ ≤
            K_P3' * s ^ 8) :
    ‖z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) + z * (P - T₂ - T₃ - T₄ - T₅) * z +
      (P - T₂ - T₃ - T₄ - T₅) * z ^ 2 +
      z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
           T₂ * T₄ - T₃ * T₃ - T₄ * T₂) +
      (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
           T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂) +
      (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
           T₂ * T₄ - T₃ * T₃ - T₄ * T₂) * z +
      (P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2)‖ ≤
      (3 * K_PmT5 + 2 * K_P2' + K_PzP' + K_P3') * s ^ 8 := by
  -- Bound each of the 7 outer terms.
  have h1 : ‖z ^ 2 * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 2 * (K_PmT5 * s ^ 6) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃ - T₄ - T₅‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P - T₂ - T₃ - T₄ - T₅‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (K_PmT5 * s ^ 6) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz 2)
            hPmT5_le (norm_nonneg _) (by positivity)
  have h2 : ‖z * (P - T₂ - T₃ - T₄ - T₅) * z‖ ≤ s * (K_PmT5 * s ^ 6) * s :=
    calc _ ≤ ‖z * (P - T₂ - T₃ - T₄ - T₅)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃ - T₄ - T₅‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (K_PmT5 * s ^ 6)) * s := by
          apply mul_le_mul _ hz (norm_nonneg _) (by positivity)
          exact mul_le_mul hz hPmT5_le (norm_nonneg _) (by positivity)
  have h3 : ‖(P - T₂ - T₃ - T₄ - T₅) * z ^ 2‖ ≤ (K_PmT5 * s ^ 6) * s ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄ - T₅‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃ - T₄ - T₅‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (K_PmT5 * s ^ 6) * s ^ 2 :=
          mul_le_mul hPmT5_le (pow_le_pow_left₀ (norm_nonneg _) hz 2)
            (by positivity) (by positivity)
  have h4 : ‖z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
                  T₂ * T₄ - T₃ * T₃ - T₄ * T₂)‖ ≤ s * (K_P2' * s ^ 7) :=
    calc _ ≤ ‖z‖ * ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
                T₂ * T₄ - T₃ * T₃ - T₄ * T₂‖ := norm_mul_le _ _
      _ ≤ s * (K_P2' * s ^ 7) := mul_le_mul hz hP2'_le (norm_nonneg _) (by positivity)
  have h6 : ‖(P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
              T₂ * T₄ - T₃ * T₃ - T₄ * T₂) * z‖ ≤ (K_P2' * s ^ 7) * s :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
                T₂ * T₄ - T₃ * T₃ - T₄ * T₂‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (K_P2' * s ^ 7) * s := mul_le_mul hP2'_le hz (norm_nonneg _) (by positivity)
  -- Sum 7 terms via triangle inequality (6 norm_add_le).
  have ha1 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) +
    z * (P - T₂ - T₃ - T₄ - T₅) * z +
    (P - T₂ - T₃ - T₄ - T₅) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂) +
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
         T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂) +
    (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂) * z)
    (P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2)
  have ha2 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) +
    z * (P - T₂ - T₃ - T₄ - T₅) * z +
    (P - T₂ - T₃ - T₄ - T₅) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂) +
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
         T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂))
    ((P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂) * z)
  have ha3 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) +
    z * (P - T₂ - T₃ - T₄ - T₅) * z +
    (P - T₂ - T₃ - T₄ - T₅) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂))
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
         T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂)
  have ha4 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) +
    z * (P - T₂ - T₃ - T₄ - T₅) * z +
    (P - T₂ - T₃ - T₄ - T₅) * z ^ 2)
    (z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
          T₂ * T₄ - T₃ * T₃ - T₄ * T₂))
  have ha5 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) +
    z * (P - T₂ - T₃ - T₄ - T₅) * z)
    ((P - T₂ - T₃ - T₄ - T₅) * z ^ 2)
  have ha6 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄ - T₅))
    (z * (P - T₂ - T₃ - T₄ - T₅) * z)
  -- Sum: 3·K_PmT5 + 2·K_P2' + K_PzP' + K_P3' (in units of s⁸).
  nlinarith [pow_nonneg hs_nn 8]

/-- Norm bound `‖P - T₂ - T₃‖ ≤ 5·s⁴` where P = exp(a)*exp(b)-1-(a+b),
T₂ = ab+½a²+½b², T₃ = ⅙a³+½a²b+½ab²+⅙b³. Algebraic identity:
`P - T₂ - T₃ = F₁ + F₂ + a·E₂ + E₁·b + D₁·D₂` where each piece has deg-4+
structure. -/
private theorem norm_P_sub_T2_sub_T3_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs34 : s < 3 / 4) (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3)‖ ≤ 5 * s ^ 4 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hs56 : s < 5 / 6 := by linarith
  -- Set up D, E, F variables
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  -- Algebraic identity: P - T₂ - T₃ = F₁ + F₂ + a·E₂ + E₁·b + D₁·D₂
  have h_alg : exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) =
      F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ := by
    simp only [hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def]
    noncomm_ring
  rw [h_alg]
  -- Bounds for D, E, F
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖α‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hα_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDa_nn,
         Real.norm_eq_abs, abs_of_nonneg hα_nn] at h
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖β‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hβ_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDb_nn,
         Real.norm_eq_abs, abs_of_nonneg hβ_nn] at h
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- Component bounds
  have hF₁s : ‖F₁‖ ≤ s ^ 4 := le_trans (le_trans hF₁_le hFa4)
    (pow_le_pow_left₀ hα_nn hα_le 4)
  have hF₂s : ‖F₂‖ ≤ s ^ 4 := le_trans (le_trans hF₂_le hFb4)
    (pow_le_pow_left₀ hβ_nn hβ_le 4)
  have h_aE₂ : ‖a * E₂‖ ≤ s ^ 4 :=
    calc _ ≤ ‖a‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 3 := mul_le_mul_of_nonneg_left
          (le_trans hE₂_le hEb3) hα_nn
      _ ≤ s * s ^ 3 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 3)
          (by positivity) hs_nn
      _ = s ^ 4 := by ring
  have h_E₁b : ‖E₁ * b‖ ≤ s ^ 4 :=
    calc _ ≤ ‖E₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β := mul_le_mul (le_trans hE₁_le hEa3) le_rfl
          hβ_nn (by positivity)
      _ ≤ s ^ 3 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          hβ_le (by positivity) (by positivity)
      _ = s ^ 4 := by ring
  have h_D₁D₂ : ‖D₁ * D₂‖ ≤ s ^ 4 :=
    calc _ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 2 := mul_le_mul (le_trans hD₁_le hDa2)
          (le_trans hD₂_le hDb2) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 4 := by ring
  -- Triangle inequality
  have ha1 := norm_add_le (F₁ + F₂ + a * E₂ + E₁ * b) (D₁ * D₂)
  have ha2 := norm_add_le (F₁ + F₂ + a * E₂) (E₁ * b)
  have ha3 := norm_add_le (F₁ + F₂) (a * E₂)
  have ha4 := norm_add_le F₁ F₂
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **P − T₂ − T₃ − T₄ algebraic decomposition**: pure ring identity in
`(ea, eb, a, b)` expressing `P - T₂ - T₃ - T₄` as a sum of 7 deg-5+ terms.
Used in `norm_P_sub_T2_sub_T3_sub_T4_le`.

Derived from `R_eq_neg_deg5_residual` via the auxiliary fact
`P - T₂ = E₁ + E₂ + Q` (which expands `P - T₂` as the deg-3+ part). -/
private theorem P_sub_T2_sub_T3_sub_T4_decomp_eq (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    ea * eb - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) =
    G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂) := by
  have hR := R_eq_neg_deg5_residual 𝕂 ea eb a b
  dsimp only at hR ⊢
  -- The bridge from hR (T₃ - E₁ - E₂ - Q + T₄ = -(...)) to our identity
  -- (P - T₂ - T₃ - T₄ = ...) requires the auxiliary `P - T₂ = E₁ + E₂ + Q`.
  -- We embed this as a single `linear_combination` step.
  linear_combination (norm := (simp only [smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul]; noncomm_ring))
    -hR

/-- Norm bound `‖P - T₂ - T₃ - T₄‖ ≤ 6·s⁵` where P = exp(a)·exp(b)-1-(a+b) and
T₂, T₃, T₄ are the deg-2, 3, 4 contributions to P. Algebraic identity:
`P - T₂ - T₃ - T₄ = G₁ + G₂ + a·F₂ + F₁·b + E₁·E₂ + ½·E₁·b² + ½·a²·E₂` where
each piece has deg-5+ structure. Used for the I2 septic residual bound. -/
private theorem norm_P_sub_T2_sub_T3_sub_T4_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs34 : s < 3 / 4) (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4)‖ ≤ 6 * s ^ 5 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hs56 : s < 5 / 6 := by linarith
  -- Set up D, E, F, G variables
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set G₁ := F₁ - (24 : 𝕂)⁻¹ • a ^ 4 with hG₁_def
  set G₂ := F₂ - (24 : 𝕂)⁻¹ • b ^ 4 with hG₂_def
  -- Algebraic identity:
  -- P - T₂ - T₃ - T₄ = G₁ + G₂ + a·F₂ + F₁·b + E₁·E₂ + (1/2)·E₁·b² + (1/2)·a²·E₂
  have h_alg : exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) =
      G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂) := by
    have h := P_sub_T2_sub_T3_sub_T4_decomp_eq 𝕂 (exp a) (exp b) a b
    simp only [hG₁_def, hG₂_def, hF₁_def, hF₂_def, hE₁_def, hE₂_def,
      hD₁_def, hD₂_def] at h
    convert h using 1
  rw [h_alg]
  -- Bounds for E, F, G via existing exp tail helpers
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hG₁_le : ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hG₂_le : ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  -- Real bound transitions
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hGa5 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 ≤ α ^ 5 :=
    real_exp_fifth_order_le_quintic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hGb5 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 ≤ β ^ 5 :=
    real_exp_fifth_order_le_quintic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- Component bounds (each of the 7 RHS pieces ≤ s⁵ or s⁶)
  have hG₁s : ‖G₁‖ ≤ s ^ 5 := le_trans (le_trans hG₁_le hGa5)
    (pow_le_pow_left₀ hα_nn hα_le 5)
  have hG₂s : ‖G₂‖ ≤ s ^ 5 := le_trans (le_trans hG₂_le hGb5)
    (pow_le_pow_left₀ hβ_nn hβ_le 5)
  have h_aF₂ : ‖a * F₂‖ ≤ s ^ 5 :=
    calc _ ≤ ‖a‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 4 := mul_le_mul_of_nonneg_left
          (le_trans hF₂_le hFb4) hα_nn
      _ ≤ s * s ^ 4 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 4)
          (by positivity) hs_nn
      _ = s ^ 5 := by ring
  have h_F₁b : ‖F₁ * b‖ ≤ s ^ 5 :=
    calc _ ≤ ‖F₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β := mul_le_mul (le_trans hF₁_le hFa4) le_rfl
          hβ_nn (by positivity)
      _ ≤ s ^ 4 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          hβ_le (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  -- E₁·E₂ ≤ s⁶ (deg-3 × deg-3)
  have h_E₁E₂ : ‖E₁ * E₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖E₁‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 3 := mul_le_mul (le_trans hE₁_le hEa3)
          (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  -- (1/2)·E₁·b² ≤ s⁵/2
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_E₁b2_norm : ‖E₁ * b ^ 2‖ ≤ s ^ 5 :=
    calc _ ≤ ‖E₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖E₁‖ * ‖b‖ ^ 2 := by gcongr; exact norm_pow_le b 2
      _ ≤ α ^ 3 * β ^ 2 := mul_le_mul (le_trans hE₁_le hEa3) le_rfl
          (by positivity) (by positivity)
      _ ≤ s ^ 3 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have h_E₁b2_smul : ‖(2 : 𝕂)⁻¹ • (E₁ * b ^ 2)‖ ≤ s ^ 5 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖E₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 5 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_E₁b2_norm (by norm_num)
      _ = s ^ 5 / 2 := by ring
  -- (1/2)·a²·E₂ ≤ s⁵/2
  have h_a2E₂_norm : ‖a ^ 2 * E₂‖ ≤ s ^ 5 :=
    calc _ ≤ ‖a ^ 2‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ ‖a‖ ^ 2 * ‖E₂‖ := by gcongr; exact norm_pow_le a 2
      _ ≤ α ^ 2 * β ^ 3 := mul_le_mul le_rfl
          (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have h_a2E₂_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * E₂)‖ ≤ s ^ 5 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * E₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 5 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2E₂_norm (by norm_num)
      _ = s ^ 5 / 2 := by ring
  -- Triangle inequality. Total ≤ 4·s⁵ + s⁶ + s⁵ ≤ 5·s⁵ + s⁵ = 6·s⁵ (using s⁶ ≤ s⁵).
  have hs1 : s ≤ 1 := by linarith
  have h_s6 : s ^ 6 ≤ s ^ 5 := by
    have h_eq : s ^ 6 = s ^ 5 * s := by ring
    rw [h_eq]
    nlinarith [pow_nonneg hs_nn 5]
  have ha1 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
    (2 : 𝕂)⁻¹ • (E₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * E₂))
  have ha2 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂)
    ((2 : 𝕂)⁻¹ • (E₁ * b ^ 2))
  have ha3 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b) (E₁ * E₂)
  have ha4 := norm_add_le (G₁ + G₂ + a * F₂) (F₁ * b)
  have ha5 := norm_add_le (G₁ + G₂) (a * F₂)
  have ha6 := norm_add_le G₁ G₂
  linarith [pow_nonneg hs_nn 5, pow_nonneg hs_nn 6]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Algebraic decomposition for `P - T₂ - T₃ - T₄ - T₅`**: pure ring identity in
`(ea, eb, a, b)` expressing `P - T₂ - T₃ - T₄ - T₅` as a sum of 7 deg-6+ terms.
Used in `norm_P_sub_T2_sub_T3_sub_T4_sub_T5_le`. Deg-9 analog of
`P_sub_T2_sub_T3_sub_T4_decomp_eq` at one degree higher.

Derived from `R_plus_T5_eq_neg_deg6_residual` via the auxiliary fact
`P - T₂ = E₁ + E₂ + Q` (which expands `P - T₂` as the deg-3+ part). -/
private theorem P_sub_T2_sub_T3_sub_T4_sub_T5_decomp_eq (𝕂 : Type*) [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    ea * eb - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) =
    H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (F₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) := by
  have hR := R_plus_T5_eq_neg_deg6_residual 𝕂 ea eb a b
  dsimp only at hR ⊢
  linear_combination (norm := (simp only [smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul]; noncomm_ring))
    -hR

/-- Norm bound `‖P - T₂ - T₃ - T₄ - T₅‖ ≤ 6·s⁶` where P = exp(a)·exp(b)-1-(a+b)
and T₂, T₃, T₄, T₅ are the deg-2..5 contributions to P. Algebraic identity:
`P - T₂ - T₃ - T₄ - T₅ = H₁ + H₂ + a·G₂ + G₁·b + E₁·E₂ + ½·F₁·b² + ½·a²·F₂`
where each piece has deg-6+ structure. Used for the I2 octic residual bound
(provides K_PmT5 = 6 input for `norm_I2_octic_residual_RHS_le`). -/
private theorem norm_P_sub_T2_sub_T3_sub_T4_sub_T5_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs34 : s < 3 / 4) (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5)‖ ≤ 6 * s ^ 6 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hs56 : s < 5 / 6 := by linarith
  -- Set up D, E, F, G, H variables
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set G₁ := F₁ - (24 : 𝕂)⁻¹ • a ^ 4 with hG₁_def
  set G₂ := F₂ - (24 : 𝕂)⁻¹ • b ^ 4 with hG₂_def
  set H₁ := G₁ - (120 : 𝕂)⁻¹ • a ^ 5 with hH₁_def
  set H₂ := G₂ - (120 : 𝕂)⁻¹ • b ^ 5 with hH₂_def
  -- Algebraic identity
  have h_alg : exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) =
      H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (F₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) := by
    have h := P_sub_T2_sub_T3_sub_T4_sub_T5_decomp_eq 𝕂 (exp a) (exp b) a b
    simp only [hH₁_def, hH₂_def, hG₁_def, hG₂_def, hF₁_def, hF₂_def,
      hE₁_def, hE₂_def, hD₁_def, hD₂_def] at h
    convert h using 1
  rw [h_alg]
  -- Real tail bounds
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hG₁_le : ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hG₂_le : ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hH₁_le : ‖H₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hH₂_le : ‖H₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  -- Real bound transitions
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hGa5 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 ≤ α ^ 5 :=
    real_exp_fifth_order_le_quintic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hGb5 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 ≤ β ^ 5 :=
    real_exp_fifth_order_le_quintic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hHa6 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 ≤ α ^ 6 :=
    real_exp_sixth_order_le_sextic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hHb6 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 ≤ β ^ 6 :=
    real_exp_sixth_order_le_sextic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- Component bounds (each of the 7 RHS pieces ≤ s⁶)
  have hH₁s : ‖H₁‖ ≤ s ^ 6 := le_trans (le_trans hH₁_le hHa6)
    (pow_le_pow_left₀ hα_nn hα_le 6)
  have hH₂s : ‖H₂‖ ≤ s ^ 6 := le_trans (le_trans hH₂_le hHb6)
    (pow_le_pow_left₀ hβ_nn hβ_le 6)
  have h_aG₂ : ‖a * G₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖a‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 5 := mul_le_mul_of_nonneg_left
          (le_trans hG₂_le hGb5) hα_nn
      _ ≤ s * s ^ 5 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 5)
          (by positivity) hs_nn
      _ = s ^ 6 := by ring
  have h_G₁b : ‖G₁ * b‖ ≤ s ^ 6 :=
    calc _ ≤ ‖G₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β := mul_le_mul (le_trans hG₁_le hGa5) le_rfl
          hβ_nn (by positivity)
      _ ≤ s ^ 5 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          hβ_le (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_E₁E₂ : ‖E₁ * E₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖E₁‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 3 := mul_le_mul (le_trans hE₁_le hEa3)
          (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_F₁b2_norm : ‖F₁ * b ^ 2‖ ≤ s ^ 6 :=
    calc _ ≤ ‖F₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖F₁‖ * ‖b‖ ^ 2 := by gcongr; exact norm_pow_le b 2
      _ ≤ α ^ 4 * β ^ 2 := mul_le_mul (le_trans hF₁_le hFa4) le_rfl
          (by positivity) (by positivity)
      _ ≤ s ^ 4 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_F₁b2_smul : ‖(2 : 𝕂)⁻¹ • (F₁ * b ^ 2)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖F₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_F₁b2_norm (by norm_num)
      _ = s ^ 6 / 2 := by ring
  have h_a2F₂_norm : ‖a ^ 2 * F₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖a ^ 2‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ ‖a‖ ^ 2 * ‖F₂‖ := by gcongr; exact norm_pow_le a 2
      _ ≤ α ^ 2 * β ^ 4 := mul_le_mul le_rfl
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_a2F₂_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * F₂)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * F₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2F₂_norm (by norm_num)
      _ = s ^ 6 / 2 := by ring
  -- Triangle inequality. Total ≤ 5·s⁶ + s⁶ = 6·s⁶.
  have ha1 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂ +
    (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * F₂))
  have ha2 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂)
    ((2 : 𝕂)⁻¹ • (F₁ * b ^ 2))
  have ha3 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b) (E₁ * E₂)
  have ha4 := norm_add_le (H₁ + H₂ + a * G₂) (G₁ * b)
  have ha5 := norm_add_le (H₁ + H₂) (a * G₂)
  have ha6 := norm_add_le H₁ H₂
  linarith [pow_nonneg hs_nn 6]

set_option maxHeartbeats 1600000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Algebraic decomposition for `P - T₂ - T₃ - T₄ - T₅ - T₆`**: pure ring identity
in `(ea, eb, a, b)` expressing `P - T₂ - T₃ - T₄ - T₅ - T₆` as a sum of 9 deg-7+
terms. Used in `norm_P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_le`. Deg-10 analog of
`P_sub_T2_sub_T3_sub_T4_sub_T5_decomp_eq` at one degree higher.

Derived from `R_plus_T5_plus_T6_eq_neg_deg7_residual` via the auxiliary fact
`P - T₂ = E₁ + E₂ + Q` (which expands `P - T₂` as the deg-3+ part). -/
private theorem P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_decomp_eq (𝕂 : Type*) [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let I_a : 𝔸 := H₁ - (720 : 𝕂)⁻¹ • a ^ 6
    let I_b : 𝔸 := H₂ - (720 : 𝕂)⁻¹ • b ^ 6
    ea * eb - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) -
      ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6) =
    I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
      (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂) +
      (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) := by
  have hR := R_plus_T5_plus_T6_eq_neg_deg7_residual 𝕂 ea eb a b
  dsimp only at hR ⊢
  linear_combination (norm := (simp only [smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul]; noncomm_ring))
    -hR

set_option maxHeartbeats 1600000 in
/-- Norm bound `‖P - T₂ - T₃ - T₄ - T₅ - T₆‖ ≤ 7·s⁷` where P = exp(a)·exp(b)-1-(a+b)
and T₂..T₆ are the deg-2..6 contributions to P. Algebraic identity:
`P - T₂ - T₃ - T₄ - T₅ - T₆ = I_a + I_b + a·H₂ + H₁·b + F₁·F₂ +
  ⅙·F₁·b³ + ⅙·a³·F₂ + ½·G₁·b² + ½·a²·G₂` where each piece has deg-7+ structure.

Foundation for the future deg-9 parent T2-F7e-octic discharge (analog at one
degree higher than `norm_P_sub_T2_sub_T3_sub_T4_sub_T5_le`). -/
private theorem norm_P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_le (a b : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs34 : s < 3 / 4) (hs1 : s ≤ 1)
    (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) -
      ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6)‖ ≤ 7 * s ^ 7 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Set up D, E, F, G, H, I variables
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set G₁ := F₁ - (24 : 𝕂)⁻¹ • a ^ 4 with hG₁_def
  set G₂ := F₂ - (24 : 𝕂)⁻¹ • b ^ 4 with hG₂_def
  set H₁ := G₁ - (120 : 𝕂)⁻¹ • a ^ 5 with hH₁_def
  set H₂ := G₂ - (120 : 𝕂)⁻¹ • b ^ 5 with hH₂_def
  set I_a := H₁ - (720 : 𝕂)⁻¹ • a ^ 6 with hI_a_def
  set I_b := H₂ - (720 : 𝕂)⁻¹ • b ^ 6 with hI_b_def
  -- Algebraic identity (9 deg-7+ terms)
  have h_alg : exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) -
      ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6) =
      I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
        (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂) +
        (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) := by
    have h := P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_decomp_eq 𝕂 (exp a) (exp b) a b
    simp only [hI_a_def, hI_b_def, hH₁_def, hH₂_def, hG₁_def, hG₂_def,
      hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def] at h
    convert h using 1
  rw [h_alg]
  -- Real tail bounds for F, G, H, I_a, I_b
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hG₁_le : ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hG₂_le : ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hH₁_le : ‖H₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hH₂_le : ‖H₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hI_a_le : ‖I_a‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hI_b_le : ‖I_b‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  -- Real bound transitions
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hGa5 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 ≤ α ^ 5 :=
    real_exp_fifth_order_le_quintic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hGb5 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 ≤ β ^ 5 :=
    real_exp_fifth_order_le_quintic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hHa6 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 ≤ α ^ 6 :=
    real_exp_sixth_order_le_sextic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hHb6 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 ≤ β ^ 6 :=
    real_exp_sixth_order_le_sextic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hIa7 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 ≤ α ^ 7 :=
    real_exp_seventh_order_le_septic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hIb7 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 ≤ β ^ 7 :=
    real_exp_seventh_order_le_septic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- Component bounds (each of the 9 RHS pieces ≤ s⁷ or ≤ ½·s⁷ or ≤ ⅙·s⁷; F₁·F₂ ≤ s⁸ ≤ s⁷)
  have hI_a_s7 : ‖I_a‖ ≤ s ^ 7 := le_trans (le_trans hI_a_le hIa7)
    (pow_le_pow_left₀ hα_nn hα_le 7)
  have hI_b_s7 : ‖I_b‖ ≤ s ^ 7 := le_trans (le_trans hI_b_le hIb7)
    (pow_le_pow_left₀ hβ_nn hβ_le 7)
  have h_aH₂ : ‖a * H₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a‖ * ‖H₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 6 := mul_le_mul_of_nonneg_left
          (le_trans hH₂_le hHb6) hα_nn
      _ ≤ s * s ^ 6 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 6)
          (by positivity) hs_nn
      _ = s ^ 7 := by ring
  have h_H₁b : ‖H₁ * b‖ ≤ s ^ 7 :=
    calc _ ≤ ‖H₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 6 * β := mul_le_mul (le_trans hH₁_le hHa6) le_rfl
          hβ_nn (by positivity)
      _ ≤ s ^ 6 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 6)
          hβ_le (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_F₁F₂ : ‖F₁ * F₂‖ ≤ s ^ 8 :=
    calc _ ≤ ‖F₁‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 4 := mul_le_mul (le_trans hF₁_le hFa4)
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_F₁b3_norm : ‖F₁ * b ^ 3‖ ≤ s ^ 7 :=
    calc _ ≤ ‖F₁‖ * ‖b ^ 3‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 3 := mul_le_mul (le_trans hF₁_le hFa4) (norm_pow_le _ _)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_F₁b3_smul : ‖(6 : 𝕂)⁻¹ • (F₁ * b ^ 3)‖ ≤ s ^ 7 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖F₁ * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 7 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_F₁b3_norm (by norm_num)
      _ = s ^ 7 / 6 := by ring
  have h_a3F₂_norm : ‖a ^ 3 * F₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a ^ 3‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 4 := mul_le_mul (norm_pow_le _ _) (le_trans hF₂_le hFb4)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_a3F₂_smul : ‖(6 : 𝕂)⁻¹ • (a ^ 3 * F₂)‖ ≤ s ^ 7 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖a ^ 3 * F₂‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 7 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_a3F₂_norm (by norm_num)
      _ = s ^ 7 / 6 := by ring
  have h_G₁b2_norm : ‖G₁ * b ^ 2‖ ≤ s ^ 7 :=
    calc _ ≤ ‖G₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β ^ 2 := mul_le_mul (le_trans hG₁_le hGa5) (norm_pow_le _ _)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 5 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_G₁b2_smul : ‖(2 : 𝕂)⁻¹ • (G₁ * b ^ 2)‖ ≤ s ^ 7 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖G₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 7 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_G₁b2_norm (by norm_num)
      _ = s ^ 7 / 2 := by ring
  have h_a2G₂_norm : ‖a ^ 2 * G₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a ^ 2‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 5 := mul_le_mul (norm_pow_le _ _) (le_trans hG₂_le hGb5)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 5 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 5) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_a2G₂_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * G₂)‖ ≤ s ^ 7 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * G₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 7 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2G₂_norm (by norm_num)
      _ = s ^ 7 / 2 := by ring
  -- s⁸ ≤ s⁷ folding (uses hs1 : s ≤ 1)
  have hs8_le_s7 : s ^ 8 ≤ s ^ 7 := by
    have h : s ^ 8 = s ^ 7 * s := by ring
    rw [h]
    calc s ^ 7 * s ≤ s ^ 7 * 1 :=
          mul_le_mul_of_nonneg_left hs1 (pow_nonneg hs_nn 7)
      _ = s ^ 7 := by ring
  -- Triangle inequality. Sum: 4·s⁷ + s⁸ + 2·(s⁷/6) + 2·(s⁷/2) = 4·s⁷ + s⁸ + 4·s⁷/3
  -- ≤ 4·s⁷ + s⁷ + 1.34·s⁷ = 6.34·s⁷ ≤ 7·s⁷.
  have ha1 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂) +
    (2 : 𝕂)⁻¹ • (G₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * G₂))
  have ha2 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂))
    ((2 : 𝕂)⁻¹ • (G₁ * b ^ 2))
  have ha3 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (F₁ * b ^ 3)) ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂))
  have ha4 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂)
    ((6 : 𝕂)⁻¹ • (F₁ * b ^ 3))
  have ha5 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b) (F₁ * F₂)
  have ha6 := norm_add_le (I_a + I_b + a * H₂) (H₁ * b)
  have ha7 := norm_add_le (I_a + I_b) (a * H₂)
  have ha8 := norm_add_le I_a I_b
  linarith [pow_nonneg hs_nn 7]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **deg-8 P-tail decomposition (pure algebraic identity).**

`P - T₂ - T₃ - T₄ - T₅ - T₆ - T₇ = J_a + J_b + a·I_b + I_a·b + F₁·F₂ +
  ⅙·G₁·b³ + ⅙·a³·G₂ + ½·H₁·b² + ½·a²·H₂`

where `P = ea·eb - 1 - (a+b)` and each RHS piece is deg-8+ in (a,b).
Deg-8 analog of `P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_decomp_eq` (session 34)
at one degree higher.

Proof: `linear_combination -hR` from `R_plus_T5_plus_T6_plus_T7_eq_neg_deg8_residual`
+ the auxiliary identity `P - T₂ = E₁ + E₂ + Q`. -/
private theorem P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_sub_T7_decomp_eq (𝕂 : Type*)
    [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let I_a : 𝔸 := H₁ - (720 : 𝕂)⁻¹ • a ^ 6
    let I_b : 𝔸 := H₂ - (720 : 𝕂)⁻¹ • b ^ 6
    let J_a : 𝔸 := I_a - (5040 : 𝕂)⁻¹ • a ^ 7
    let J_b : 𝔸 := I_b - (5040 : 𝕂)⁻¹ • b ^ 7
    ea * eb - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) -
      ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6) -
      ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a * b ^ 6) + (5040 : 𝕂)⁻¹ • b ^ 7) =
    J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
      (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂) +
      (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) := by
  have hR := R_plus_T5_plus_T6_plus_T7_eq_neg_deg8_residual 𝕂 ea eb a b
  dsimp only at hR ⊢
  linear_combination (norm := (simp only [smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul]; noncomm_ring))
    -hR

set_option maxHeartbeats 1600000 in
/-- Norm bound `‖P - T₂ - T₃ - T₄ - T₅ - T₆ - T₇‖ ≤ 7·s⁸` where
`P = exp(a)·exp(b) - 1 - (a+b)` and T₂..T₇ are the deg-2..7 contributions to P.
Algebraic identity: each RHS piece is deg-8+ structure.

Per-term bounds (each ≤ s⁸, ≤ s⁸/2, or ≤ s⁸/6): J_a + J_b + a·I_b + I_a·b
+ F₁·F₂ contribute 5·s⁸; ⅙·G₁·b³ + ⅙·a³·G₂ contribute s⁸/3; ½·H₁·b² + ½·a²·H₂
contribute s⁸. Total ≤ 19/3·s⁸ ≈ 6.34·s⁸ ≤ 7·s⁸.

Deg-8 analog of `norm_P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_le` (session 34,
≤ 7·s⁷). Foundation for the future deg-9-parent T2-F7e-octic discharge. -/
private theorem norm_P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_sub_T7_le (a b : 𝔸)
    {s : ℝ} (hs_nn : 0 ≤ s) (hs34 : s < 3 / 4)
    (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) -
      ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6) -
      ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a * b ^ 6) + (5040 : 𝕂)⁻¹ • b ^ 7)‖ ≤ 7 * s ^ 8 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Set up D, E, F, G, H, I, J variables
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set G₁ := F₁ - (24 : 𝕂)⁻¹ • a ^ 4 with hG₁_def
  set G₂ := F₂ - (24 : 𝕂)⁻¹ • b ^ 4 with hG₂_def
  set H₁ := G₁ - (120 : 𝕂)⁻¹ • a ^ 5 with hH₁_def
  set H₂ := G₂ - (120 : 𝕂)⁻¹ • b ^ 5 with hH₂_def
  set I_a := H₁ - (720 : 𝕂)⁻¹ • a ^ 6 with hI_a_def
  set I_b := H₂ - (720 : 𝕂)⁻¹ • b ^ 6 with hI_b_def
  set J_a := I_a - (5040 : 𝕂)⁻¹ • a ^ 7 with hJ_a_def
  set J_b := I_b - (5040 : 𝕂)⁻¹ • b ^ 7 with hJ_b_def
  -- Algebraic identity (9 deg-8+ terms)
  have h_alg : exp a * exp b - 1 - (a + b) -
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) -
      ((6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4) -
      ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5) -
      ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6) -
      ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a * b ^ 6) + (5040 : 𝕂)⁻¹ • b ^ 7) =
      J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
        (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂) +
        (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) := by
    have h := P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_sub_T7_decomp_eq 𝕂 (exp a) (exp b) a b
    simp only [hJ_a_def, hJ_b_def, hI_a_def, hI_b_def, hH₁_def, hH₂_def, hG₁_def, hG₂_def,
      hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def] at h
    convert h using 1
  rw [h_alg]
  -- Real tail bounds for F, G, H, I, J
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hG₁_le : ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hG₂_le : ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hH₁_le : ‖H₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hH₂_le : ‖H₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hI_a_le : ‖I_a‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hI_b_le : ‖I_b‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hJ_a_le : ‖J_a‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 - α ^ 7 / 5040 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hJ_b_le : ‖J_b‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 - β ^ 7 / 5040 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  -- Real bound transitions
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hGa5 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 ≤ α ^ 5 :=
    real_exp_fifth_order_le_quintic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hGb5 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 ≤ β ^ 5 :=
    real_exp_fifth_order_le_quintic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hHa6 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 ≤ α ^ 6 :=
    real_exp_sixth_order_le_sextic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hHb6 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 ≤ β ^ 6 :=
    real_exp_sixth_order_le_sextic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hIa7 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 ≤ α ^ 7 :=
    real_exp_seventh_order_le_septic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hIb7 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 ≤ β ^ 7 :=
    real_exp_seventh_order_le_septic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hJa8 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 - α ^ 7 / 5040 ≤ α ^ 8 :=
    real_exp_eighth_order_le_octic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hJb8 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 - β ^ 7 / 5040 ≤ β ^ 8 :=
    real_exp_eighth_order_le_octic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- Component bounds (each of the 9 RHS pieces ≤ s⁸, ≤ s⁸/2, or ≤ s⁸/6)
  have hJ_a_s8 : ‖J_a‖ ≤ s ^ 8 := le_trans (le_trans hJ_a_le hJa8)
    (pow_le_pow_left₀ hα_nn hα_le 8)
  have hJ_b_s8 : ‖J_b‖ ≤ s ^ 8 := le_trans (le_trans hJ_b_le hJb8)
    (pow_le_pow_left₀ hβ_nn hβ_le 8)
  have h_aI_b : ‖a * I_b‖ ≤ s ^ 8 :=
    calc _ ≤ ‖a‖ * ‖I_b‖ := norm_mul_le _ _
      _ ≤ α * β ^ 7 := mul_le_mul_of_nonneg_left
          (le_trans hI_b_le hIb7) hα_nn
      _ ≤ s * s ^ 7 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 7)
          (by positivity) hs_nn
      _ = s ^ 8 := by ring
  have h_I_ab : ‖I_a * b‖ ≤ s ^ 8 :=
    calc _ ≤ ‖I_a‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 7 * β := mul_le_mul (le_trans hI_a_le hIa7) le_rfl
          hβ_nn (by positivity)
      _ ≤ s ^ 7 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 7)
          hβ_le (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_F₁F₂ : ‖F₁ * F₂‖ ≤ s ^ 8 :=
    calc _ ≤ ‖F₁‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 4 := mul_le_mul (le_trans hF₁_le hFa4)
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_G₁b3_norm : ‖G₁ * b ^ 3‖ ≤ s ^ 8 :=
    calc _ ≤ ‖G₁‖ * ‖b ^ 3‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β ^ 3 := mul_le_mul (le_trans hG₁_le hGa5) (norm_pow_le _ _)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 5 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_G₁b3_smul : ‖(6 : 𝕂)⁻¹ • (G₁ * b ^ 3)‖ ≤ s ^ 8 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖G₁ * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 8 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_G₁b3_norm (by norm_num)
      _ = s ^ 8 / 6 := by ring
  have h_a3G₂_norm : ‖a ^ 3 * G₂‖ ≤ s ^ 8 :=
    calc _ ≤ ‖a ^ 3‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 5 := mul_le_mul (norm_pow_le _ _) (le_trans hG₂_le hGb5)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 5 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 5) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_a3G₂_smul : ‖(6 : 𝕂)⁻¹ • (a ^ 3 * G₂)‖ ≤ s ^ 8 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖a ^ 3 * G₂‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 8 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_a3G₂_norm (by norm_num)
      _ = s ^ 8 / 6 := by ring
  have h_H₁b2_norm : ‖H₁ * b ^ 2‖ ≤ s ^ 8 :=
    calc _ ≤ ‖H₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 6 * β ^ 2 := mul_le_mul (le_trans hH₁_le hHa6) (norm_pow_le _ _)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 6 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 6)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_H₁b2_smul : ‖(2 : 𝕂)⁻¹ • (H₁ * b ^ 2)‖ ≤ s ^ 8 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖H₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 8 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_H₁b2_norm (by norm_num)
      _ = s ^ 8 / 2 := by ring
  have h_a2H₂_norm : ‖a ^ 2 * H₂‖ ≤ s ^ 8 :=
    calc _ ≤ ‖a ^ 2‖ * ‖H₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 6 := mul_le_mul (norm_pow_le _ _) (le_trans hH₂_le hHb6)
          (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 6 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 6) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_a2H₂_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * H₂)‖ ≤ s ^ 8 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * H₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 8 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2H₂_norm (by norm_num)
      _ = s ^ 8 / 2 := by ring
  -- Triangle inequality. Sum: 5·s⁸ + 2·(s⁸/6) + 2·(s⁸/2) = 5·s⁸ + s⁸/3 + s⁸
  -- = 19/3·s⁸ ≈ 6.34·s⁸ ≤ 7·s⁸.
  have ha1 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂) +
    (2 : 𝕂)⁻¹ • (H₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * H₂))
  have ha2 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂))
    ((2 : 𝕂)⁻¹ • (H₁ * b ^ 2))
  have ha3 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (G₁ * b ^ 3)) ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂))
  have ha4 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂)
    ((6 : 𝕂)⁻¹ • (G₁ * b ^ 3))
  have ha5 := norm_add_le (J_a + J_b + a * I_b + I_a * b) (F₁ * F₂)
  have ha6 := norm_add_le (J_a + J_b + a * I_b) (I_a * b)
  have ha7 := norm_add_le (J_a + J_b) (a * I_b)
  have ha8 := norm_add_le J_a J_b
  linarith [pow_nonneg hs_nn 8]

/-- Norm bound `‖P² - T₂² - T₂T₃ - T₃T₂ - T₂T₄ - T₃² - T₄T₂‖ ≤ 16·s⁷`
for `s ≤ 1/10`. Decomposes via `P = T₂ + T₃ + T₄ + D₅` (D₅ = P-T₂-T₃-T₄,
‖D₅‖ ≤ 6·s⁵) into 10 deg-7+ terms.

The deg-7 P²-residual cluster — deg-9 analog of `norm_T22_sub_P2_etc_le`
at one degree higher. Provides the K_P2' = 16 input bound for
`norm_I2_octic_residual_RHS_le`. -/
private theorem norm_P2_etc_octic_le (P T₂ T₃ T₄ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3) (hT₄ : ‖T₄‖ ≤ s ^ 4)
    (hD5 : ‖P - T₂ - T₃ - T₄‖ ≤ 6 * s ^ 5) :
    ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
        T₂ * T₄ - T₃ * T₃ - T₄ * T₂‖ ≤ 16 * s ^ 7 := by
  have heq : P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ - T₂ * T₄ - T₃ * T₃ - T₄ * T₂ =
      T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₂ +
      T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₃ +
      T₄ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₄ +
      (P - T₂ - T₃ - T₄) ^ 2 := by
    have hP : P = T₂ + T₃ + T₄ + (P - T₂ - T₃ - T₄) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  -- 10 component bounds
  have h_T3T4 : ‖T₃ * T₄‖ ≤ s ^ 3 * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hT₄ (norm_nonneg _) (by positivity))
  have h_T4T3 : ‖T₄ * T₃‖ ≤ s ^ 4 * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hT₃ (norm_nonneg _) (by positivity))
  have h_T2D5 : ‖T₂ * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 2 * (6 * s ^ 5) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₂ hD5 (norm_nonneg _) (by positivity))
  have h_D5T2 : ‖(P - T₂ - T₃ - T₄) * T₂‖ ≤ (6 * s ^ 5) * s ^ 2 :=
    (norm_mul_le _ _).trans (mul_le_mul hD5 hT₂ (norm_nonneg _) (by positivity))
  have h_T4_2 : ‖T₄ ^ 2‖ ≤ s ^ 4 * s ^ 4 :=
    calc _ ≤ ‖T₄‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₄ 2
      _ = s ^ 4 * s ^ 4 := by ring
  have h_T3D5 : ‖T₃ * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 3 * (6 * s ^ 5) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hD5 (norm_nonneg _) (by positivity))
  have h_D5T3 : ‖(P - T₂ - T₃ - T₄) * T₃‖ ≤ (6 * s ^ 5) * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hD5 hT₃ (norm_nonneg _) (by positivity))
  have h_T4D5 : ‖T₄ * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 4 * (6 * s ^ 5) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hD5 (norm_nonneg _) (by positivity))
  have h_D5T4 : ‖(P - T₂ - T₃ - T₄) * T₄‖ ≤ (6 * s ^ 5) * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hD5 hT₄ (norm_nonneg _) (by positivity))
  have h_D5_2 : ‖(P - T₂ - T₃ - T₄) ^ 2‖ ≤ (6 * s ^ 5) ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄‖ ^ 2 := norm_pow_le _ _
      _ ≤ (6 * s ^ 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD5 2
  -- Triangle inequality on 10-term sum.
  have ha1 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₃ + T₄ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₄) ((P - T₂ - T₃ - T₄) ^ 2)
  have ha2 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₃ + T₄ * (P - T₂ - T₃ - T₄))
    ((P - T₂ - T₃ - T₄) * T₄)
  have ha3 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₃) (T₄ * (P - T₂ - T₃ - T₄))
  have ha4 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄))
    ((P - T₂ - T₃ - T₄) * T₃)
  have ha5 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2) (T₃ * (P - T₂ - T₃ - T₄))
  have ha6 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂) (T₄ ^ 2)
  have ha7 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄))
    ((P - T₂ - T₃ - T₄) * T₂)
  have ha8 := norm_add_le (T₃ * T₄ + T₄ * T₃) (T₂ * (P - T₂ - T₃ - T₄))
  have ha9 := norm_add_le (T₃ * T₄) (T₄ * T₃)
  -- Sum: 2·s⁷ + 12·s⁷ + s⁸ + 12·s⁸ + 12·s⁹ + 36·s¹⁰
  --   = 14·s⁷ + 13·s⁸ + 12·s⁹ + 36·s¹⁰
  -- For s ≤ 1/10: ≤ 14 + 1.3 + 0.12 + 0.0036 ≈ 15.4 ≤ 16
  nlinarith [pow_nonneg hs_nn 7, pow_nonneg hs_nn 8, pow_nonneg hs_nn 9,
    pow_nonneg hs_nn 10, mul_nonneg (pow_nonneg hs_nn 7) hs_nn,
    mul_nonneg (pow_nonneg hs_nn 7) (sq_nonneg s),
    mul_nonneg (pow_nonneg hs_nn 7) (pow_nonneg hs_nn 3)]

set_option maxHeartbeats 4000000 in
/-- Norm bound `‖P² - T₂² - T₂T₃ - T₃T₂ - T₂T₄ - T₃² - T₄T₂ - T₂T₅ - T₃T₄ - T₄T₃ - T₅T₂‖
≤ 19·s⁸` for `s ≤ 1/10`. Decomposes via `P = T₂ + T₃ + T₄ + T₅ + D₆`
(D₆ = P-T₂-T₃-T₄-T₅, ‖D₆‖ ≤ 7·s⁶) into 15 deg-8+ terms.

The deg-8 P²-residual cluster — deg-9 analog of `norm_P2_etc_octic_le` at
one degree higher. Forward-looking infrastructure for the future I2-nonic
chain in the deg-9-parent T2-F7e-octic discharge. -/
private theorem norm_P2_etc_nonic_le (P T₂ T₃ T₄ T₅ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3) (hT₄ : ‖T₄‖ ≤ s ^ 4)
    (hT₅ : ‖T₅‖ ≤ s ^ 5)
    (hD6 : ‖P - T₂ - T₃ - T₄ - T₅‖ ≤ 7 * s ^ 6) :
    ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ - T₂ * T₄ - T₃ * T₃ - T₄ * T₂ -
        T₂ * T₅ - T₃ * T₄ - T₄ * T₃ - T₅ * T₂‖ ≤ 19 * s ^ 8 := by
  have heq : P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ - T₂ * T₄ - T₃ * T₃ - T₄ * T₂ -
        T₂ * T₅ - T₃ * T₄ - T₄ * T₃ - T₅ * T₂ =
      T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
      T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
      T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
      T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄ +
      T₅ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₅ +
      (P - T₂ - T₃ - T₄ - T₅) ^ 2 := by
    have hP : P = T₂ + T₃ + T₄ + T₅ + (P - T₂ - T₃ - T₄ - T₅) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  -- 15 component bounds.
  have h_T3T5 : ‖T₃ * T₅‖ ≤ s ^ 3 * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hT₅ (norm_nonneg _) (by positivity))
  have h_T4_2 : ‖T₄ ^ 2‖ ≤ s ^ 4 * s ^ 4 :=
    calc _ ≤ ‖T₄‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₄ 2
      _ = s ^ 4 * s ^ 4 := by ring
  have h_T5T3 : ‖T₅ * T₃‖ ≤ s ^ 5 * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hT₃ (norm_nonneg _) (by positivity))
  have h_T4T5 : ‖T₄ * T₅‖ ≤ s ^ 4 * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hT₅ (norm_nonneg _) (by positivity))
  have h_T5T4 : ‖T₅ * T₄‖ ≤ s ^ 5 * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hT₄ (norm_nonneg _) (by positivity))
  have h_T5_2 : ‖T₅ ^ 2‖ ≤ s ^ 5 * s ^ 5 :=
    calc _ ≤ ‖T₅‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₅ 2
      _ = s ^ 5 * s ^ 5 := by ring
  have h_T2D6 : ‖T₂ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 2 * (7 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₂ hD6 (norm_nonneg _) (by positivity))
  have h_D6T2 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₂‖ ≤ (7 * s ^ 6) * s ^ 2 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₂ (norm_nonneg _) (by positivity))
  have h_T3D6 : ‖T₃ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 3 * (7 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hD6 (norm_nonneg _) (by positivity))
  have h_D6T3 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₃‖ ≤ (7 * s ^ 6) * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₃ (norm_nonneg _) (by positivity))
  have h_T4D6 : ‖T₄ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 4 * (7 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hD6 (norm_nonneg _) (by positivity))
  have h_D6T4 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₄‖ ≤ (7 * s ^ 6) * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₄ (norm_nonneg _) (by positivity))
  have h_T5D6 : ‖T₅ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 5 * (7 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hD6 (norm_nonneg _) (by positivity))
  have h_D6T5 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₅‖ ≤ (7 * s ^ 6) * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₅ (norm_nonneg _) (by positivity))
  have h_D6_2 : ‖(P - T₂ - T₃ - T₄ - T₅) ^ 2‖ ≤ (7 * s ^ 6) ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄ - T₅‖ ^ 2 := norm_pow_le _ _
      _ ≤ (7 * s ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD6 2
  -- Triangle inequality on 15-term sum (14 norm_add_le).
  have ha1 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₅)
    ((P - T₂ - T₃ - T₄ - T₅) ^ 2)
  have ha2 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * T₅)
  have ha3 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄)
    (T₅ * (P - T₂ - T₃ - T₄ - T₅))
  have ha4 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * T₄)
  have ha5 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃)
    (T₄ * (P - T₂ - T₃ - T₄ - T₅))
  have ha6 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * T₃)
  have ha7 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂)
    (T₃ * (P - T₂ - T₃ - T₄ - T₅))
  have ha8 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * T₂)
  have ha9 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄ + T₅ ^ 2)
    (T₂ * (P - T₂ - T₃ - T₄ - T₅))
  have ha10 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅ + T₅ * T₄) (T₅ ^ 2)
  have ha11 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₄ * T₅) (T₅ * T₄)
  have ha12 := norm_add_le (T₃ * T₅ + T₄ ^ 2 + T₅ * T₃) (T₄ * T₅)
  have ha13 := norm_add_le (T₃ * T₅ + T₄ ^ 2) (T₅ * T₃)
  have ha14 := norm_add_le (T₃ * T₅) (T₄ ^ 2)
  -- Sum (units of s⁸):
  -- s⁸ pieces: 3 (T₃T₅+T₄²+T₅T₃) + 14 (T₂D₆+D₆T₂) = 17·s⁸
  -- s⁹ pieces: 2 (T₄T₅+T₅T₄) + 14 (T₃D₆+D₆T₃) = 16·s⁹ ≤ 1.6·s⁸
  -- s¹⁰ pieces: 1 (T₅²) + 14 (T₄D₆+D₆T₄) = 15·s¹⁰ ≤ 0.15·s⁸
  -- s¹¹ pieces: 14 (T₅D₆+D₆T₅) ≤ 0.014·s⁸
  -- s¹² pieces: 49 (D₆²) ≤ 0.0000049·s⁸
  -- Total ≈ 17 + 1.6 + 0.15 + 0.014 + ε ≈ 18.76 ≤ 19·s⁸.
  nlinarith [pow_nonneg hs_nn 8, pow_nonneg hs_nn 9, pow_nonneg hs_nn 10,
    pow_nonneg hs_nn 11, pow_nonneg hs_nn 12, mul_nonneg (pow_nonneg hs_nn 8) hs_nn,
    mul_nonneg (pow_nonneg hs_nn 8) (sq_nonneg s),
    mul_nonneg (pow_nonneg hs_nn 8) (pow_nonneg hs_nn 3)]

/-- Norm bound `‖PzP - T₂zT₂ - T₂zT₃ - T₃zT₂ - T₂zT₄ - T₃zT₃ - T₄zT₂‖ ≤ 16·s⁸`
for `s ≤ 1/10`. Decomposes via `P = T₂ + T₃ + T₄ + D₅` (D₅ = P-T₂-T₃-T₄,
‖D₅‖ ≤ 6·s⁵) into 10 deg-8+ terms.

The deg-8 PzP-residual sandwich — deg-9 analog of `norm_PzP_sub_T2zT2_etc_le`
at one degree higher. Provides the K_PzP' = 16 input bound for
`norm_I2_octic_residual_RHS_le`. -/
private theorem norm_PzP_etc_octic_le (z P T₂ T₃ T₄ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hz : ‖z‖ ≤ s)
    (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3) (hT₄ : ‖T₄‖ ≤ s ^ 4)
    (hD5 : ‖P - T₂ - T₃ - T₄‖ ≤ 6 * s ^ 5) :
    ‖P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
        T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂‖ ≤ 16 * s ^ 8 := by
  have heq : P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
      T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂ =
      T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
      T₃ * z * (P - T₂ - T₃ - T₄) + T₄ * z * T₃ + T₄ * z * T₄ +
      T₄ * z * (P - T₂ - T₃ - T₄) +
      (P - T₂ - T₃ - T₄) * z * T₂ + (P - T₂ - T₃ - T₄) * z * T₃ +
      (P - T₂ - T₃ - T₄) * z * T₄ +
      (P - T₂ - T₃ - T₄) * z * (P - T₂ - T₃ - T₄) := by
    have hP : P = T₂ + T₃ + T₄ + (P - T₂ - T₃ - T₄) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  -- 10 component bounds (each `‖X * z * Y‖ ≤ ‖X‖·‖z‖·‖Y‖`)
  have h_T2zD5 : ‖T₂ * z * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 2 * s * (6 * s ^ 5) :=
    calc _ ≤ ‖T₂ * z‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * (6 * s ^ 5) := by
          apply mul_le_mul _ hD5 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hz (norm_nonneg _) (by positivity)
  have h_T3zT4 : ‖T₃ * z * T₄‖ ≤ s ^ 3 * s * s ^ 4 :=
    calc _ ≤ ‖T₃ * z‖ * ‖T₄‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖z‖) * ‖T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * s) * s ^ 4 := by
          apply mul_le_mul _ hT₄ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hz (norm_nonneg _) (by positivity)
  have h_T3zD5 : ‖T₃ * z * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 3 * s * (6 * s ^ 5) :=
    calc _ ≤ ‖T₃ * z‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * s) * (6 * s ^ 5) := by
          apply mul_le_mul _ hD5 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hz (norm_nonneg _) (by positivity)
  have h_T4zT3 : ‖T₄ * z * T₃‖ ≤ s ^ 4 * s * s ^ 3 :=
    calc _ ≤ ‖T₄ * z‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₄‖ * ‖z‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 4 * s) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₄ hz (norm_nonneg _) (by positivity)
  have h_T4zT4 : ‖T₄ * z * T₄‖ ≤ s ^ 4 * s * s ^ 4 :=
    calc _ ≤ ‖T₄ * z‖ * ‖T₄‖ := norm_mul_le _ _
      _ ≤ (‖T₄‖ * ‖z‖) * ‖T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 4 * s) * s ^ 4 := by
          apply mul_le_mul _ hT₄ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₄ hz (norm_nonneg _) (by positivity)
  have h_T4zD5 : ‖T₄ * z * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 4 * s * (6 * s ^ 5) :=
    calc _ ≤ ‖T₄ * z‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
      _ ≤ (‖T₄‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 4 * s) * (6 * s ^ 5) := by
          apply mul_le_mul _ hD5 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₄ hz (norm_nonneg _) (by positivity)
  have h_D5zT2 : ‖(P - T₂ - T₃ - T₄) * z * T₂‖ ≤ (6 * s ^ 5) * s * s ^ 2 :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄‖ * ‖z‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((6 * s ^ 5) * s) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hD5 hz (norm_nonneg _) (by positivity)
  have h_D5zT3 : ‖(P - T₂ - T₃ - T₄) * z * T₃‖ ≤ (6 * s ^ 5) * s * s ^ 3 :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄) * z‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄‖ * ‖z‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((6 * s ^ 5) * s) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hD5 hz (norm_nonneg _) (by positivity)
  have h_D5zT4 : ‖(P - T₂ - T₃ - T₄) * z * T₄‖ ≤ (6 * s ^ 5) * s * s ^ 4 :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄) * z‖ * ‖T₄‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄‖ * ‖z‖) * ‖T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((6 * s ^ 5) * s) * s ^ 4 := by
          apply mul_le_mul _ hT₄ (norm_nonneg _) (by positivity)
          exact mul_le_mul hD5 hz (norm_nonneg _) (by positivity)
  have h_D5zD5 : ‖(P - T₂ - T₃ - T₄) * z * (P - T₂ - T₃ - T₄)‖ ≤
      (6 * s ^ 5) * s * (6 * s ^ 5) :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄) * z‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((6 * s ^ 5) * s) * (6 * s ^ 5) := by
          apply mul_le_mul _ hD5 (norm_nonneg _) (by positivity)
          exact mul_le_mul hD5 hz (norm_nonneg _) (by positivity)
  -- Triangle inequality on 10-term sum.
  have ha1 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
    T₃ * z * (P - T₂ - T₃ - T₄) + T₄ * z * T₃ + T₄ * z * T₄ +
    T₄ * z * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * z * T₂ + (P - T₂ - T₃ - T₄) * z * T₃ +
    (P - T₂ - T₃ - T₄) * z * T₄)
    ((P - T₂ - T₃ - T₄) * z * (P - T₂ - T₃ - T₄))
  have ha2 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
    T₃ * z * (P - T₂ - T₃ - T₄) + T₄ * z * T₃ + T₄ * z * T₄ +
    T₄ * z * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * z * T₂ + (P - T₂ - T₃ - T₄) * z * T₃)
    ((P - T₂ - T₃ - T₄) * z * T₄)
  have ha3 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
    T₃ * z * (P - T₂ - T₃ - T₄) + T₄ * z * T₃ + T₄ * z * T₄ +
    T₄ * z * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * z * T₂)
    ((P - T₂ - T₃ - T₄) * z * T₃)
  have ha4 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
    T₃ * z * (P - T₂ - T₃ - T₄) + T₄ * z * T₃ + T₄ * z * T₄ +
    T₄ * z * (P - T₂ - T₃ - T₄))
    ((P - T₂ - T₃ - T₄) * z * T₂)
  have ha5 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
    T₃ * z * (P - T₂ - T₃ - T₄) + T₄ * z * T₃ + T₄ * z * T₄)
    (T₄ * z * (P - T₂ - T₃ - T₄))
  have ha6 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
    T₃ * z * (P - T₂ - T₃ - T₄) + T₄ * z * T₃) (T₄ * z * T₄)
  have ha7 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄ +
    T₃ * z * (P - T₂ - T₃ - T₄)) (T₄ * z * T₃)
  have ha8 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄) + T₃ * z * T₄)
    (T₃ * z * (P - T₂ - T₃ - T₄))
  have ha9 := norm_add_le (T₂ * z * (P - T₂ - T₃ - T₄)) (T₃ * z * T₄)
  -- Sum bounds: 6s⁸ + s⁸ + 6s⁹ + s⁸ + s⁹ + 6s¹⁰ + 6s⁸ + 6s⁹ + 6s¹⁰ + 36s¹¹
  --   = 14·s⁸ + 13·s⁹ + 12·s¹⁰ + 36·s¹¹
  -- For s ≤ 1/10: ≤ 14 + 1.3 + 0.12 + 0.036 ≈ 15.46 ≤ 16
  nlinarith [pow_nonneg hs_nn 8, pow_nonneg hs_nn 9, pow_nonneg hs_nn 10,
    pow_nonneg hs_nn 11, mul_nonneg (pow_nonneg hs_nn 8) hs_nn,
    mul_nonneg (pow_nonneg hs_nn 8) (sq_nonneg s),
    mul_nonneg (pow_nonneg hs_nn 8) (pow_nonneg hs_nn 3)]

set_option maxHeartbeats 4000000 in
/-- Norm bound `‖PzP - T₂zT₂ - T₂zT₃ - T₃zT₂ - T₂zT₄ - T₃zT₃ - T₄zT₂
       - T₂zT₅ - T₃zT₄ - T₄zT₃ - T₅zT₂‖ ≤ 19·s⁹` for `s ≤ 1/10`.
Decomposes via `P = T₂ + T₃ + T₄ + T₅ + D₆` (D₆ = P-T₂-T₃-T₄-T₅,
‖D₆‖ ≤ 7·s⁶) into 15 deg-9+ terms.

The deg-9 PzP-residual sandwich — deg-9 analog of `norm_PzP_etc_octic_le`
at one degree higher (15 terms instead of 10). Forward-looking infrastructure
for the future I2-nonic chain in the deg-9-parent T2-F7e-octic discharge. -/
private theorem norm_PzP_etc_nonic_le (z P T₂ T₃ T₄ T₅ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hz : ‖z‖ ≤ s)
    (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3) (hT₄ : ‖T₄‖ ≤ s ^ 4)
    (hT₅ : ‖T₅‖ ≤ s ^ 5)
    (hD6 : ‖P - T₂ - T₃ - T₄ - T₅‖ ≤ 7 * s ^ 6) :
    ‖P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
        T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂ -
        T₂ * z * T₅ - T₃ * z * T₄ - T₄ * z * T₃ - T₅ * z * T₂‖ ≤ 19 * s ^ 9 := by
  have heq : P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
      T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂ -
      T₂ * z * T₅ - T₃ * z * T₄ - T₄ * z * T₃ - T₅ * z * T₂ =
      T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ + T₅ * z * T₄ + T₅ * z * T₅ +
      T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂ +
      T₃ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₃ +
      T₄ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₄ +
      T₅ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₅ +
      (P - T₂ - T₃ - T₄ - T₅) * z * (P - T₂ - T₃ - T₄ - T₅) := by
    have hP : P = T₂ + T₃ + T₄ + T₅ + (P - T₂ - T₃ - T₄ - T₅) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  -- 15 component bounds (each `‖X·z·Y‖ ≤ ‖X‖·‖z‖·‖Y‖`).
  have h_T3zT5 : ‖T₃ * z * T₅‖ ≤ s ^ 3 * s * s ^ 5 :=
    calc _ ≤ ‖T₃ * z‖ * ‖T₅‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖z‖) * ‖T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * s) * s ^ 5 := by
          apply mul_le_mul _ hT₅ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hz (norm_nonneg _) (by positivity)
  have h_T4zT4 : ‖T₄ * z * T₄‖ ≤ s ^ 4 * s * s ^ 4 :=
    calc _ ≤ ‖T₄ * z‖ * ‖T₄‖ := norm_mul_le _ _
      _ ≤ (‖T₄‖ * ‖z‖) * ‖T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 4 * s) * s ^ 4 := by
          apply mul_le_mul _ hT₄ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₄ hz (norm_nonneg _) (by positivity)
  have h_T5zT3 : ‖T₅ * z * T₃‖ ≤ s ^ 5 * s * s ^ 3 :=
    calc _ ≤ ‖T₅ * z‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₅‖ * ‖z‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 5 * s) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₅ hz (norm_nonneg _) (by positivity)
  have h_T4zT5 : ‖T₄ * z * T₅‖ ≤ s ^ 4 * s * s ^ 5 :=
    calc _ ≤ ‖T₄ * z‖ * ‖T₅‖ := norm_mul_le _ _
      _ ≤ (‖T₄‖ * ‖z‖) * ‖T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 4 * s) * s ^ 5 := by
          apply mul_le_mul _ hT₅ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₄ hz (norm_nonneg _) (by positivity)
  have h_T5zT4 : ‖T₅ * z * T₄‖ ≤ s ^ 5 * s * s ^ 4 :=
    calc _ ≤ ‖T₅ * z‖ * ‖T₄‖ := norm_mul_le _ _
      _ ≤ (‖T₅‖ * ‖z‖) * ‖T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 5 * s) * s ^ 4 := by
          apply mul_le_mul _ hT₄ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₅ hz (norm_nonneg _) (by positivity)
  have h_T5zT5 : ‖T₅ * z * T₅‖ ≤ s ^ 5 * s * s ^ 5 :=
    calc _ ≤ ‖T₅ * z‖ * ‖T₅‖ := norm_mul_le _ _
      _ ≤ (‖T₅‖ * ‖z‖) * ‖T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 5 * s) * s ^ 5 := by
          apply mul_le_mul _ hT₅ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₅ hz (norm_nonneg _) (by positivity)
  have h_T2zD6 : ‖T₂ * z * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 2 * s * (7 * s ^ 6) :=
    calc _ ≤ ‖T₂ * z‖ * ‖P - T₂ - T₃ - T₄ - T₅‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄ - T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * (7 * s ^ 6) := by
          apply mul_le_mul _ hD6 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hz (norm_nonneg _) (by positivity)
  have h_D6zT2 : ‖(P - T₂ - T₃ - T₄ - T₅) * z * T₂‖ ≤ (7 * s ^ 6) * s * s ^ 2 :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄ - T₅) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄ - T₅‖ * ‖z‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((7 * s ^ 6) * s) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hD6 hz (norm_nonneg _) (by positivity)
  have h_T3zD6 : ‖T₃ * z * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 3 * s * (7 * s ^ 6) :=
    calc _ ≤ ‖T₃ * z‖ * ‖P - T₂ - T₃ - T₄ - T₅‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄ - T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * s) * (7 * s ^ 6) := by
          apply mul_le_mul _ hD6 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hz (norm_nonneg _) (by positivity)
  have h_D6zT3 : ‖(P - T₂ - T₃ - T₄ - T₅) * z * T₃‖ ≤ (7 * s ^ 6) * s * s ^ 3 :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄ - T₅) * z‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄ - T₅‖ * ‖z‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((7 * s ^ 6) * s) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hD6 hz (norm_nonneg _) (by positivity)
  have h_T4zD6 : ‖T₄ * z * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 4 * s * (7 * s ^ 6) :=
    calc _ ≤ ‖T₄ * z‖ * ‖P - T₂ - T₃ - T₄ - T₅‖ := norm_mul_le _ _
      _ ≤ (‖T₄‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄ - T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 4 * s) * (7 * s ^ 6) := by
          apply mul_le_mul _ hD6 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₄ hz (norm_nonneg _) (by positivity)
  have h_D6zT4 : ‖(P - T₂ - T₃ - T₄ - T₅) * z * T₄‖ ≤ (7 * s ^ 6) * s * s ^ 4 :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄ - T₅) * z‖ * ‖T₄‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄ - T₅‖ * ‖z‖) * ‖T₄‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((7 * s ^ 6) * s) * s ^ 4 := by
          apply mul_le_mul _ hT₄ (norm_nonneg _) (by positivity)
          exact mul_le_mul hD6 hz (norm_nonneg _) (by positivity)
  have h_T5zD6 : ‖T₅ * z * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 5 * s * (7 * s ^ 6) :=
    calc _ ≤ ‖T₅ * z‖ * ‖P - T₂ - T₃ - T₄ - T₅‖ := norm_mul_le _ _
      _ ≤ (‖T₅‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄ - T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 5 * s) * (7 * s ^ 6) := by
          apply mul_le_mul _ hD6 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₅ hz (norm_nonneg _) (by positivity)
  have h_D6zT5 : ‖(P - T₂ - T₃ - T₄ - T₅) * z * T₅‖ ≤ (7 * s ^ 6) * s * s ^ 5 :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄ - T₅) * z‖ * ‖T₅‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄ - T₅‖ * ‖z‖) * ‖T₅‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((7 * s ^ 6) * s) * s ^ 5 := by
          apply mul_le_mul _ hT₅ (norm_nonneg _) (by positivity)
          exact mul_le_mul hD6 hz (norm_nonneg _) (by positivity)
  have h_D6zD6 : ‖(P - T₂ - T₃ - T₄ - T₅) * z * (P - T₂ - T₃ - T₄ - T₅)‖ ≤
      (7 * s ^ 6) * s * (7 * s ^ 6) :=
    calc _ ≤ ‖(P - T₂ - T₃ - T₄ - T₅) * z‖ * ‖P - T₂ - T₃ - T₄ - T₅‖ :=
            norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃ - T₄ - T₅‖ * ‖z‖) * ‖P - T₂ - T₃ - T₄ - T₅‖ := by
            gcongr; exact norm_mul_le _ _
      _ ≤ ((7 * s ^ 6) * s) * (7 * s ^ 6) := by
          apply mul_le_mul _ hD6 (norm_nonneg _) (by positivity)
          exact mul_le_mul hD6 hz (norm_nonneg _) (by positivity)
  -- Triangle inequality on 15-term sum (14 norm_add_le).
  have ha1 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂ +
    T₃ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₃ +
    T₄ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₄ +
    T₅ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₅)
    ((P - T₂ - T₃ - T₄ - T₅) * z * (P - T₂ - T₃ - T₄ - T₅))
  have ha2 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂ +
    T₃ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₃ +
    T₄ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₄ +
    T₅ * z * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * z * T₅)
  have ha3 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂ +
    T₃ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₃ +
    T₄ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₄)
    (T₅ * z * (P - T₂ - T₃ - T₄ - T₅))
  have ha4 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂ +
    T₃ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₃ +
    T₄ * z * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * z * T₄)
  have ha5 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂ +
    T₃ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₃)
    (T₄ * z * (P - T₂ - T₃ - T₄ - T₅))
  have ha6 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂ +
    T₃ * z * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * z * T₃)
  have ha7 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * z * T₂)
    (T₃ * z * (P - T₂ - T₃ - T₄ - T₅))
  have ha8 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅ +
    T₂ * z * (P - T₂ - T₃ - T₄ - T₅)) ((P - T₂ - T₃ - T₄ - T₅) * z * T₂)
  have ha9 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄ + T₅ * z * T₅) (T₂ * z * (P - T₂ - T₃ - T₄ - T₅))
  have ha10 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅ +
    T₅ * z * T₄) (T₅ * z * T₅)
  have ha11 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃ + T₄ * z * T₅)
    (T₅ * z * T₄)
  have ha12 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄ + T₅ * z * T₃)
    (T₄ * z * T₅)
  have ha13 := norm_add_le (T₃ * z * T₅ + T₄ * z * T₄) (T₅ * z * T₃)
  have ha14 := norm_add_le (T₃ * z * T₅) (T₄ * z * T₄)
  -- Sum (units of s⁹):
  -- s⁹: 3 (T₃zT₅+T₄zT₄+T₅zT₃) + 14 (T₂zD₆+D₆zT₂) = 17·s⁹
  -- s¹⁰: 2 (T₄zT₅+T₅zT₄) + 14 (T₃zD₆+D₆zT₃) = 16·s¹⁰ ≤ 1.6·s⁹
  -- s¹¹: 1 (T₅zT₅) + 14 (T₄zD₆+D₆zT₄) = 15·s¹¹ ≤ 0.15·s⁹
  -- s¹²: 14 (T₅zD₆+D₆zT₅) ≤ 0.014·s⁹
  -- s¹³: 49 (D₆zD₆) ≤ ε
  -- Total ≈ 17 + 1.6 + 0.15 + 0.014 + ε ≈ 18.76 ≤ 19·s⁹.
  nlinarith [pow_nonneg hs_nn 9, pow_nonneg hs_nn 10, pow_nonneg hs_nn 11,
    pow_nonneg hs_nn 12, pow_nonneg hs_nn 13, mul_nonneg (pow_nonneg hs_nn 9) hs_nn,
    mul_nonneg (pow_nonneg hs_nn 9) (sq_nonneg s),
    mul_nonneg (pow_nonneg hs_nn 9) (pow_nonneg hs_nn 3)]

/-- Norm bound `‖P³ - T₂³ - T₂²T₃ - T₂T₃T₂ - T₃T₂²‖ ≤ 105·s⁸` for `s ≤ 1/10`.
Decomposes via `P = T₂ + V'` (V' = P-T₂, ‖V'‖ ≤ 5·s³) and refines the deg-7
contributions by subtracting `T₂²T₃ + T₂T₃T₂ + T₃T₂²` to use V = P-T₂-T₃
(‖V‖ ≤ 5·s⁴). 7-term decomposition:

  P³ - T₂³ - T₂²T₃ - T₂T₃T₂ - T₃T₂² =
    T₂²·V + T₂·V·T₂ + V·T₂² +
    T₂·V'² + V'·T₂·V' + V'²·T₂ +
    V'³

Per-term bounds with s ≤ 1/10:
  3·5s⁸ + 3·25s⁸ + 125s⁹ = 15s⁸ + 75s⁸ + 12.5s⁸ = 102.5s⁸ ≤ 105·s⁸.

Deg-9 analog of `norm_P3_sub_T23_le` at one degree higher.
Provides the K_P3' = 105 input bound for `norm_I2_octic_residual_RHS_le`. -/
private theorem norm_P3_etc_octic_le (P T₂ T₃ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2‖ ≤ 105 * s ^ 8 := by
  have heq : P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2 =
      T₂ ^ 2 * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₂ + (P - T₂ - T₃) * T₂ ^ 2 +
      T₂ * (P - T₂) ^ 2 + (P - T₂) * T₂ * (P - T₂) + (P - T₂) ^ 2 * T₂ +
      (P - T₂) ^ 3 := by
    have hP : P = T₂ + (P - T₂) := by abel
    have hVp : P - T₂ = T₃ + (P - T₂ - T₃) := by abel
    -- We expand P^3 = (T₂+V')^3 = T₂^3 + T₂^2 V' + T₂ V' T₂ + V' T₂^2
    --   + T₂ V'^2 + V' T₂ V' + V'^2 T₂ + V'^3.
    -- Then T₂^2 V' = T₂^2 T₃ + T₂^2 V where V = P-T₂-T₃, similarly for conjugates.
    rw [hP]; noncomm_ring
  rw [heq]
  -- 7 component bounds
  have h_T22V : ‖T₂ ^ 2 * (P - T₂ - T₃)‖ ≤ (s ^ 2) ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖T₂ ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ‖T₂‖ ^ 2 * ‖P - T₂ - T₃‖ := by gcongr; exact norm_pow_le T₂ 2
      _ ≤ (s ^ 2) ^ 2 * (5 * s ^ 4) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hT₂ 2) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  have h_T2VT2 : ‖T₂ * (P - T₂ - T₃) * T₂‖ ≤ s ^ 2 * (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖T₂ * (P - T₂ - T₃)‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖P - T₂ - T₃‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * (5 * s ^ 4)) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have h_VT22 : ‖(P - T₂ - T₃) * T₂ ^ 2‖ ≤ (5 * s ^ 4) * (s ^ 2) ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖T₂ ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ * ‖T₂‖ ^ 2 := by gcongr; exact norm_pow_le T₂ 2
      _ ≤ (5 * s ^ 4) * (s ^ 2) ^ 2 :=
          mul_le_mul hPmT₂mT₃ (pow_le_pow_left₀ (norm_nonneg _) hT₂ 2)
            (by positivity) (by positivity)
  have h_T2Vp2 : ‖T₂ * (P - T₂) ^ 2‖ ≤ s ^ 2 * (5 * s ^ 3) ^ 2 :=
    calc _ ≤ ‖T₂‖ * ‖(P - T₂) ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖T₂‖ * ‖P - T₂‖ ^ 2 := by gcongr; exact norm_pow_le (P - T₂) 2
      _ ≤ s ^ 2 * (5 * s ^ 3) ^ 2 := mul_le_mul hT₂
          (pow_le_pow_left₀ (norm_nonneg _) hPmT₂ 2) (by positivity) (by positivity)
  have h_VpT2Vp : ‖(P - T₂) * T₂ * (P - T₂)‖ ≤ (5 * s ^ 3) * s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖(P - T₂) * T₂‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖T₂‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s ^ 2) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ hT₂ (norm_nonneg _) (by positivity)
  have h_Vp2T2 : ‖(P - T₂) ^ 2 * T₂‖ ≤ (5 * s ^ 3) ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(P - T₂) ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ ^ 2 * ‖T₂‖ := by gcongr; exact norm_pow_le (P - T₂) 2
      _ ≤ (5 * s ^ 3) ^ 2 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hPmT₂ 2) hT₂
            (by positivity) (by positivity)
  have h_Vp3 : ‖(P - T₂) ^ 3‖ ≤ (5 * s ^ 3) ^ 3 :=
    calc _ ≤ ‖P - T₂‖ ^ 3 := norm_pow_le (P - T₂) 3
      _ ≤ (5 * s ^ 3) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hPmT₂ 3
  -- Triangle inequality on 7-term sum.
  have ha1 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₂ +
    (P - T₂ - T₃) * T₂ ^ 2 + T₂ * (P - T₂) ^ 2 +
    (P - T₂) * T₂ * (P - T₂) + (P - T₂) ^ 2 * T₂) ((P - T₂) ^ 3)
  have ha2 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₂ +
    (P - T₂ - T₃) * T₂ ^ 2 + T₂ * (P - T₂) ^ 2 +
    (P - T₂) * T₂ * (P - T₂)) ((P - T₂) ^ 2 * T₂)
  have ha3 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₂ +
    (P - T₂ - T₃) * T₂ ^ 2 + T₂ * (P - T₂) ^ 2)
    ((P - T₂) * T₂ * (P - T₂))
  have ha4 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₂ +
    (P - T₂ - T₃) * T₂ ^ 2) (T₂ * (P - T₂) ^ 2)
  have ha5 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₂)
    ((P - T₂ - T₃) * T₂ ^ 2)
  have ha6 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃)) (T₂ * (P - T₂ - T₃) * T₂)
  -- Sum: 3·5s⁸ + 3·25s⁸ + 125s⁹ = 90s⁸ + 125s⁹
  -- For s ≤ 1/10: 90 + 12.5 = 102.5 ≤ 105
  nlinarith [pow_nonneg hs_nn 8, pow_nonneg hs_nn 9,
    mul_nonneg (pow_nonneg hs_nn 8) hs_nn]

set_option maxHeartbeats 4000000 in
/-- Norm bound
`‖P³ - T₂³ - T₂²T₃ - T₂T₃T₂ - T₃T₂² - T₂²T₄ - T₂T₄T₂ - T₄T₂²
    - T₂T₃² - T₃T₂T₃ - T₃²T₂‖ ≤ 200·s⁹` for `s ≤ 1/10`.

Deg-9 analog of `norm_P3_etc_octic_le` at one degree higher. Refines the
deg-7 cancellation (3 T₂²T₃-style terms) and the deg-8 cancellation (6
terms: 3 T₂²T₄-style + 3 T₂T₃²-style). Decomposes via `P = T₂ + V'`
(V' := P-T₂, ‖V'‖ ≤ 5·s³), with the deg-7 layer using V := P-T₂-T₃
(‖V‖ ≤ 5·s⁴) and the deg-8 layer using W := P-T₂-T₃-T₄ (‖W‖ ≤ 6·s⁵).

16-term decomposition:

  P³ − T₂³ − 3 deg-7 − 6 deg-8 =
    T₂²·W + T₂·W·T₂ + W·T₂²                                    (3 A-terms)
    + T₂·T₃·V + T₂·V·T₃ + T₂·V²                                 (3 B-T₂… terms)
    + T₃·T₂·V + V·T₂·T₃ + V·T₂·V                                (3 B-…T₂… terms)
    + T₃·V·T₂ + V·T₃·T₂ + V²·T₂                                 (3 B-…T₂ terms)
    + V'³                                                       (1 C-term)

Per-term bounds (units of s⁹):
  A: 3·6·s⁹ = 18·s⁹
  B (s⁹ pieces): 6·5·s⁹ = 30·s⁹
  B (s¹⁰ pieces): 3·25·s¹⁰ ≤ 7.5·s⁹  (using s ≤ 1/10)
  C: 125·s⁹
  Total ≈ 180.5·s⁹ ≤ 200·s⁹.

Forward-looking infrastructure for the future I2-nonic chain in the
deg-9-parent T2-F7e-octic discharge. -/
private theorem norm_P3_etc_nonic_le (P T₂ T₃ T₄ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3) (hT₄ : ‖T₄‖ ≤ s ^ 4)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4)
    (hPmT₂mT₃mT₄ : ‖P - T₂ - T₃ - T₄‖ ≤ 6 * s ^ 5) :
    ‖P ^ 3 - T₂ ^ 3
        - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2
        - T₂ ^ 2 * T₄ - T₂ * T₄ * T₂ - T₄ * T₂ ^ 2
        - T₂ * T₃ ^ 2 - T₃ * T₂ * T₃ - T₃ ^ 2 * T₂‖ ≤ 200 * s ^ 9 := by
  have heq : P ^ 3 - T₂ ^ 3
        - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2
        - T₂ ^ 2 * T₄ - T₂ * T₄ * T₂ - T₄ * T₂ ^ 2
        - T₂ * T₃ ^ 2 - T₃ * T₂ * T₃ - T₃ ^ 2 * T₂ =
      T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
        (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
      T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
        T₂ * (P - T₂ - T₃) ^ 2 +
      T₃ * T₂ * (P - T₂ - T₃) + (P - T₂ - T₃) * T₂ * T₃ +
        (P - T₂ - T₃) * T₂ * (P - T₂ - T₃) +
      T₃ * (P - T₂ - T₃) * T₂ + (P - T₂ - T₃) * T₃ * T₂ +
        (P - T₂ - T₃) ^ 2 * T₂ +
      (P - T₂) ^ 3 := by
    have hP : P = T₂ + (P - T₂) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  -- 16 component bounds.
  -- Group A (3 terms with W := P-T₂-T₃-T₄): each ≤ s² · s² · 6s⁵ = 6·s⁹.
  have h_A1 : ‖T₂ ^ 2 * (P - T₂ - T₃ - T₄)‖ ≤ (s ^ 2) ^ 2 * (6 * s ^ 5) :=
    calc _ ≤ ‖T₂ ^ 2‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
      _ ≤ ‖T₂‖ ^ 2 * ‖P - T₂ - T₃ - T₄‖ := by gcongr; exact norm_pow_le T₂ 2
      _ ≤ (s ^ 2) ^ 2 * (6 * s ^ 5) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hT₂ 2) hPmT₂mT₃mT₄
            (norm_nonneg _) (by positivity)
  have h_A2 : ‖T₂ * (P - T₂ - T₃ - T₄) * T₂‖ ≤ s ^ 2 * (6 * s ^ 5) * s ^ 2 :=
    calc _ ≤ ‖T₂ * (P - T₂ - T₃ - T₄)‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖P - T₂ - T₃ - T₄‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * (6 * s ^ 5)) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hPmT₂mT₃mT₄ (norm_nonneg _) (by positivity)
  have h_A3 : ‖(P - T₂ - T₃ - T₄) * T₂ ^ 2‖ ≤ (6 * s ^ 5) * (s ^ 2) ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄‖ * ‖T₂ ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃ - T₄‖ * ‖T₂‖ ^ 2 := by gcongr; exact norm_pow_le T₂ 2
      _ ≤ (6 * s ^ 5) * (s ^ 2) ^ 2 :=
          mul_le_mul hPmT₂mT₃mT₄ (pow_le_pow_left₀ (norm_nonneg _) hT₂ 2)
            (by positivity) (by positivity)
  -- Group B s⁹ terms (6 terms each ≤ s² · s³ · 5s⁴ = 5·s⁹).
  have h_B1 : ‖T₂ * T₃ * (P - T₂ - T₃)‖ ≤ s ^ 2 * s ^ 3 * (5 * s ^ 4) :=
    calc _ ≤ ‖T₂ * T₃‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖T₃‖) * ‖P - T₂ - T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s ^ 3) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hT₃ (norm_nonneg _) (by positivity)
  have h_B2 : ‖T₂ * (P - T₂ - T₃) * T₃‖ ≤ s ^ 2 * (5 * s ^ 4) * s ^ 3 :=
    calc _ ≤ ‖T₂ * (P - T₂ - T₃)‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖P - T₂ - T₃‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * (5 * s ^ 4)) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have h_B4 : ‖T₃ * T₂ * (P - T₂ - T₃)‖ ≤ s ^ 3 * s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖T₃ * T₂‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖T₂‖) * ‖P - T₂ - T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * s ^ 2) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hT₂ (norm_nonneg _) (by positivity)
  have h_B5 : ‖(P - T₂ - T₃) * T₂ * T₃‖ ≤ (5 * s ^ 4) * s ^ 2 * s ^ 3 :=
    calc _ ≤ ‖(P - T₂ - T₃) * T₂‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃‖ * ‖T₂‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 4) * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ hT₂ (norm_nonneg _) (by positivity)
  have h_B7 : ‖T₃ * (P - T₂ - T₃) * T₂‖ ≤ s ^ 3 * (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖T₃ * (P - T₂ - T₃)‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖P - T₂ - T₃‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * (5 * s ^ 4)) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have h_B8 : ‖(P - T₂ - T₃) * T₃ * T₂‖ ≤ (5 * s ^ 4) * s ^ 3 * s ^ 2 :=
    calc _ ≤ ‖(P - T₂ - T₃) * T₃‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃‖ * ‖T₃‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 4) * s ^ 3) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ hT₃ (norm_nonneg _) (by positivity)
  -- Group B s¹⁰ terms (3 terms each ≤ s² · (5s⁴)² = 25·s¹⁰).
  have h_B3 : ‖T₂ * (P - T₂ - T₃) ^ 2‖ ≤ s ^ 2 * (5 * s ^ 4) ^ 2 :=
    calc _ ≤ ‖T₂‖ * ‖(P - T₂ - T₃) ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖T₂‖ * ‖P - T₂ - T₃‖ ^ 2 := by gcongr; exact norm_pow_le (P - T₂ - T₃) 2
      _ ≤ s ^ 2 * (5 * s ^ 4) ^ 2 := mul_le_mul hT₂
          (pow_le_pow_left₀ (norm_nonneg _) hPmT₂mT₃ 2) (by positivity) (by positivity)
  have h_B6 : ‖(P - T₂ - T₃) * T₂ * (P - T₂ - T₃)‖ ≤
      (5 * s ^ 4) * s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖(P - T₂ - T₃) * T₂‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃‖ * ‖T₂‖) * ‖P - T₂ - T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 4) * s ^ 2) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ hT₂ (norm_nonneg _) (by positivity)
  have h_B9 : ‖(P - T₂ - T₃) ^ 2 * T₂‖ ≤ (5 * s ^ 4) ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(P - T₂ - T₃) ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ ^ 2 * ‖T₂‖ := by gcongr; exact norm_pow_le (P - T₂ - T₃) 2
      _ ≤ (5 * s ^ 4) ^ 2 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hPmT₂mT₃ 2) hT₂
            (by positivity) (by positivity)
  -- Group C: (P-T₂)³ — ≤ (5·s³)³ = 125·s⁹.
  have h_C : ‖(P - T₂) ^ 3‖ ≤ (5 * s ^ 3) ^ 3 :=
    calc _ ≤ ‖P - T₂‖ ^ 3 := norm_pow_le (P - T₂) 3
      _ ≤ (5 * s ^ 3) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hPmT₂ 3
  -- Triangle inequality on 16-term sum (15 norm_add_le).
  have ha1 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
    T₂ * (P - T₂ - T₃) ^ 2 +
    T₃ * T₂ * (P - T₂ - T₃) + (P - T₂ - T₃) * T₂ * T₃ +
    (P - T₂ - T₃) * T₂ * (P - T₂ - T₃) +
    T₃ * (P - T₂ - T₃) * T₂ + (P - T₂ - T₃) * T₃ * T₂ +
    (P - T₂ - T₃) ^ 2 * T₂) ((P - T₂) ^ 3)
  have ha2 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
    T₂ * (P - T₂ - T₃) ^ 2 +
    T₃ * T₂ * (P - T₂ - T₃) + (P - T₂ - T₃) * T₂ * T₃ +
    (P - T₂ - T₃) * T₂ * (P - T₂ - T₃) +
    T₃ * (P - T₂ - T₃) * T₂ + (P - T₂ - T₃) * T₃ * T₂)
    ((P - T₂ - T₃) ^ 2 * T₂)
  have ha3 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
    T₂ * (P - T₂ - T₃) ^ 2 +
    T₃ * T₂ * (P - T₂ - T₃) + (P - T₂ - T₃) * T₂ * T₃ +
    (P - T₂ - T₃) * T₂ * (P - T₂ - T₃) +
    T₃ * (P - T₂ - T₃) * T₂) ((P - T₂ - T₃) * T₃ * T₂)
  have ha4 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
    T₂ * (P - T₂ - T₃) ^ 2 +
    T₃ * T₂ * (P - T₂ - T₃) + (P - T₂ - T₃) * T₂ * T₃ +
    (P - T₂ - T₃) * T₂ * (P - T₂ - T₃))
    (T₃ * (P - T₂ - T₃) * T₂)
  have ha5 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
    T₂ * (P - T₂ - T₃) ^ 2 +
    T₃ * T₂ * (P - T₂ - T₃) + (P - T₂ - T₃) * T₂ * T₃)
    ((P - T₂ - T₃) * T₂ * (P - T₂ - T₃))
  have ha6 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
    T₂ * (P - T₂ - T₃) ^ 2 +
    T₃ * T₂ * (P - T₂ - T₃)) ((P - T₂ - T₃) * T₂ * T₃)
  have ha7 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃ +
    T₂ * (P - T₂ - T₃) ^ 2) (T₃ * T₂ * (P - T₂ - T₃))
  have ha8 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃) + T₂ * (P - T₂ - T₃) * T₃)
    (T₂ * (P - T₂ - T₃) ^ 2)
  have ha9 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2 +
    T₂ * T₃ * (P - T₂ - T₃)) (T₂ * (P - T₂ - T₃) * T₃)
  have ha10 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂ +
    (P - T₂ - T₃ - T₄) * T₂ ^ 2) (T₂ * T₃ * (P - T₂ - T₃))
  have ha11 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄) + T₂ * (P - T₂ - T₃ - T₄) * T₂)
    ((P - T₂ - T₃ - T₄) * T₂ ^ 2)
  have ha12 := norm_add_le (T₂ ^ 2 * (P - T₂ - T₃ - T₄)) (T₂ * (P - T₂ - T₃ - T₄) * T₂)
  -- Sum (units of s⁹):
  --   A (3 terms): 18·s⁹
  --   B (6 deg-9 terms): 30·s⁹
  --   B (3 deg-10 terms): 75·s¹⁰ ≤ 7.5·s⁹ (s ≤ 1/10)
  --   C: 125·s⁹
  -- Total ≈ 180.5·s⁹ ≤ 200·s⁹.
  nlinarith [pow_nonneg hs_nn 9, pow_nonneg hs_nn 10,
    mul_nonneg (pow_nonneg hs_nn 9) hs_nn]

/-- Norm bound `‖R+T₅+T₆ residual sum‖ ≤ 7·s⁷` from precomputed component bounds.
The 9 terms come from `R_plus_T5_plus_T6_eq_neg_deg7_residual`:
I_a+I_b+a·H₂+H₁·b+F₁·F₂+⅙·F₁·b³+⅙·a³·F₂+½·G₁·b²+½·a²·G₂.

Analog of `norm_R_plus_T5_residual_sum_le` at one degree higher.
All inputs are deg-7+ (or deg-8+ for F₁·F₂); requires `s ≤ 1` to fold
the s⁸ piece into s⁷. -/
private theorem norm_R_plus_T5_plus_T6_residual_sum_le
    (I_a I_b H₁ H₂ G₁ G₂ F₁ F₂ a b : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hI_a_le : ‖I_a‖ ≤ s ^ 7) (hI_b_le : ‖I_b‖ ≤ s ^ 7)
    (h_aH₂_le : ‖a * H₂‖ ≤ s ^ 7) (h_H₁b_le : ‖H₁ * b‖ ≤ s ^ 7)
    (h_F₁F₂_le : ‖F₁ * F₂‖ ≤ s ^ 8)
    (h_F₁b3_le : ‖F₁ * b ^ 3‖ ≤ s ^ 7)
    (h_a3F₂_le : ‖a ^ 3 * F₂‖ ≤ s ^ 7)
    (h_G₁b2_le : ‖G₁ * b ^ 2‖ ≤ s ^ 7)
    (h_a2G₂_le : ‖a ^ 2 * G₂‖ ≤ s ^ 7) :
    ‖I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
      (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂) +
      (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * G₂)‖ ≤ 7 * s ^ 7 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hs7_le_s7 : s ^ 8 ≤ s ^ 7 := by
    have h : s ^ 8 = s ^ 7 * s := by ring
    rw [h]
    nlinarith [pow_nonneg hs_nn 7]
  have h_F₁b3_smul : ‖(6 : 𝕂)⁻¹ • (F₁ * b ^ 3)‖ ≤ s ^ 7 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖F₁ * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 7 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_F₁b3_le (by norm_num)
      _ = s ^ 7 / 6 := by ring
  have h_a3F₂_smul : ‖(6 : 𝕂)⁻¹ • (a ^ 3 * F₂)‖ ≤ s ^ 7 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖a ^ 3 * F₂‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 7 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_a3F₂_le (by norm_num)
      _ = s ^ 7 / 6 := by ring
  have h_G₁b2_smul : ‖(2 : 𝕂)⁻¹ • (G₁ * b ^ 2)‖ ≤ s ^ 7 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖G₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 7 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_G₁b2_le (by norm_num)
      _ = s ^ 7 / 2 := by ring
  have h_a2G₂_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * G₂)‖ ≤ s ^ 7 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * G₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 7 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2G₂_le (by norm_num)
      _ = s ^ 7 / 2 := by ring
  -- 8-term sum via triangle inequality (8 norm_add_le).
  have ha1 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂) +
    (2 : 𝕂)⁻¹ • (G₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * G₂))
  have ha2 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂))
    ((2 : 𝕂)⁻¹ • (G₁ * b ^ 2))
  have ha3 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (F₁ * b ^ 3)) ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂))
  have ha4 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂)
    ((6 : 𝕂)⁻¹ • (F₁ * b ^ 3))
  have ha5 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b) (F₁ * F₂)
  have ha6 := norm_add_le (I_a + I_b + a * H₂) (H₁ * b)
  have ha7 := norm_add_le (I_a + I_b) (a * H₂)
  have ha8 := norm_add_le I_a I_b
  -- Sum: 4·s⁷ + s⁸ + 2·s⁷/6 + s⁷ = 4s⁷ + 1/3·s⁷ + s⁷ + ε = 16/3·s⁷ + s⁸ ≤ 7·s⁷
  linarith [pow_nonneg hs_nn 7]

/-- Norm bound `‖R+T₅+T₆+T₇ residual sum‖ ≤ 7·s⁸` from precomputed component bounds.
The 9 terms come from `R_plus_T5_plus_T6_plus_T7_eq_neg_deg8_residual`:
J_a+J_b+a·I_b+I_a·b+F₁·F₂+⅙·G₁·b³+⅙·a³·G₂+½·H₁·b²+½·a²·H₂.

Analog of `norm_R_plus_T5_plus_T6_residual_sum_le` at one degree higher. All
inputs are deg-8+ inherently (the F₁·F₂ term has deg-4+4 = 8 leading, so no
`s ≤ 1` folding is needed at this level). Forward-looking infrastructure for
the eventual deg-9-parent T2-F7e-octic discharge. -/
private theorem norm_R_plus_T5_plus_T6_plus_T7_residual_sum_le
    (J_a J_b I_a I_b H₁ H₂ G₁ G₂ F₁ F₂ a b : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s)
    (hJ_a_le : ‖J_a‖ ≤ s ^ 8) (hJ_b_le : ‖J_b‖ ≤ s ^ 8)
    (h_aI_b_le : ‖a * I_b‖ ≤ s ^ 8) (h_I_ab_le : ‖I_a * b‖ ≤ s ^ 8)
    (h_F₁F₂_le : ‖F₁ * F₂‖ ≤ s ^ 8)
    (h_G₁b3_le : ‖G₁ * b ^ 3‖ ≤ s ^ 8)
    (h_a3G₂_le : ‖a ^ 3 * G₂‖ ≤ s ^ 8)
    (h_H₁b2_le : ‖H₁ * b ^ 2‖ ≤ s ^ 8)
    (h_a2H₂_le : ‖a ^ 2 * H₂‖ ≤ s ^ 8) :
    ‖J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
      (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂) +
      (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * H₂)‖ ≤ 7 * s ^ 8 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_G₁b3_smul : ‖(6 : 𝕂)⁻¹ • (G₁ * b ^ 3)‖ ≤ s ^ 8 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖G₁ * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 8 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_G₁b3_le (by norm_num)
      _ = s ^ 8 / 6 := by ring
  have h_a3G₂_smul : ‖(6 : 𝕂)⁻¹ • (a ^ 3 * G₂)‖ ≤ s ^ 8 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖a ^ 3 * G₂‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 8 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_a3G₂_le (by norm_num)
      _ = s ^ 8 / 6 := by ring
  have h_H₁b2_smul : ‖(2 : 𝕂)⁻¹ • (H₁ * b ^ 2)‖ ≤ s ^ 8 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖H₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 8 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_H₁b2_le (by norm_num)
      _ = s ^ 8 / 2 := by ring
  have h_a2H₂_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * H₂)‖ ≤ s ^ 8 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * H₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 8 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2H₂_le (by norm_num)
      _ = s ^ 8 / 2 := by ring
  -- 8-term sum via triangle inequality (8 norm_add_le).
  have ha1 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂) +
    (2 : 𝕂)⁻¹ • (H₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * H₂))
  have ha2 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂))
    ((2 : 𝕂)⁻¹ • (H₁ * b ^ 2))
  have ha3 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂ +
    (6 : 𝕂)⁻¹ • (G₁ * b ^ 3)) ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂))
  have ha4 := norm_add_le (J_a + J_b + a * I_b + I_a * b + F₁ * F₂)
    ((6 : 𝕂)⁻¹ • (G₁ * b ^ 3))
  have ha5 := norm_add_le (J_a + J_b + a * I_b + I_a * b) (F₁ * F₂)
  have ha6 := norm_add_le (J_a + J_b + a * I_b) (I_a * b)
  have ha7 := norm_add_le (J_a + J_b) (a * I_b)
  have ha8 := norm_add_le J_a J_b
  -- Sum: 4·s⁸ + s⁸ + 2·s⁸/6 + 2·s⁸/2 = 4 + 1 + 1/3 + 1 = 19/3·s⁸ ≈ 6.34·s⁸ ≤ 7·s⁸.
  linarith [pow_nonneg hs_nn 8]

/-- Norm bound `‖T₄‖ ≤ s⁴` where T₄ = (1/24)·a⁴ + (1/6)·a³b + (1/4)·a²b² +
(1/6)·ab³ + (1/24)·b⁴ is the deg-4 contribution of `exp(a)·exp(b)-1`.
Sum of |coefficients| = 16/24 = 2/3 ≤ 1, so ‖T₄‖ ≤ (2/3)·s⁴ ≤ s⁴. -/
private theorem norm_T4_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖(24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
      (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
      (24 : 𝕂)⁻¹ • b ^ 4‖ ≤ s ^ 4 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have h4eq : ‖(4 : 𝕂)⁻¹‖ = (4 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h24eq : ‖(24 : 𝕂)⁻¹‖ = (24 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hT1 : ‖(24:𝕂)⁻¹ • a ^ 4‖ ≤ α ^ 4 / 24 := by
    calc _ ≤ ‖(24:𝕂)⁻¹‖ * ‖a ^ 4‖ := norm_smul_le _ _
      _ ≤ (24:ℝ)⁻¹ * α ^ 4 := by
          rw [h24eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = α ^ 4 / 24 := by ring
  have hT2 : ‖(6:𝕂)⁻¹ • (a ^ 3 * b)‖ ≤ α ^ 3 * β / 6 :=
    calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖a ^ 3 * b‖ := norm_smul_le _ _
      _ ≤ (6:ℝ)⁻¹ * (α ^ 3 * β) := by
          rw [h6eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn
              (by positivity))) (by norm_num)
      _ = α ^ 3 * β / 6 := by ring
  have hT3 : ‖(4:𝕂)⁻¹ • (a ^ 2 * b ^ 2)‖ ≤ α ^ 2 * β ^ 2 / 4 :=
    calc _ ≤ ‖(4:𝕂)⁻¹‖ * ‖a ^ 2 * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (4:ℝ)⁻¹ * (α ^ 2 * β ^ 2) := by
          rw [h4eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 2 * β ^ 2 / 4 := by ring
  have hT4 : ‖(6:𝕂)⁻¹ • (a * b ^ 3)‖ ≤ α * β ^ 3 / 6 :=
    calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖a * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (6:ℝ)⁻¹ * (α * β ^ 3) := by
          rw [h6eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul le_rfl (norm_pow_le _ _)
              (by positivity) hα_nn)) (by norm_num)
      _ = α * β ^ 3 / 6 := by ring
  have hT5 : ‖(24:𝕂)⁻¹ • b ^ 4‖ ≤ β ^ 4 / 24 :=
    calc _ ≤ ‖(24:𝕂)⁻¹‖ * ‖b ^ 4‖ := norm_smul_le _ _
      _ ≤ (24:ℝ)⁻¹ * β ^ 4 := by
          rw [h24eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = β ^ 4 / 24 := by ring
  have ha1 := norm_add_le ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
    (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3)) ((24 : 𝕂)⁻¹ • b ^ 4)
  have ha2 := norm_add_le ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
    (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2)) ((6 : 𝕂)⁻¹ • (a * b ^ 3))
  have ha3 := norm_add_le ((24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b))
    ((4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2))
  have ha4 := norm_add_le ((24 : 𝕂)⁻¹ • a ^ 4) ((6 : 𝕂)⁻¹ • (a ^ 3 * b))
  -- α^k·β^(4-k) ≤ s^4 for each k = 0, 1, 2, 3, 4.
  have ha4s : α ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ hα_nn hα_le 4
  have hb4s : β ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ hβ_nn hβ_le 4
  have ha3bs : α ^ 3 * β ≤ s ^ 4 := by
    calc α ^ 3 * β ≤ s ^ 3 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3) hβ_le
          hβ_nn (by positivity)
      _ = s ^ 4 := by ring
  have ha2b2s : α ^ 2 * β ^ 2 ≤ s ^ 4 := by
    calc α ^ 2 * β ^ 2 ≤ s ^ 2 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 4 := by ring
  have hab3s : α * β ^ 3 ≤ s ^ 4 := by
    calc α * β ^ 3 ≤ s * s ^ 3 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 3)
          (by positivity) hs_nn
      _ = s ^ 4 := by ring
  -- Sum: α⁴/24 + α³β/6 + α²β²/4 + αβ³/6 + β⁴/24 ≤ s⁴·(1/24+1/6+1/4+1/6+1/24) = (2/3)·s⁴ ≤ s⁴.
  nlinarith [pow_nonneg hs_nn 4]

/-- Norm bound `‖T₅‖ ≤ s⁵` where T₅ = (1/120)·a⁵ + (1/24)·a⁴b + (1/12)·a³b² +
(1/12)·a²b³ + (1/24)·ab⁴ + (1/120)·b⁵ is the deg-5 contribution of
`exp(a)·exp(b)-1`. Sum of |coefficients| = 32/120 = 4/15 ≤ 1, so
‖T₅‖ ≤ (4/15)·s⁵ ≤ s⁵. -/
private theorem norm_T5_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖(120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
      (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
      (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5‖ ≤ s ^ 5 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have h12eq : ‖(12 : 𝕂)⁻¹‖ = (12 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h24eq : ‖(24 : 𝕂)⁻¹‖ = (24 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h120eq : ‖(120 : 𝕂)⁻¹‖ = (120 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hT1 : ‖(120:𝕂)⁻¹ • a ^ 5‖ ≤ α ^ 5 / 120 :=
    calc _ ≤ ‖(120:𝕂)⁻¹‖ * ‖a ^ 5‖ := norm_smul_le _ _
      _ ≤ (120:ℝ)⁻¹ * α ^ 5 := by
          rw [h120eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = α ^ 5 / 120 := by ring
  have hT2 : ‖(24:𝕂)⁻¹ • (a ^ 4 * b)‖ ≤ α ^ 4 * β / 24 :=
    calc _ ≤ ‖(24:𝕂)⁻¹‖ * ‖a ^ 4 * b‖ := norm_smul_le _ _
      _ ≤ (24:ℝ)⁻¹ * (α ^ 4 * β) := by
          rw [h24eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn
              (by positivity))) (by norm_num)
      _ = α ^ 4 * β / 24 := by ring
  have hT3 : ‖(12:𝕂)⁻¹ • (a ^ 3 * b ^ 2)‖ ≤ α ^ 3 * β ^ 2 / 12 :=
    calc _ ≤ ‖(12:𝕂)⁻¹‖ * ‖a ^ 3 * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (12:ℝ)⁻¹ * (α ^ 3 * β ^ 2) := by
          rw [h12eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 3 * β ^ 2 / 12 := by ring
  have hT4 : ‖(12:𝕂)⁻¹ • (a ^ 2 * b ^ 3)‖ ≤ α ^ 2 * β ^ 3 / 12 :=
    calc _ ≤ ‖(12:𝕂)⁻¹‖ * ‖a ^ 2 * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (12:ℝ)⁻¹ * (α ^ 2 * β ^ 3) := by
          rw [h12eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 2 * β ^ 3 / 12 := by ring
  have hT5 : ‖(24:𝕂)⁻¹ • (a * b ^ 4)‖ ≤ α * β ^ 4 / 24 :=
    calc _ ≤ ‖(24:𝕂)⁻¹‖ * ‖a * b ^ 4‖ := norm_smul_le _ _
      _ ≤ (24:ℝ)⁻¹ * (α * β ^ 4) := by
          rw [h24eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul le_rfl (norm_pow_le _ _)
              (by positivity) hα_nn)) (by norm_num)
      _ = α * β ^ 4 / 24 := by ring
  have hT6 : ‖(120:𝕂)⁻¹ • b ^ 5‖ ≤ β ^ 5 / 120 :=
    calc _ ≤ ‖(120:𝕂)⁻¹‖ * ‖b ^ 5‖ := norm_smul_le _ _
      _ ≤ (120:ℝ)⁻¹ * β ^ 5 := by
          rw [h120eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = β ^ 5 / 120 := by ring
  have ha1 := norm_add_le ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
    (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
    (24 : 𝕂)⁻¹ • (a * b ^ 4)) ((120 : 𝕂)⁻¹ • b ^ 5)
  have ha2 := norm_add_le ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
    (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3))
    ((24 : 𝕂)⁻¹ • (a * b ^ 4))
  have ha3 := norm_add_le ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
    (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2)) ((12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3))
  have ha4 := norm_add_le ((120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b))
    ((12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2))
  have ha5 := norm_add_le ((120 : 𝕂)⁻¹ • a ^ 5) ((24 : 𝕂)⁻¹ • (a ^ 4 * b))
  -- α^k·β^(5-k) ≤ s^5.
  have ha5s : α ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ hα_nn hα_le 5
  have hb5s : β ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ hβ_nn hβ_le 5
  have ha4bs : α ^ 4 * β ≤ s ^ 5 := by
    calc α ^ 4 * β ≤ s ^ 4 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4) hβ_le
          hβ_nn (by positivity)
      _ = s ^ 5 := by ring
  have ha3b2s : α ^ 3 * β ^ 2 ≤ s ^ 5 := by
    calc α ^ 3 * β ^ 2 ≤ s ^ 3 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have ha2b3s : α ^ 2 * β ^ 3 ≤ s ^ 5 := by
    calc α ^ 2 * β ^ 3 ≤ s ^ 2 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have hab4s : α * β ^ 4 ≤ s ^ 5 := by
    calc α * β ^ 4 ≤ s * s ^ 4 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 4)
          (by positivity) hs_nn
      _ = s ^ 5 := by ring
  -- Sum: α⁵/120 + α⁴β/24 + α³β²/12 + α²β³/12 + αβ⁴/24 + β⁵/120 ≤ s⁵·(1/120+1/24+1/12+1/12+1/24+1/120)
  --       = s⁵·(1+5+10+10+5+1)/120 = 32/120·s⁵ = (4/15)·s⁵ ≤ s⁵.
  nlinarith [pow_nonneg hs_nn 5]

/-- Norm bound `‖T₆‖ ≤ s⁶` where T₆ = (1/720)·a⁶ + (1/120)·a⁵b + (1/48)·a⁴b² +
(1/36)·a³b³ + (1/48)·a²b⁴ + (1/120)·ab⁵ + (1/720)·b⁶ is the deg-6
contribution of `exp(a)·exp(b)-1`. Sum of |coefficients| =
(1+6+15+20+15+6+1)/720 = 64/720 = 4/45 ≤ 1, so ‖T₆‖ ≤ (4/45)·s⁶ ≤ s⁶. -/
private theorem norm_T6_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖(720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
      (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
      (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
      (720 : 𝕂)⁻¹ • b ^ 6‖ ≤ s ^ 6 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have h36eq : ‖(36 : 𝕂)⁻¹‖ = (36 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h48eq : ‖(48 : 𝕂)⁻¹‖ = (48 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h120eq : ‖(120 : 𝕂)⁻¹‖ = (120 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h720eq : ‖(720 : 𝕂)⁻¹‖ = (720 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hT1 : ‖(720:𝕂)⁻¹ • a ^ 6‖ ≤ α ^ 6 / 720 :=
    calc _ ≤ ‖(720:𝕂)⁻¹‖ * ‖a ^ 6‖ := norm_smul_le _ _
      _ ≤ (720:ℝ)⁻¹ * α ^ 6 := by
          rw [h720eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = α ^ 6 / 720 := by ring
  have hT2 : ‖(120:𝕂)⁻¹ • (a ^ 5 * b)‖ ≤ α ^ 5 * β / 120 :=
    calc _ ≤ ‖(120:𝕂)⁻¹‖ * ‖a ^ 5 * b‖ := norm_smul_le _ _
      _ ≤ (120:ℝ)⁻¹ * (α ^ 5 * β) := by
          rw [h120eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn
              (by positivity))) (by norm_num)
      _ = α ^ 5 * β / 120 := by ring
  have hT3 : ‖(48:𝕂)⁻¹ • (a ^ 4 * b ^ 2)‖ ≤ α ^ 4 * β ^ 2 / 48 :=
    calc _ ≤ ‖(48:𝕂)⁻¹‖ * ‖a ^ 4 * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (48:ℝ)⁻¹ * (α ^ 4 * β ^ 2) := by
          rw [h48eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 4 * β ^ 2 / 48 := by ring
  have hT4 : ‖(36:𝕂)⁻¹ • (a ^ 3 * b ^ 3)‖ ≤ α ^ 3 * β ^ 3 / 36 :=
    calc _ ≤ ‖(36:𝕂)⁻¹‖ * ‖a ^ 3 * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (36:ℝ)⁻¹ * (α ^ 3 * β ^ 3) := by
          rw [h36eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 3 * β ^ 3 / 36 := by ring
  have hT5 : ‖(48:𝕂)⁻¹ • (a ^ 2 * b ^ 4)‖ ≤ α ^ 2 * β ^ 4 / 48 :=
    calc _ ≤ ‖(48:𝕂)⁻¹‖ * ‖a ^ 2 * b ^ 4‖ := norm_smul_le _ _
      _ ≤ (48:ℝ)⁻¹ * (α ^ 2 * β ^ 4) := by
          rw [h48eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 2 * β ^ 4 / 48 := by ring
  have hT6 : ‖(120:𝕂)⁻¹ • (a * b ^ 5)‖ ≤ α * β ^ 5 / 120 :=
    calc _ ≤ ‖(120:𝕂)⁻¹‖ * ‖a * b ^ 5‖ := norm_smul_le _ _
      _ ≤ (120:ℝ)⁻¹ * (α * β ^ 5) := by
          rw [h120eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul le_rfl (norm_pow_le _ _)
              (by positivity) hα_nn)) (by norm_num)
      _ = α * β ^ 5 / 120 := by ring
  have hT7 : ‖(720:𝕂)⁻¹ • b ^ 6‖ ≤ β ^ 6 / 720 :=
    calc _ ≤ ‖(720:𝕂)⁻¹‖ * ‖b ^ 6‖ := norm_smul_le _ _
      _ ≤ (720:ℝ)⁻¹ * β ^ 6 := by
          rw [h720eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = β ^ 6 / 720 := by ring
  have ha1 := norm_add_le ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
    (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
    (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5))
    ((720 : 𝕂)⁻¹ • b ^ 6)
  have ha2 := norm_add_le ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
    (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
    (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4)) ((120 : 𝕂)⁻¹ • (a * b ^ 5))
  have ha3 := norm_add_le ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
    (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3))
    ((48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4))
  have ha4 := norm_add_le ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
    (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2)) ((36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3))
  have ha5 := norm_add_le ((720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b))
    ((48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2))
  have ha6 := norm_add_le ((720 : 𝕂)⁻¹ • a ^ 6) ((120 : 𝕂)⁻¹ • (a ^ 5 * b))
  -- α^k·β^(6-k) ≤ s^6.
  have ha6s : α ^ 6 ≤ s ^ 6 := pow_le_pow_left₀ hα_nn hα_le 6
  have hb6s : β ^ 6 ≤ s ^ 6 := pow_le_pow_left₀ hβ_nn hβ_le 6
  have ha5bs : α ^ 5 * β ≤ s ^ 6 := by
    calc α ^ 5 * β ≤ s ^ 5 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5) hβ_le
          hβ_nn (by positivity)
      _ = s ^ 6 := by ring
  have ha4b2s : α ^ 4 * β ^ 2 ≤ s ^ 6 := by
    calc α ^ 4 * β ^ 2 ≤ s ^ 4 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have ha3b3s : α ^ 3 * β ^ 3 ≤ s ^ 6 := by
    calc α ^ 3 * β ^ 3 ≤ s ^ 3 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have ha2b4s : α ^ 2 * β ^ 4 ≤ s ^ 6 := by
    calc α ^ 2 * β ^ 4 ≤ s ^ 2 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have hab5s : α * β ^ 5 ≤ s ^ 6 := by
    calc α * β ^ 5 ≤ s * s ^ 5 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 5)
          (by positivity) hs_nn
      _ = s ^ 6 := by ring
  -- Sum: α⁶/720 + α⁵β/120 + α⁴β²/48 + α³β³/36 + α²β⁴/48 + αβ⁵/120 + β⁶/720
  --   ≤ s⁶·(1/720+1/120+1/48+1/36+1/48+1/120+1/720) = (1+6+15+20+15+6+1)/720·s⁶
  --   = 64/720·s⁶ = (4/45)·s⁶ ≤ s⁶.
  nlinarith [pow_nonneg hs_nn 6]

/-- Norm bound `‖T₇‖ ≤ s⁷` where
`T₇ = (1/5040)·a⁷ + (1/720)·a⁶b + (1/240)·a⁵b² + (1/144)·a⁴b³ +
      (1/144)·a³b⁴ + (1/240)·a²b⁵ + (1/720)·ab⁶ + (1/5040)·b⁷`
is the deg-7 contribution of `exp(a)·exp(b)-1`. Sum of |coefficients| =
(1+7+21+35+35+21+7+1)/5040 = 128/5040 ≈ 0.0254, so `‖T₇‖ ≤ s⁷`. -/
private theorem norm_T7_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖(5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
      (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
      (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
      (720 : 𝕂)⁻¹ • (a * b ^ 6) + (5040 : 𝕂)⁻¹ • b ^ 7‖ ≤ s ^ 7 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have h144eq : ‖(144 : 𝕂)⁻¹‖ = (144 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h240eq : ‖(240 : 𝕂)⁻¹‖ = (240 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h720eq : ‖(720 : 𝕂)⁻¹‖ = (720 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h5040eq : ‖(5040 : 𝕂)⁻¹‖ = (5040 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Per-coefficient bounds.
  have hT1 : ‖(5040 : 𝕂)⁻¹ • a ^ 7‖ ≤ α ^ 7 / 5040 :=
    calc _ ≤ ‖(5040 : 𝕂)⁻¹‖ * ‖a ^ 7‖ := norm_smul_le _ _
      _ ≤ (5040 : ℝ)⁻¹ * α ^ 7 := by
          rw [h5040eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = α ^ 7 / 5040 := by ring
  have hT2 : ‖(720 : 𝕂)⁻¹ • (a ^ 6 * b)‖ ≤ α ^ 6 * β / 720 :=
    calc _ ≤ ‖(720 : 𝕂)⁻¹‖ * ‖a ^ 6 * b‖ := norm_smul_le _ _
      _ ≤ (720 : ℝ)⁻¹ * (α ^ 6 * β) := by
          rw [h720eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn
              (by positivity))) (by norm_num)
      _ = α ^ 6 * β / 720 := by ring
  have hT3 : ‖(240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2)‖ ≤ α ^ 5 * β ^ 2 / 240 :=
    calc _ ≤ ‖(240 : 𝕂)⁻¹‖ * ‖a ^ 5 * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (240 : ℝ)⁻¹ * (α ^ 5 * β ^ 2) := by
          rw [h240eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 5 * β ^ 2 / 240 := by ring
  have hT4 : ‖(144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3)‖ ≤ α ^ 4 * β ^ 3 / 144 :=
    calc _ ≤ ‖(144 : 𝕂)⁻¹‖ * ‖a ^ 4 * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (144 : ℝ)⁻¹ * (α ^ 4 * β ^ 3) := by
          rw [h144eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 4 * β ^ 3 / 144 := by ring
  have hT5 : ‖(144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4)‖ ≤ α ^ 3 * β ^ 4 / 144 :=
    calc _ ≤ ‖(144 : 𝕂)⁻¹‖ * ‖a ^ 3 * b ^ 4‖ := norm_smul_le _ _
      _ ≤ (144 : ℝ)⁻¹ * (α ^ 3 * β ^ 4) := by
          rw [h144eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 3 * β ^ 4 / 144 := by ring
  have hT6 : ‖(240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5)‖ ≤ α ^ 2 * β ^ 5 / 240 :=
    calc _ ≤ ‖(240 : 𝕂)⁻¹‖ * ‖a ^ 2 * b ^ 5‖ := norm_smul_le _ _
      _ ≤ (240 : ℝ)⁻¹ * (α ^ 2 * β ^ 5) := by
          rw [h240eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 2 * β ^ 5 / 240 := by ring
  have hT7 : ‖(720 : 𝕂)⁻¹ • (a * b ^ 6)‖ ≤ α * β ^ 6 / 720 :=
    calc _ ≤ ‖(720 : 𝕂)⁻¹‖ * ‖a * b ^ 6‖ := norm_smul_le _ _
      _ ≤ (720 : ℝ)⁻¹ * (α * β ^ 6) := by
          rw [h720eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul le_rfl (norm_pow_le _ _)
              (by positivity) hα_nn)) (by norm_num)
      _ = α * β ^ 6 / 720 := by ring
  have hT8 : ‖(5040 : 𝕂)⁻¹ • b ^ 7‖ ≤ β ^ 7 / 5040 :=
    calc _ ≤ ‖(5040 : 𝕂)⁻¹‖ * ‖b ^ 7‖ := norm_smul_le _ _
      _ ≤ (5040 : ℝ)⁻¹ * β ^ 7 := by
          rw [h5040eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = β ^ 7 / 5040 := by ring
  -- Triangle inequality (7 norm_add_le applications).
  have ha1 := norm_add_le ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
    (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
    (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
    (720 : 𝕂)⁻¹ • (a * b ^ 6)) ((5040 : 𝕂)⁻¹ • b ^ 7)
  have ha2 := norm_add_le ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
    (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
    (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5))
    ((720 : 𝕂)⁻¹ • (a * b ^ 6))
  have ha3 := norm_add_le ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
    (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
    (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4)) ((240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5))
  have ha4 := norm_add_le ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
    (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3))
    ((144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4))
  have ha5 := norm_add_le ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
    (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2)) ((144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3))
  have ha6 := norm_add_le ((5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b))
    ((240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2))
  have ha7 := norm_add_le ((5040 : 𝕂)⁻¹ • a ^ 7) ((720 : 𝕂)⁻¹ • (a ^ 6 * b))
  -- α^k·β^(7-k) ≤ s^7.
  have ha7s : α ^ 7 ≤ s ^ 7 := pow_le_pow_left₀ hα_nn hα_le 7
  have hb7s : β ^ 7 ≤ s ^ 7 := pow_le_pow_left₀ hβ_nn hβ_le 7
  have ha6bs : α ^ 6 * β ≤ s ^ 7 := by
    calc α ^ 6 * β ≤ s ^ 6 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 6) hβ_le
          hβ_nn (by positivity)
      _ = s ^ 7 := by ring
  have ha5b2s : α ^ 5 * β ^ 2 ≤ s ^ 7 := by
    calc α ^ 5 * β ^ 2 ≤ s ^ 5 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have ha4b3s : α ^ 4 * β ^ 3 ≤ s ^ 7 := by
    calc α ^ 4 * β ^ 3 ≤ s ^ 4 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have ha3b4s : α ^ 3 * β ^ 4 ≤ s ^ 7 := by
    calc α ^ 3 * β ^ 4 ≤ s ^ 3 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have ha2b5s : α ^ 2 * β ^ 5 ≤ s ^ 7 := by
    calc α ^ 2 * β ^ 5 ≤ s ^ 2 * s ^ 5 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 5) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have hab6s : α * β ^ 6 ≤ s ^ 7 := by
    calc α * β ^ 6 ≤ s * s ^ 6 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 6)
          (by positivity) hs_nn
      _ = s ^ 7 := by ring
  -- Sum: α⁷/5040 + α⁶β/720 + α⁵β²/240 + α⁴β³/144 + α³β⁴/144 + α²β⁵/240 + αβ⁶/720 + β⁷/5040
  --   ≤ s⁷·(1+7+21+35+35+21+7+1)/5040 = 128/5040·s⁷ = (8/315)·s⁷ ≤ s⁷.
  nlinarith [pow_nonneg hs_nn 7]

/-- Norm bound `‖T₈‖ ≤ s⁸` where
`T₈ = (1/40320)·a⁸ + (1/5040)·a⁷b + (1/1440)·a⁶b² + (1/720)·a⁵b³ +
      (1/576)·a⁴b⁴ + (1/720)·a³b⁵ + (1/1440)·a²b⁶ + (1/5040)·ab⁷ +
      (1/40320)·b⁸`
is the deg-8 contribution of `exp(a)·exp(b)-1`. Sum of |coefficients|·LCM =
(1+8+28+56+70+56+28+8+1)/40320 = 256/40320 = 2/315 ≈ 0.00635, so `‖T₈‖ ≤ s⁸`.

Deg-8 analog of `norm_T7_le` (session 31). Standalone helper for the
forward-looking deg-9-parent T2-F7e-octic discharge infrastructure. -/
private theorem norm_T8_le (a b : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hα_le : ‖a‖ ≤ s) (hβ_le : ‖b‖ ≤ s) :
    ‖(40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b) +
      (1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3) +
      (576 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4) + (720 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5) +
      (1440 : 𝕂)⁻¹ • (a ^ 2 * b ^ 6) + (5040 : 𝕂)⁻¹ • (a * b ^ 7) +
      (40320 : 𝕂)⁻¹ • b ^ 8‖ ≤ s ^ 8 := by
  set α := ‖a‖
  set β := ‖b‖
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have h576eq : ‖(576 : 𝕂)⁻¹‖ = (576 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h720eq : ‖(720 : 𝕂)⁻¹‖ = (720 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h1440eq : ‖(1440 : 𝕂)⁻¹‖ = (1440 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h5040eq : ‖(5040 : 𝕂)⁻¹‖ = (5040 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h40320eq : ‖(40320 : 𝕂)⁻¹‖ = (40320 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Per-coefficient bounds.
  have hT1 : ‖(40320 : 𝕂)⁻¹ • a ^ 8‖ ≤ α ^ 8 / 40320 :=
    calc _ ≤ ‖(40320 : 𝕂)⁻¹‖ * ‖a ^ 8‖ := norm_smul_le _ _
      _ ≤ (40320 : ℝ)⁻¹ * α ^ 8 := by
          rw [h40320eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = α ^ 8 / 40320 := by ring
  have hT2 : ‖(5040 : 𝕂)⁻¹ • (a ^ 7 * b)‖ ≤ α ^ 7 * β / 5040 :=
    calc _ ≤ ‖(5040 : 𝕂)⁻¹‖ * ‖a ^ 7 * b‖ := norm_smul_le _ _
      _ ≤ (5040 : ℝ)⁻¹ * (α ^ 7 * β) := by
          rw [h5040eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn
              (by positivity))) (by norm_num)
      _ = α ^ 7 * β / 5040 := by ring
  have hT3 : ‖(1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2)‖ ≤ α ^ 6 * β ^ 2 / 1440 :=
    calc _ ≤ ‖(1440 : 𝕂)⁻¹‖ * ‖a ^ 6 * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (1440 : ℝ)⁻¹ * (α ^ 6 * β ^ 2) := by
          rw [h1440eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 6 * β ^ 2 / 1440 := by ring
  have hT4 : ‖(720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3)‖ ≤ α ^ 5 * β ^ 3 / 720 :=
    calc _ ≤ ‖(720 : 𝕂)⁻¹‖ * ‖a ^ 5 * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (720 : ℝ)⁻¹ * (α ^ 5 * β ^ 3) := by
          rw [h720eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 5 * β ^ 3 / 720 := by ring
  have hT5 : ‖(576 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4)‖ ≤ α ^ 4 * β ^ 4 / 576 :=
    calc _ ≤ ‖(576 : 𝕂)⁻¹‖ * ‖a ^ 4 * b ^ 4‖ := norm_smul_le _ _
      _ ≤ (576 : ℝ)⁻¹ * (α ^ 4 * β ^ 4) := by
          rw [h576eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 4 * β ^ 4 / 576 := by ring
  have hT6 : ‖(720 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5)‖ ≤ α ^ 3 * β ^ 5 / 720 :=
    calc _ ≤ ‖(720 : 𝕂)⁻¹‖ * ‖a ^ 3 * b ^ 5‖ := norm_smul_le _ _
      _ ≤ (720 : ℝ)⁻¹ * (α ^ 3 * β ^ 5) := by
          rw [h720eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 3 * β ^ 5 / 720 := by ring
  have hT7 : ‖(1440 : 𝕂)⁻¹ • (a ^ 2 * b ^ 6)‖ ≤ α ^ 2 * β ^ 6 / 1440 :=
    calc _ ≤ ‖(1440 : 𝕂)⁻¹‖ * ‖a ^ 2 * b ^ 6‖ := norm_smul_le _ _
      _ ≤ (1440 : ℝ)⁻¹ * (α ^ 2 * β ^ 6) := by
          rw [h1440eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (by positivity))) (by norm_num)
      _ = α ^ 2 * β ^ 6 / 1440 := by ring
  have hT8 : ‖(5040 : 𝕂)⁻¹ • (a * b ^ 7)‖ ≤ α * β ^ 7 / 5040 :=
    calc _ ≤ ‖(5040 : 𝕂)⁻¹‖ * ‖a * b ^ 7‖ := norm_smul_le _ _
      _ ≤ (5040 : ℝ)⁻¹ * (α * β ^ 7) := by
          rw [h5040eq]
          exact mul_le_mul_of_nonneg_left
            ((norm_mul_le _ _).trans (mul_le_mul le_rfl (norm_pow_le _ _)
              (by positivity) hα_nn)) (by norm_num)
      _ = α * β ^ 7 / 5040 := by ring
  have hT9 : ‖(40320 : 𝕂)⁻¹ • b ^ 8‖ ≤ β ^ 8 / 40320 :=
    calc _ ≤ ‖(40320 : 𝕂)⁻¹‖ * ‖b ^ 8‖ := norm_smul_le _ _
      _ ≤ (40320 : ℝ)⁻¹ * β ^ 8 := by
          rw [h40320eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
      _ = β ^ 8 / 40320 := by ring
  -- Triangle inequality (8 norm_add_le applications).
  have ha1 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b) +
    (1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3) +
    (576 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4) + (720 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5) +
    (1440 : 𝕂)⁻¹ • (a ^ 2 * b ^ 6) + (5040 : 𝕂)⁻¹ • (a * b ^ 7))
    ((40320 : 𝕂)⁻¹ • b ^ 8)
  have ha2 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b) +
    (1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3) +
    (576 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4) + (720 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5) +
    (1440 : 𝕂)⁻¹ • (a ^ 2 * b ^ 6))
    ((5040 : 𝕂)⁻¹ • (a * b ^ 7))
  have ha3 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b) +
    (1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3) +
    (576 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4) + (720 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5))
    ((1440 : 𝕂)⁻¹ • (a ^ 2 * b ^ 6))
  have ha4 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b) +
    (1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3) +
    (576 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4))
    ((720 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5))
  have ha5 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b) +
    (1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3))
    ((576 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4))
  have ha6 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b) +
    (1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2)) ((720 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3))
  have ha7 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8 + (5040 : 𝕂)⁻¹ • (a ^ 7 * b))
    ((1440 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2))
  have ha8 := norm_add_le ((40320 : 𝕂)⁻¹ • a ^ 8) ((5040 : 𝕂)⁻¹ • (a ^ 7 * b))
  -- α^k·β^(8-k) ≤ s^8 for each k = 0, 1, ..., 8.
  have ha8s : α ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ hα_nn hα_le 8
  have hb8s : β ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ hβ_nn hβ_le 8
  have ha7bs : α ^ 7 * β ≤ s ^ 8 := by
    calc α ^ 7 * β ≤ s ^ 7 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 7) hβ_le
          hβ_nn (by positivity)
      _ = s ^ 8 := by ring
  have ha6b2s : α ^ 6 * β ^ 2 ≤ s ^ 8 := by
    calc α ^ 6 * β ^ 2 ≤ s ^ 6 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 6)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have ha5b3s : α ^ 5 * β ^ 3 ≤ s ^ 8 := by
    calc α ^ 5 * β ^ 3 ≤ s ^ 5 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have ha4b4s : α ^ 4 * β ^ 4 ≤ s ^ 8 := by
    calc α ^ 4 * β ^ 4 ≤ s ^ 4 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have ha3b5s : α ^ 3 * β ^ 5 ≤ s ^ 8 := by
    calc α ^ 3 * β ^ 5 ≤ s ^ 3 * s ^ 5 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 5) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have ha2b6s : α ^ 2 * β ^ 6 ≤ s ^ 8 := by
    calc α ^ 2 * β ^ 6 ≤ s ^ 2 * s ^ 6 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 6) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have hab7s : α * β ^ 7 ≤ s ^ 8 := by
    calc α * β ^ 7 ≤ s * s ^ 7 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 7)
          (by positivity) hs_nn
      _ = s ^ 8 := by ring
  -- Sum: α⁸/40320 + α⁷β/5040 + α⁶β²/1440 + α⁵β³/720 + α⁴β⁴/576 + α³β⁵/720 +
  --      α²β⁶/1440 + αβ⁷/5040 + β⁸/40320
  --   ≤ s⁸·(1+8+28+56+70+56+28+8+1)/40320 = 256/40320·s⁸ = (2/315)·s⁸ ≤ s⁸.
  nlinarith [pow_nonneg hs_nn 8]

/-! ### Sixth-order BCH remainder bound

The public theorem `norm_bch_sextic_remainder_le` extends
`norm_bch_quintic_remainder_le` by one degree, providing the order-6 bound
needed for the B1.c (`norm_symmetric_bch_quintic_sub_poly_le`) discharge.

The large-s case (`s ≥ 1/10`) is fully proved as
`norm_bch_sextic_remainder_large_s_le`. The small-s case (`s < 1/10`) is
introduced as a scoped private axiom; the proof requires combining
`pieceB_sextic_decomp` with the per-term bounds (`norm_I1_residual_RHS_le`,
`norm_I2_residual_inner_le`, `norm_y4_sub_z4_sub_y4_5_le`,
`norm_pow5_sub_zpow5_le`) — see Task #17b in `claude/` for the discharge
plan.
-/

set_option maxHeartbeats 4000000000 in
include 𝕂 in
/-- **Sixth-order BCH remainder, small-s case** (Tier-1 of B1.c).

For `s = ‖a‖+‖b‖ < 1/10`: `‖LHS_sextic‖ ≤ 100·s⁶/(2-exp(s))`.

Combines `pieceB_sextic_decomp` (the central decomposition from QPI+SPI)
with per-term bounds: `norm_I1_residual_RHS_le` (S₁ ≤ 20·s⁶),
`norm_I2_residual_inner_le` (→ S₂ ≤ 17·s⁶), `norm_y4_sub_z4_sub_y4_5_le`
(→ S₃ ≤ 8·s⁶), `norm_pow5_sub_zpow5_le` (→ S₄ ≤ 7·s⁶). Total ≤ 52·s⁶.
Plus pieceA ≤ 2·s⁶/(2-exp(s)) for `s ≤ 1/10`. Final ≤ 100·s⁶/(2-exp(s)).

Mirrors the quintic proof's `hH1` + `hI₁_quartic` pattern, extended one
degree higher. -/
private theorem norm_bch_sextic_remainder_small_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b‖ ≤
      100 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  -- SETUP.
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖
  set β := ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hs_small_le : s ≤ 1 / 10 := hs_small.le
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hs1 : s < 1 := by linarith
  have hs34 : s < 3 / 4 := by linarith
  have hs56 : s < 5 / 6 := by linarith
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  set y := exp a * exp b - 1 with hy_def
  set z := a + b with hz_def
  set P := y - z with hP_def
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have hy_eq : y = (exp a - 1) * exp b + (exp b - 1) := by
      rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [hy_eq]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          apply add_le_add
          · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
              (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn,
         Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  have hy_le2 : ‖y‖ ≤ 2 * s := by
    calc ‖y‖ ≤ Real.exp s - 1 := hy_le
      _ ≤ s + s ^ 2 := by linarith
      _ ≤ 2 * s := by nlinarith [sq_nonneg s]
  have hz_le : ‖z‖ ≤ s := by rw [hz_def]; exact norm_add_le _ _
  -- Exp remainders.
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set G₁ := F₁ - (24 : 𝕂)⁻¹ • a ^ 4 with hG₁_def
  set G₂ := F₂ - (24 : 𝕂)⁻¹ • b ^ 4 with hG₂_def
  set H₁ := G₁ - (120 : 𝕂)⁻¹ • a ^ 5 with hH₁_def
  set H₂ := G₂ - (120 : 𝕂)⁻¹ • b ^ 5 with hH₂_def
  set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
  set W_H1 := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
      z * P - P * z - P ^ 2 with hW_H1_def
  set T₂ := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2 with hT₂_def
  -- T₃ in T₃_SPI ordering (matches I1/I2_residual_decomp_eq).
  set T₃ := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
      (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 with hT₃_def
  set T₄ := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
      (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
      (24 : 𝕂)⁻¹ • b ^ 4 with hT₄_def
  set W5 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
      (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
      (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
      (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂) with hW5_def
  set y3_5 := z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
      z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z with hy3_5_def
  set y4_5 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3 with hy4_5_def
  -- Norm bounds for D, E, F, G, H.
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖α‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hα_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDa_nn,
         Real.norm_eq_abs, abs_of_nonneg hα_nn] at h
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖β‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hβ_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDb_nn,
         Real.norm_eq_abs, abs_of_nonneg hβ_nn] at h
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hG₁_le : ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hG₂_le : ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hGa5 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 ≤ α ^ 5 :=
    real_exp_fifth_order_le_quintic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hGb5 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 ≤ β ^ 5 :=
    real_exp_fifth_order_le_quintic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hH₁_le : ‖H₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hH₂_le : ‖H₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hHa6 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 ≤
      α ^ 6 :=
    real_exp_sixth_order_le_sextic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hHb6 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 ≤
      β ^ 6 :=
    real_exp_sixth_order_le_sextic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- ‖P‖ ≤ s² and friends.
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
    have hP_split : P = a * (exp b - 1) + D₁ * exp b + D₂ := by
      simp only [hP_def, hy_def, hz_def, hD₁_def, hD₂_def]; noncomm_ring
    calc ‖P‖ = ‖a * (exp b - 1) + D₁ * exp b + D₂‖ := by rw [hP_split]
      _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
          calc _ ≤ ‖a * (exp b - 1) + D₁ * exp b‖ + ‖D₂‖ := norm_add_le _ _
            _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
                gcongr; exact norm_add_le _ _
      _ ≤ α * (Real.exp β - 1) + (Real.exp α - 1 - α) * Real.exp β +
          (Real.exp β - 1 - β) := by
          have h1 : ‖a * (exp b - 1)‖ ≤ α * (Real.exp β - 1) :=
            calc _ ≤ ‖a‖ * ‖exp b - 1‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_exp_sub_one_le (𝕂 := 𝕂) b
          have h2 : ‖D₁ * exp b‖ ≤ (Real.exp α - 1 - α) * Real.exp β :=
            calc _ ≤ ‖D₁‖ * ‖exp b‖ := norm_mul_le _ _
              _ ≤ _ := mul_le_mul hD₁_le (norm_exp_le (𝕂 := 𝕂) b)
                  (norm_nonneg _) (by linarith)
          linarith [hD₂_le]
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  have hP_le_s2 : ‖P‖ ≤ s ^ 2 := le_trans hP_le hEs2
  have hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3 := by
    have hS_eq : P - T₂ = E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂ := by
      simp only [hP_def, hy_def, hT₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hz_def]
      noncomm_ring
    rw [hS_eq]
    have hE₁_s3 : ‖E₁‖ ≤ α ^ 3 := le_trans hE₁_le hEa3
    have hE₂_s3 : ‖E₂‖ ≤ β ^ 3 := le_trans hE₂_le hEb3
    have haD₂ : ‖a * D₂‖ ≤ α * β ^ 2 :=
      calc _ ≤ ‖a‖ * ‖D₂‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans hD₂_le hDb2) hα_nn
    have hD₁b : ‖D₁ * b‖ ≤ α ^ 2 * β :=
      calc _ ≤ ‖D₁‖ * ‖b‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) le_rfl hβ_nn (by positivity)
    have hDD : ‖D₁ * D₂‖ ≤ α ^ 2 * β ^ 2 :=
      calc _ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
            (norm_nonneg _) (by positivity)
    calc ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖
        ≤ ‖E₁‖ + ‖E₂‖ + ‖a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖ := by
          have := norm_add_le E₁ E₂
          have := norm_add_le (E₁ + E₂) (a * D₂)
          have := norm_add_le (E₁ + E₂ + a * D₂) (D₁ * b)
          have := norm_add_le (E₁ + E₂ + a * D₂ + D₁ * b) (D₁ * D₂)
          linarith
      _ ≤ α ^ 3 + β ^ 3 + α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 := by
          linarith [hE₁_s3, hE₂_s3, haD₂, hD₁b, hDD]
      _ ≤ 5 * s ^ 3 := by
          nlinarith [pow_le_pow_left₀ hα_nn hα_le 3, pow_le_pow_left₀ hβ_nn hβ_le 3,
            pow_le_pow_left₀ hα_nn hα_le 2, pow_le_pow_left₀ hβ_nn hβ_le 2,
            pow_nonneg hs_nn 4]
  have hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4 := by
    have h := norm_P_sub_T2_sub_T3_le (𝕂 := 𝕂) a b hs_nn hs34 hα_le hβ_le
    have hP_unfold : P = exp a * exp b - 1 - (a + b) := by
      rw [hP_def, hy_def, hz_def]
    rw [hP_unfold, hT₂_def, hT₃_def]
    exact h
  have h2_le : ‖(2 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h3eq : ‖(3 : 𝕂)⁻¹‖ = (3 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h4eq : ‖(4 : 𝕂)⁻¹‖ = (4 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h5eq : ‖(5 : 𝕂)⁻¹‖ = (5 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hT₂_le : ‖T₂‖ ≤ s ^ 2 := by
    have h1 : ‖a * b‖ ≤ α * β := norm_mul_le _ _
    have h2 : ‖(2:𝕂)⁻¹ • a^2‖ ≤ α^2 :=
      calc _ ≤ 1 * ‖a‖ ^ 2 := (norm_smul_le _ _).trans
              (mul_le_mul h2_le (norm_pow_le a 2) (norm_nonneg _) (by norm_num))
        _ = α^2 := one_mul _
    have h3 : ‖(2:𝕂)⁻¹ • b^2‖ ≤ β^2 :=
      calc _ ≤ 1 * ‖b‖ ^ 2 := (norm_smul_le _ _).trans
              (mul_le_mul h2_le (norm_pow_le b 2) (norm_nonneg _) (by norm_num))
        _ = β^2 := one_mul _
    have htriangle : ‖T₂‖ ≤ ‖a * b‖ + ‖(2:𝕂)⁻¹ • a^2‖ + ‖(2:𝕂)⁻¹ • b^2‖ := by
      rw [hT₂_def]
      have n1 := norm_add_le (a * b + (2:𝕂)⁻¹ • a^2) ((2:𝕂)⁻¹ • b^2)
      have n2 := norm_add_le (a * b) ((2:𝕂)⁻¹ • a^2)
      linarith
    have hs2 : s^2 = α^2 + 2*α*β + β^2 := by rw [hs_def]; ring
    have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
    linarith
  have hT₃_le : ‖T₃‖ ≤ s ^ 3 := by
    have h6_le : ‖(6:𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
    have h6eq : ‖(6:𝕂)⁻¹‖ = (6:ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
    have hT1 : ‖(6:𝕂)⁻¹ • a^3‖ ≤ α^3 / 6 := by
      calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖a^3‖ := norm_smul_le _ _
        _ ≤ (6:ℝ)⁻¹ * α^3 := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
        _ = α^3 / 6 := by ring
    have hT2 : ‖(2:𝕂)⁻¹ • (a^2*b)‖ ≤ α^2 * β / 2 := by
      have hab_le : ‖a^2*b‖ ≤ α^2 * β :=
        calc _ ≤ ‖a^2‖ * ‖b‖ := norm_mul_le _ _
          _ ≤ α^2 * β := mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn (by positivity)
      calc _ ≤ ‖(2:𝕂)⁻¹‖ * ‖a^2*b‖ := norm_smul_le _ _
        _ ≤ (2:ℝ)⁻¹ * (α^2 * β) := by
            rw [h2eq]; exact mul_le_mul_of_nonneg_left hab_le (by norm_num)
        _ = α^2 * β / 2 := by ring
    have hT3 : ‖(2:𝕂)⁻¹ • (a*b^2)‖ ≤ α * β^2 / 2 := by
      have hab_le : ‖a*b^2‖ ≤ α * β^2 :=
        calc _ ≤ ‖a‖ * ‖b^2‖ := norm_mul_le _ _
          _ ≤ α * β^2 := mul_le_mul le_rfl (norm_pow_le _ _) (by positivity) hα_nn
      calc _ ≤ ‖(2:𝕂)⁻¹‖ * ‖a*b^2‖ := norm_smul_le _ _
        _ ≤ (2:ℝ)⁻¹ * (α * β^2) := by
            rw [h2eq]; exact mul_le_mul_of_nonneg_left hab_le (by norm_num)
        _ = α * β^2 / 2 := by ring
    have hT4 : ‖(6:𝕂)⁻¹ • b^3‖ ≤ β^3 / 6 := by
      calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖b^3‖ := norm_smul_le _ _
        _ ≤ (6:ℝ)⁻¹ * β^3 := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
        _ = β^3 / 6 := by ring
    have htriangle : ‖T₃‖ ≤ ‖(6:𝕂)⁻¹ • a^3‖ + ‖(2:𝕂)⁻¹ • (a^2*b)‖ +
        ‖(2:𝕂)⁻¹ • (a*b^2)‖ + ‖(6:𝕂)⁻¹ • b^3‖ := by
      rw [hT₃_def]
      have n1 := norm_add_le ((6:𝕂)⁻¹ • a^3 + (2:𝕂)⁻¹ • (a^2*b) +
        (2:𝕂)⁻¹ • (a*b^2)) ((6:𝕂)⁻¹ • b^3)
      have n2 := norm_add_le ((6:𝕂)⁻¹ • a^3 + (2:𝕂)⁻¹ • (a^2*b)) ((2:𝕂)⁻¹ • (a*b^2))
      have n3 := norm_add_le ((6:𝕂)⁻¹ • a^3) ((2:𝕂)⁻¹ • (a^2*b))
      linarith
    have hs3 : s^3 = α^3 + 3*α^2*β + 3*α*β^2 + β^3 := by rw [hs_def]; ring
    have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
    have hα2β : 0 ≤ α^2 * β := mul_nonneg (sq_nonneg _) hβ_nn
    have hαβ2 : 0 ≤ α * β^2 := mul_nonneg hα_nn (sq_nonneg _)
    nlinarith [pow_nonneg hα_nn 3, pow_nonneg hβ_nn 3]
  -- H1 identity (mirror quintic proof's hH1).
  have hH1 : y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 =
      (2 : 𝕂)⁻¹ • W_H1 := by
    suffices h : (2 : 𝕂) • (y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2) = (2 : 𝕂) • ((2 : 𝕂)⁻¹ • W_H1) by
      have hinj : Function.Injective ((2 : 𝕂) • · : 𝔸 → 𝔸) := by
        intro x₀ y₀ hxy; have := congrArg ((2 : 𝕂)⁻¹ • ·) hxy
        simp only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] at this; exact this
      exact hinj h
    rw [smul_smul, mul_inv_cancel₀ h2ne, one_smul]
    simp only [hE₁_def, hE₂_def, hD₁_def, hD₂_def, hP_def, hy_def, hW_H1_def, hz_def,
      smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h2ne, one_smul, two_smul]
    noncomm_ring
  -- Decomposition.
  have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b - bch_quintic_term 𝕂 a b =
      (logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
        (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5) +
      (y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
        (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
        bch_quintic_term 𝕂 a b) := by
    unfold bch; rw [hz_def]; abel
  rw [hdecomp]
  -- Bound pieceA.
  have hpieceA : ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
      (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5‖ ≤
      (Real.exp s - 1) ^ 6 / (2 - Real.exp s) :=
    calc _ ≤ ‖y‖ ^ 6 / (1 - ‖y‖) :=
          norm_logOnePlus_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) y hy_lt
      _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
          (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
  have hexp6 : (Real.exp s - 1) ^ 6 ≤ 2 * s ^ 6 := by
    have hE1_nn : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
    calc (Real.exp s - 1) ^ 6 ≤ (s + s ^ 2) ^ 6 :=
          pow_le_pow_left₀ hE1_nn (by linarith) 6
      _ = s ^ 6 * (1 + s) ^ 6 := by ring
      _ ≤ s ^ 6 * 2 := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs_nn 6)
          have h1 : (1 + s) ^ 6 ≤ (1 + 1/10) ^ 6 :=
            pow_le_pow_left₀ (by linarith) (by linarith) 6
          have h2 : (1 + 1/10 : ℝ) ^ 6 ≤ 2 := by norm_num
          linarith
      _ = 2 * s ^ 6 := by ring
  -- Define I₁ in the H1 form and apply quartic_identity.
  set I₁ := (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 -
      bch_cubic_term 𝕂 a b with hI₁_def
  have hI₁_quartic : I₁ =
      F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
      (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
      (2 : 𝕂)⁻¹ • P ^ 2 := by
    rw [hI₁_def]; exact quartic_identity 𝕂 (exp a) (exp b) a b
  -- Set R for I1_residual_decomp_eq's RHS.
  set R := T₃ - E₁ - E₂ - Q + T₄ with hR_def
  set T22_resid := T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂ with hT22_def
  -- I1_residual_decomp_eq applied: I₁ - corr₁_T3SPI - ½W5 = I1_RHS.
  have hI1_decomp_full :
      (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
        (2 : 𝕂)⁻¹ • P ^ 2) -
        ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
          (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
          (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
          (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
        (2 : 𝕂)⁻¹ • W5 =
      H₁ + H₂ + a * G₂ + G₁ * b +
      (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
      (2 : 𝕂)⁻¹ • (z * R + R * z) +
      (2 : 𝕂)⁻¹ • T22_resid := by
    have h := I1_residual_decomp_eq 𝕂 (exp a) (exp b) a b
    simp only [hH₁_def, hH₂_def, hG₁_def, hG₂_def, hF₁_def, hF₂_def,
      hE₁_def, hE₂_def, hD₁_def, hD₂_def, hQ_def, hR_def, hT22_def,
      hP_def, hy_def, hz_def, hT₂_def, hT₃_def, hT₄_def, hW5_def] at h
    convert h using 1
  -- Compute per-component norm bounds for the I1_residual_decomp_eq RHS.
  have hH₁_s6 : ‖H₁‖ ≤ s ^ 6 :=
    le_trans hH₁_le (le_trans hHa6 (pow_le_pow_left₀ hα_nn hα_le 6))
  have hH₂_s6 : ‖H₂‖ ≤ s ^ 6 :=
    le_trans hH₂_le (le_trans hHb6 (pow_le_pow_left₀ hβ_nn hβ_le 6))
  have h_aG₂_s6 : ‖a * G₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖a‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 5 := mul_le_mul_of_nonneg_left
          (le_trans hG₂_le hGb5) hα_nn
      _ ≤ s * s ^ 5 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 5)
          (by positivity) hs_nn
      _ = s ^ 6 := by ring
  have h_G₁b_s6 : ‖G₁ * b‖ ≤ s ^ 6 :=
    calc _ ≤ ‖G₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β := mul_le_mul (le_trans hG₁_le hGa5) le_rfl hβ_nn
          (by positivity)
      _ ≤ s ^ 5 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5) hβ_le
          (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_E₁E₂_s6 : ‖E₁ * E₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖E₁‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 3 := mul_le_mul (le_trans hE₁_le hEa3)
          (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_a2F₂_s6 : ‖a ^ 2 * F₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖a ^ 2‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 4 := mul_le_mul (norm_pow_le _ _)
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_F₁b2_s6 : ‖F₁ * b ^ 2‖ ≤ s ^ 6 :=
    calc _ ≤ ‖F₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 2 := mul_le_mul (le_trans hF₁_le hFa4)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  -- ‖R‖ ≤ 6·s⁵ via R_eq_neg_deg5_residual + norm_R_residual_sum_le.
  have hR_neg : R = -(G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂)) := by
    have h := R_eq_neg_deg5_residual 𝕂 (exp a) (exp b) a b
    simp only [hR_def, hG₁_def, hG₂_def, hF₁_def, hF₂_def, hE₁_def, hE₂_def,
      hD₁_def, hD₂_def, hQ_def, hT₃_def, hT₄_def] at h
    convert h using 1
  have h_aF₂_s5 : ‖a * F₂‖ ≤ s ^ 5 :=
    calc _ ≤ ‖a‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 4 := mul_le_mul_of_nonneg_left (le_trans hF₂_le hFb4) hα_nn
      _ ≤ s * s ^ 4 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 4)
          (by positivity) hs_nn
      _ = s ^ 5 := by ring
  have h_F₁b_s5 : ‖F₁ * b‖ ≤ s ^ 5 :=
    calc _ ≤ ‖F₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β := mul_le_mul (le_trans hF₁_le hFa4) le_rfl hβ_nn (by positivity)
      _ ≤ s ^ 4 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4) hβ_le
          (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have h_G₁_s5 : ‖G₁‖ ≤ s ^ 5 :=
    le_trans hG₁_le (le_trans hGa5 (pow_le_pow_left₀ hα_nn hα_le 5))
  have h_G₂_s5 : ‖G₂‖ ≤ s ^ 5 :=
    le_trans hG₂_le (le_trans hGb5 (pow_le_pow_left₀ hβ_nn hβ_le 5))
  have h_E₁b2_s5 : ‖E₁ * b ^ 2‖ ≤ s ^ 5 :=
    calc _ ≤ ‖E₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 2 := mul_le_mul (le_trans hE₁_le hEa3)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have h_a2E₂_s5 : ‖a ^ 2 * E₂‖ ≤ s ^ 5 :=
    calc _ ≤ ‖a ^ 2‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 3 := mul_le_mul (norm_pow_le _ _)
          (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have hR_le : ‖R‖ ≤ 6 * s ^ 5 := by
    rw [hR_neg, norm_neg]
    exact norm_R_residual_sum_le G₁ G₂ F₁ F₂ E₁ E₂ a b hs_nn hs_small_le
      h_G₁_s5 h_G₂_s5 h_aF₂_s5 h_F₁b_s5 h_E₁E₂_s6 h_E₁b2_s5 h_a2E₂_s5
  have h_zRpRz_le : ‖z * R + R * z‖ ≤ 12 * s ^ 6 := by
    have h1 : ‖z * R‖ ≤ s * (6 * s ^ 5) :=
      (norm_mul_le _ _).trans (mul_le_mul hz_le hR_le (norm_nonneg _) hs_nn)
    have h2 : ‖R * z‖ ≤ (6 * s ^ 5) * s :=
      (norm_mul_le _ _).trans (mul_le_mul hR_le hz_le (norm_nonneg _) (by positivity))
    have htri := norm_add_le (z * R) (R * z)
    nlinarith [pow_nonneg hs_nn 6]
  have h_T22_le : ‖T22_resid‖ ≤ 15 * s ^ 6 := by
    rw [hT22_def]
    exact norm_T22_sub_P2_etc_le P T₂ T₃ hs_nn hP_le_s2 hT₂_le hT₃_le hPmT₂ hPmT₂mT₃
  -- I1_RHS bound: ‖I1_RHS‖ ≤ 20·s⁶.
  have hI1_RHS_le :
      ‖H₁ + H₂ + a * G₂ + G₁ * b +
        (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
        (2 : 𝕂)⁻¹ • (z * R + R * z) +
        (2 : 𝕂)⁻¹ • T22_resid‖ ≤ 20 * s ^ 6 :=
    norm_I1_residual_RHS_le a b z H₁ H₂ G₁ G₂ F₁ F₂ E₁ E₂ R T22_resid hs_nn
      hH₁_s6 hH₂_s6 h_aG₂_s6 h_G₁b_s6 h_E₁E₂_s6 h_a2F₂_s6 h_F₁b2_s6
      h_zRpRz_le h_T22_le
  -- Bound ‖I₁ - corr₁_T3SPI - ½W5‖ ≤ 20·s⁶.
  have hI1_minus_corr_le :
      ‖I₁ - ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
        (2 : 𝕂)⁻¹ • W5‖ ≤ 20 * s ^ 6 := by
    rw [hI₁_quartic, hI1_decomp_full]
    exact hI1_RHS_le
  -- Now bound pieceB''.
  have hpieceB : ‖y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
      (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b‖ ≤ 52 * s ^ 6 := by
    -- Apply pieceB_sextic_decomp.
    rw [pieceB_sextic_decomp 𝕂 a b]
    -- Goal: ‖S₁_pieceB + S₂_pieceB - S₃_pieceB + S₄_pieceB‖ ≤ 52·s⁶
    -- For S₁, convert from pieceB_sextic_decomp form (T₃_QPI in corr₁) to my form (T₃_SPI).
    -- pieceB_sextic_decomp's S₁ = (y - z - ½(ab-ba) - ½y² + ⅓z³ - C₃) - corr₁_QPI - ½W5.
    -- I have: I₁ = ½W_H1 + ⅓z³ - C₃ = (y - z - ½(ab-ba) - ½y² + ⅓z³ - C₃) by hH1.
    -- And T₃_QPI = T₃_SPI by abel (in corr₁).
    have hI₁_eq_form :
        (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b =
        y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
          (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b := by
      rw [← hH1]
    have hT3_QPI_eq_SPI :
        (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b) =
        (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 := by abel
    have hS1_le :
        ‖(y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
            (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b) -
          ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
            (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
            (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
            (2 : 𝕂)⁻¹ • (z * ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
                (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) +
              ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
                (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) * z) -
            (2 : 𝕂)⁻¹ • T₂ ^ 2) -
          (2 : 𝕂)⁻¹ • W5‖ ≤ 20 * s ^ 6 := by
      -- Convert T₃_QPI to T₃_SPI in corr₁.
      rw [hT3_QPI_eq_SPI]
      -- Convert (y - z - ½(ab-ba) - ½y² + ⅓z³ - C₃) to I₁ via H1.
      rw [← hI₁_eq_form]
      exact hI1_minus_corr_le
    -- S₂ = ⅓•(y³-z³) - ⅓•(z²T₂+zT₂z+T₂z²) - ⅓•y3_5.
    -- Bound: ‖S₂‖ ≤ 17·s⁶ via I2_residual_decomp_eq + ⅓ scaling.
    have hyzP : y = z + P := by rw [hP_def]; abel
    have hS2_inner_eq : y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
        (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
          z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) =
        z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
        (P - T₂ - T₃) * z ^ 2 + z * (P ^ 2 - T₂ ^ 2) +
        (P * z * P - T₂ * z * T₂) + (P ^ 2 - T₂ ^ 2) * z + P ^ 3 := by
      rw [hyzP]; exact I2_residual_decomp_eq z P T₂ T₃
    have hS2_inner_le :
        ‖z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z + (P - T₂ - T₃) * z ^ 2 +
          z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) + (P ^ 2 - T₂ ^ 2) * z +
          P ^ 3‖ ≤ 50 * s ^ 6 :=
      norm_I2_residual_inner_le z P T₂ T₃ hs_nn hs_small_le hz_le hP_le_s2 hT₂_le
        hPmT₂ hPmT₂mT₃
    have hS2_inner_full : ‖y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
        (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
          z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z)‖ ≤ 50 * s ^ 6 := by
      rw [hS2_inner_eq]; exact hS2_inner_le
    have hS2_smul_eq :
        (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
          z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) =
        (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z)) := by
      simp only [smul_sub]
    have hS2_le :
        ‖(3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z)‖ ≤ 17 * s ^ 6 := by
      rw [hS2_smul_eq]
      calc _ ≤ ‖(3 : 𝕂)⁻¹‖ * ‖y ^ 3 - z ^ 3 -
                (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
                (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
                  z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z)‖ := norm_smul_le _ _
        _ ≤ (3 : ℝ)⁻¹ * (50 * s ^ 6) := by
            rw [h3eq]; exact mul_le_mul_of_nonneg_left hS2_inner_full (by norm_num)
        _ ≤ 17 * s ^ 6 := by nlinarith [pow_nonneg hs_nn 6]
    -- S₃ = ¼•(y⁴-z⁴-y4_5).
    have hzeq : z = y - P := by rw [hP_def]; abel
    have hS3_inner_le : ‖y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)‖ ≤ 31 * s ^ 6 := by
      have h := norm_y4_sub_z4_sub_y4_5_le y P T₂ hs_nn hy_le2
        (by rw [← hzeq]; exact hz_le) hP_le_s2 hPmT₂
      rwa [show y - P = z from hzeq.symm] at h
    have hS3_le : ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3))‖ ≤
        8 * s ^ 6 := by
      calc _ ≤ ‖(4 : 𝕂)⁻¹‖ * ‖y ^ 4 - z ^ 4 -
                (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)‖ :=
            norm_smul_le _ _
        _ ≤ (4 : ℝ)⁻¹ * (31 * s ^ 6) := by
            rw [h4eq]; exact mul_le_mul_of_nonneg_left hS3_inner_le (by norm_num)
        _ ≤ 8 * s ^ 6 := by nlinarith [pow_nonneg hs_nn 6]
    -- S₄ = ⅕•(y⁵-z⁵).
    have hS4_inner_le : ‖y ^ 5 - z ^ 5‖ ≤ 31 * s ^ 6 := by
      have h := norm_pow5_sub_zpow5_le y P hs_nn hy_le2
        (by rw [← hzeq]; exact hz_le) hP_le_s2
      rwa [show y - P = z from hzeq.symm] at h
    have hS4_le : ‖(5 : 𝕂)⁻¹ • (y ^ 5 - z ^ 5)‖ ≤ 7 * s ^ 6 := by
      calc _ ≤ ‖(5 : 𝕂)⁻¹‖ * ‖y ^ 5 - z ^ 5‖ := norm_smul_le _ _
        _ ≤ (5 : ℝ)⁻¹ * (31 * s ^ 6) := by
            rw [h5eq]; exact mul_le_mul_of_nonneg_left hS4_inner_le (by norm_num)
        _ ≤ 7 * s ^ 6 := by nlinarith [pow_nonneg hs_nn 6]
    -- Triangle inequality on the 4-piece sum.
    -- Goal: ‖S₁ + S₂ - S₃ + S₄‖ ≤ 52*s^6
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans ?_
    calc _ ≤ 20 * s ^ 6 + 17 * s ^ 6 + 8 * s ^ 6 + 7 * s ^ 6 :=
        add_le_add (add_le_add (add_le_add hS1_le hS2_le) hS3_le) hS4_le
      _ = 52 * s ^ 6 := by ring
  -- COMBINE pieceA + pieceB''.
  calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
          (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5‖ +
        ‖y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
          (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
          bch_quintic_term 𝕂 a b‖ := norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 6 / (2 - Real.exp s) + 52 * s ^ 6 := by
        linarith [hpieceA, hpieceB]
    _ ≤ (Real.exp s - 1) ^ 6 / (2 - Real.exp s) +
        52 * s ^ 6 / (2 - Real.exp s) := by
        gcongr
        rw [le_div_iff₀ hdenom]
        nlinarith [pow_nonneg hs_nn 6]
    _ = ((Real.exp s - 1) ^ 6 + 52 * s ^ 6) / (2 - Real.exp s) :=
        (add_div _ _ _).symm
    _ ≤ 100 * s ^ 6 / (2 - Real.exp s) := by
        apply div_le_div_of_nonneg_right _ hdenom.le
        linarith [hexp6, pow_nonneg hs_nn 6]

include 𝕂 in
/-- **Sixth-order BCH remainder bound** (public theorem, Tier-1 of B1.c).

Extends `norm_bch_quintic_remainder_le` by one degree:

  `‖bch a b - (a+b) - ½[a,b] - C₃ - C₄ - C₅‖ ≤ 100000·s⁶/(2-exp(s))`

for `s = ‖a‖+‖b‖ < log 2`, where `C_k = bch_*_term 𝕂 a b` denotes the
degree-k commutator coefficient.

Proof: case split on `s ≥ 1/10` (uses `norm_bch_sextic_remainder_large_s_le`,
fully proved) vs. `s < 1/10` (uses `norm_bch_sextic_remainder_small_s_le`,
currently a scoped axiom — see its docstring).

This theorem is the Tier-1 piece needed to discharge the B1.c axiom
(`symmetric_bch_quintic_sub_poly_axiom`). Per the strategy, after Tier 1
we extend the cubic template `norm_symmetric_bch_cubic_sub_poly_le` (line
~3798) to give the quintic version, replacing the B1.c axiom. -/
theorem norm_bch_sextic_remainder_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b‖ ≤
      100000 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  by_cases hs : 1 / 10 ≤ ‖a‖ + ‖b‖
  · -- Large-s: ‖LHS‖ ≤ 100000·s⁶/(2-exp(s)) directly.
    exact norm_bch_sextic_remainder_large_s_le (𝕂 := 𝕂) a b hab hs
  · -- Small-s: ‖LHS‖ ≤ 100·s⁶/(2-exp(s)) ≤ 100000·s⁶/(2-exp(s)).
    push_neg at hs
    have h_small := norm_bch_sextic_remainder_small_s_le (𝕂 := 𝕂) a b hab hs
    have hexp_lt : Real.exp (‖a‖ + ‖b‖) < 2 := by
      calc Real.exp (‖a‖ + ‖b‖) < Real.exp (Real.log 2) := Real.exp_strictMono hab
        _ = 2 := Real.exp_log (by norm_num)
    have hdenom : 0 < 2 - Real.exp (‖a‖ + ‖b‖) := by linarith
    have hs_nn : 0 ≤ ‖a‖ + ‖b‖ := by positivity
    calc _ ≤ 100 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := h_small
      _ ≤ 100000 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
          apply div_le_div_of_nonneg_right _ hdenom.le
          have : 100 * (‖a‖ + ‖b‖) ^ 6 ≤ 100000 * (‖a‖ + ‖b‖) ^ 6 := by
            nlinarith [pow_nonneg hs_nn 6]
          linarith

include 𝕂 in
set_option maxHeartbeats 32000000 in
/-- **Order-7 BCH remainder small-s bound** (private theorem, T2-F7e step 22).

For `‖a‖+‖b‖ < 1/10`,

  `‖bch(a, b) - through-deg-6 expansion‖ ≤ 1000 · s⁷ / (2 - exp(s))`

Proof mirrors `norm_bch_sextic_remainder_small_s_le` at one degree higher, using
`septic_pure_identity` (the deg-6 cancellation), `pieceB_septic_decomp` (the
central decomposition), `norm_combined_tricky_le` (28·s⁷ for I₁'s "tricky"
cluster), `norm_I1_septic_residual_RHS_le` (21·s⁷ for I₁), and
`norm_I2_septic_residual_RHS_le` (76·s⁷ for I₂'s inner). Total pieceB''' ≤ 91·s⁷.
Combined with pieceA ≤ 2·s⁷/(2-exp(s)) gives ≤ 93·s⁷/(2-exp(s)) ≤ 1000·s⁷/(2-exp(s)). -/
private theorem norm_bch_septic_remainder_small_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b‖ ≤
      1000 * (‖a‖ + ‖b‖) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  -- SETUP.
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖
  set β := ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hs_small_le : s ≤ 1 / 10 := hs_small.le
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hs1 : s < 1 := by linarith
  have hs34 : s < 3 / 4 := by linarith
  have hs56 : s < 5 / 6 := by linarith
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  set y := exp a * exp b - 1 with hy_def
  set z := a + b with hz_def
  set P := y - z with hP_def
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have hy_eq : y = (exp a - 1) * exp b + (exp b - 1) := by
      rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [hy_eq]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          apply add_le_add
          · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
              (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn,
         Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  have hy_le2 : ‖y‖ ≤ 2 * s := by
    calc ‖y‖ ≤ Real.exp s - 1 := hy_le
      _ ≤ s + s ^ 2 := by linarith
      _ ≤ 2 * s := by nlinarith [sq_nonneg s]
  have hz_le : ‖z‖ ≤ s := by rw [hz_def]; exact norm_add_le _ _
  -- Exp remainders D, E, F, G, H, I.
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set G₁ := F₁ - (24 : 𝕂)⁻¹ • a ^ 4 with hG₁_def
  set G₂ := F₂ - (24 : 𝕂)⁻¹ • b ^ 4 with hG₂_def
  set H₁ := G₁ - (120 : 𝕂)⁻¹ • a ^ 5 with hH₁_def
  set H₂ := G₂ - (120 : 𝕂)⁻¹ • b ^ 5 with hH₂_def
  set I_a := H₁ - (720 : 𝕂)⁻¹ • a ^ 6 with hI_a_def
  set I_b := H₂ - (720 : 𝕂)⁻¹ • b ^ 6 with hI_b_def
  set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
  set W_H1 := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
      z * P - P * z - P ^ 2 with hW_H1_def
  set T₂ := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2 with hT₂_def
  set T₃ := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
      (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 with hT₃_def
  set T₄ := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
      (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
      (24 : 𝕂)⁻¹ • b ^ 4 with hT₄_def
  set T₅ := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
      (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
      (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5 with hT₅_def
  set W5 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
      (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
      (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
      (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂) with hW5_def
  set W6 := (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
      (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
      (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
      (360 : 𝕂)⁻¹ • b ^ 6 -
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) with hW6_def
  -- Norm bounds for D, E, F, G, H, I.
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖α‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hα_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDa_nn,
         Real.norm_eq_abs, abs_of_nonneg hα_nn] at h
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖β‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hβ_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDb_nn,
         Real.norm_eq_abs, abs_of_nonneg hβ_nn] at h
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hG₁_le : ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hG₂_le : ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hGa5 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 ≤ α ^ 5 :=
    real_exp_fifth_order_le_quintic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hGb5 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 ≤ β ^ 5 :=
    real_exp_fifth_order_le_quintic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hH₁_le : ‖H₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hH₂_le : ‖H₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hHa6 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 ≤
      α ^ 6 :=
    real_exp_sixth_order_le_sextic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hHb6 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 ≤
      β ^ 6 :=
    real_exp_sixth_order_le_sextic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hI_a_le : ‖I_a‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hI_b_le : ‖I_b‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hIa7 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 -
      α ^ 6 / 720 ≤ α ^ 7 :=
    real_exp_seventh_order_le_septic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hIb7 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 -
      β ^ 6 / 720 ≤ β ^ 7 :=
    real_exp_seventh_order_le_septic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- ‖P‖ ≤ s² and friends.
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
    have hP_split : P = a * (exp b - 1) + D₁ * exp b + D₂ := by
      simp only [hP_def, hy_def, hz_def, hD₁_def, hD₂_def]; noncomm_ring
    calc ‖P‖ = ‖a * (exp b - 1) + D₁ * exp b + D₂‖ := by rw [hP_split]
      _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
          calc _ ≤ ‖a * (exp b - 1) + D₁ * exp b‖ + ‖D₂‖ := norm_add_le _ _
            _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
                gcongr; exact norm_add_le _ _
      _ ≤ α * (Real.exp β - 1) + (Real.exp α - 1 - α) * Real.exp β +
          (Real.exp β - 1 - β) := by
          have h1 : ‖a * (exp b - 1)‖ ≤ α * (Real.exp β - 1) :=
            calc _ ≤ ‖a‖ * ‖exp b - 1‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_exp_sub_one_le (𝕂 := 𝕂) b
          have h2 : ‖D₁ * exp b‖ ≤ (Real.exp α - 1 - α) * Real.exp β :=
            calc _ ≤ ‖D₁‖ * ‖exp b‖ := norm_mul_le _ _
              _ ≤ _ := mul_le_mul hD₁_le (norm_exp_le (𝕂 := 𝕂) b)
                  (norm_nonneg _) (by linarith)
          linarith [hD₂_le]
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  have hP_le_s2 : ‖P‖ ≤ s ^ 2 := le_trans hP_le hEs2
  have hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3 := by
    have hS_eq : P - T₂ = E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂ := by
      simp only [hP_def, hy_def, hT₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hz_def]
      noncomm_ring
    rw [hS_eq]
    have hE₁_s3 : ‖E₁‖ ≤ α ^ 3 := le_trans hE₁_le hEa3
    have hE₂_s3 : ‖E₂‖ ≤ β ^ 3 := le_trans hE₂_le hEb3
    have haD₂ : ‖a * D₂‖ ≤ α * β ^ 2 :=
      calc _ ≤ ‖a‖ * ‖D₂‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans hD₂_le hDb2) hα_nn
    have hD₁b : ‖D₁ * b‖ ≤ α ^ 2 * β :=
      calc _ ≤ ‖D₁‖ * ‖b‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) le_rfl hβ_nn (by positivity)
    have hDD : ‖D₁ * D₂‖ ≤ α ^ 2 * β ^ 2 :=
      calc _ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
            (norm_nonneg _) (by positivity)
    calc ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖
        ≤ ‖E₁‖ + ‖E₂‖ + ‖a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖ := by
          have := norm_add_le E₁ E₂
          have := norm_add_le (E₁ + E₂) (a * D₂)
          have := norm_add_le (E₁ + E₂ + a * D₂) (D₁ * b)
          have := norm_add_le (E₁ + E₂ + a * D₂ + D₁ * b) (D₁ * D₂)
          linarith
      _ ≤ α ^ 3 + β ^ 3 + α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 := by
          linarith [hE₁_s3, hE₂_s3, haD₂, hD₁b, hDD]
      _ ≤ 5 * s ^ 3 := by
          nlinarith [pow_le_pow_left₀ hα_nn hα_le 3, pow_le_pow_left₀ hβ_nn hβ_le 3,
            pow_le_pow_left₀ hα_nn hα_le 2, pow_le_pow_left₀ hβ_nn hβ_le 2,
            pow_nonneg hs_nn 4]
  have hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4 := by
    have h := norm_P_sub_T2_sub_T3_le (𝕂 := 𝕂) a b hs_nn hs34 hα_le hβ_le
    have hP_unfold : P = exp a * exp b - 1 - (a + b) := by
      rw [hP_def, hy_def, hz_def]
    rw [hP_unfold, hT₂_def, hT₃_def]
    exact h
  have hPmT₂mT₃mT₄ : ‖P - T₂ - T₃ - T₄‖ ≤ 6 * s ^ 5 := by
    have h := norm_P_sub_T2_sub_T3_sub_T4_le (𝕂 := 𝕂) a b hs_nn hs34 hα_le hβ_le
    have hP_unfold : P = exp a * exp b - 1 - (a + b) := by
      rw [hP_def, hy_def, hz_def]
    rw [hP_unfold, hT₂_def, hT₃_def, hT₄_def]
    exact h
  have h2_le : ‖(2 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h3eq : ‖(3 : 𝕂)⁻¹‖ = (3 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h4eq : ‖(4 : 𝕂)⁻¹‖ = (4 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h5eq : ‖(5 : 𝕂)⁻¹‖ = (5 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hT₂_le : ‖T₂‖ ≤ s ^ 2 := by
    have h1 : ‖a * b‖ ≤ α * β := norm_mul_le _ _
    have h2 : ‖(2:𝕂)⁻¹ • a^2‖ ≤ α^2 :=
      calc _ ≤ 1 * ‖a‖ ^ 2 := (norm_smul_le _ _).trans
              (mul_le_mul h2_le (norm_pow_le a 2) (norm_nonneg _) (by norm_num))
        _ = α^2 := one_mul _
    have h3 : ‖(2:𝕂)⁻¹ • b^2‖ ≤ β^2 :=
      calc _ ≤ 1 * ‖b‖ ^ 2 := (norm_smul_le _ _).trans
              (mul_le_mul h2_le (norm_pow_le b 2) (norm_nonneg _) (by norm_num))
        _ = β^2 := one_mul _
    have htriangle : ‖T₂‖ ≤ ‖a * b‖ + ‖(2:𝕂)⁻¹ • a^2‖ + ‖(2:𝕂)⁻¹ • b^2‖ := by
      rw [hT₂_def]
      have n1 := norm_add_le (a * b + (2:𝕂)⁻¹ • a^2) ((2:𝕂)⁻¹ • b^2)
      have n2 := norm_add_le (a * b) ((2:𝕂)⁻¹ • a^2)
      linarith
    have hs2 : s^2 = α^2 + 2*α*β + β^2 := by rw [hs_def]; ring
    have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
    linarith
  have hT₃_le : ‖T₃‖ ≤ s ^ 3 := by
    have hT1 : ‖(6:𝕂)⁻¹ • a^3‖ ≤ α^3 / 6 := by
      calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖a^3‖ := norm_smul_le _ _
        _ ≤ (6:ℝ)⁻¹ * α^3 := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
        _ = α^3 / 6 := by ring
    have hT2_norm : ‖(2:𝕂)⁻¹ • (a^2*b)‖ ≤ α^2 * β / 2 := by
      have hab_le : ‖a^2*b‖ ≤ α^2 * β :=
        calc _ ≤ ‖a^2‖ * ‖b‖ := norm_mul_le _ _
          _ ≤ α^2 * β := mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn (by positivity)
      calc _ ≤ ‖(2:𝕂)⁻¹‖ * ‖a^2*b‖ := norm_smul_le _ _
        _ ≤ (2:ℝ)⁻¹ * (α^2 * β) := by
            rw [h2eq]; exact mul_le_mul_of_nonneg_left hab_le (by norm_num)
        _ = α^2 * β / 2 := by ring
    have hT3 : ‖(2:𝕂)⁻¹ • (a*b^2)‖ ≤ α * β^2 / 2 := by
      have hab_le : ‖a*b^2‖ ≤ α * β^2 :=
        calc _ ≤ ‖a‖ * ‖b^2‖ := norm_mul_le _ _
          _ ≤ α * β^2 := mul_le_mul le_rfl (norm_pow_le _ _) (by positivity) hα_nn
      calc _ ≤ ‖(2:𝕂)⁻¹‖ * ‖a*b^2‖ := norm_smul_le _ _
        _ ≤ (2:ℝ)⁻¹ * (α * β^2) := by
            rw [h2eq]; exact mul_le_mul_of_nonneg_left hab_le (by norm_num)
        _ = α * β^2 / 2 := by ring
    have hT4_norm : ‖(6:𝕂)⁻¹ • b^3‖ ≤ β^3 / 6 := by
      calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖b^3‖ := norm_smul_le _ _
        _ ≤ (6:ℝ)⁻¹ * β^3 := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
        _ = β^3 / 6 := by ring
    have htriangle : ‖T₃‖ ≤ ‖(6:𝕂)⁻¹ • a^3‖ + ‖(2:𝕂)⁻¹ • (a^2*b)‖ +
        ‖(2:𝕂)⁻¹ • (a*b^2)‖ + ‖(6:𝕂)⁻¹ • b^3‖ := by
      rw [hT₃_def]
      have n1 := norm_add_le ((6:𝕂)⁻¹ • a^3 + (2:𝕂)⁻¹ • (a^2*b) +
        (2:𝕂)⁻¹ • (a*b^2)) ((6:𝕂)⁻¹ • b^3)
      have n2 := norm_add_le ((6:𝕂)⁻¹ • a^3 + (2:𝕂)⁻¹ • (a^2*b)) ((2:𝕂)⁻¹ • (a*b^2))
      have n3 := norm_add_le ((6:𝕂)⁻¹ • a^3) ((2:𝕂)⁻¹ • (a^2*b))
      linarith
    have hs3 : s^3 = α^3 + 3*α^2*β + 3*α*β^2 + β^3 := by rw [hs_def]; ring
    have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
    have hα2β : 0 ≤ α^2 * β := mul_nonneg (sq_nonneg _) hβ_nn
    have hαβ2 : 0 ≤ α * β^2 := mul_nonneg hα_nn (sq_nonneg _)
    nlinarith [pow_nonneg hα_nn 3, pow_nonneg hβ_nn 3]
  have hT₄_le : ‖T₄‖ ≤ s ^ 4 := by
    rw [hT₄_def]; exact norm_T4_le (𝕂 := 𝕂) a b hs_nn hα_le hβ_le
  have hT₅_le : ‖T₅‖ ≤ s ^ 5 := by
    rw [hT₅_def]; exact norm_T5_le (𝕂 := 𝕂) a b hs_nn hα_le hβ_le
  -- H1 identity (mirror sextic).
  have hH1 : y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 =
      (2 : 𝕂)⁻¹ • W_H1 := by
    suffices h : (2 : 𝕂) • (y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2) = (2 : 𝕂) • ((2 : 𝕂)⁻¹ • W_H1) by
      have hinj : Function.Injective ((2 : 𝕂) • · : 𝔸 → 𝔸) := by
        intro x₀ y₀ hxy; have := congrArg ((2 : 𝕂)⁻¹ • ·) hxy
        simp only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] at this; exact this
      exact hinj h
    rw [smul_smul, mul_inv_cancel₀ h2ne, one_smul]
    simp only [hE₁_def, hE₂_def, hD₁_def, hD₂_def, hP_def, hy_def, hW_H1_def, hz_def,
      smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h2ne, one_smul, two_smul]
    noncomm_ring
  -- Decomposition: LHS = pieceA + pieceB'''.
  have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b - bch_quintic_term 𝕂 a b -
      bch_sextic_term 𝕂 a b =
      (logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
        (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 + (6 : 𝕂)⁻¹ • y ^ 6) +
      (y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
        (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
        (6 : 𝕂)⁻¹ • y ^ 6 -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
        bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b) := by
    unfold bch; rw [hz_def]; abel
  rw [hdecomp]
  -- Bound pieceA.
  have hpieceA : ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
      (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 +
      (6 : 𝕂)⁻¹ • y ^ 6‖ ≤
      (Real.exp s - 1) ^ 7 / (2 - Real.exp s) :=
    calc _ ≤ ‖y‖ ^ 7 / (1 - ‖y‖) :=
          norm_logOnePlus_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) y hy_lt
      _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
          (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
  have hexp7 : (Real.exp s - 1) ^ 7 ≤ 2 * s ^ 7 :=
    real_exp_sub_one_pow7_le_small hs_nn hs_small_le
  -- Define I₁ via H1+quartic_identity, and the cluster vars R, T22, T_extra.
  set I₁ := (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 -
      bch_cubic_term 𝕂 a b with hI₁_def
  have hI₁_quartic : I₁ =
      F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
      (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
      (2 : 𝕂)⁻¹ • P ^ 2 := by
    rw [hI₁_def]; exact quartic_identity 𝕂 (exp a) (exp b) a b
  set R := T₃ - E₁ - E₂ - Q + T₄ with hR_def
  set T22_resid := T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂ with hT22_def
  set T_extra := z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z with hT_extra_def
  -- Apply I1_septic_residual_decomp_eq.
  have hI1_decomp_full :
      (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
        (2 : 𝕂)⁻¹ • P ^ 2) -
        ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
          (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
          (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
          (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
        (2 : 𝕂)⁻¹ • W5 -
        (2 : 𝕂)⁻¹ • W6 =
      I_a + I_b + a * H₂ + H₁ * b +
      ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
      (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) + (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) +
      (2 : 𝕂)⁻¹ • (z * R + R * z) +
      (2 : 𝕂)⁻¹ • T22_resid +
      (2 : 𝕂)⁻¹ • T_extra := by
    have h := I1_septic_residual_decomp_eq 𝕂 (exp a) (exp b) a b
    simp only [hI_a_def, hI_b_def, hH₁_def, hH₂_def, hG₁_def, hG₂_def,
      hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hQ_def, hR_def,
      hT22_def, hT_extra_def, hP_def, hy_def, hz_def, hT₂_def, hT₃_def,
      hT₄_def, hT₅_def, hW5_def, hW6_def] at h
    convert h using 1
  -- Per-component norm bounds at deg-7.
  have hI_a_s7 : ‖I_a‖ ≤ s ^ 7 :=
    le_trans hI_a_le (le_trans hIa7 (pow_le_pow_left₀ hα_nn hα_le 7))
  have hI_b_s7 : ‖I_b‖ ≤ s ^ 7 :=
    le_trans hI_b_le (le_trans hIb7 (pow_le_pow_left₀ hβ_nn hβ_le 7))
  have h_aH₂_s7 : ‖a * H₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a‖ * ‖H₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 6 := mul_le_mul_of_nonneg_left
          (le_trans hH₂_le hHb6) hα_nn
      _ ≤ s * s ^ 6 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 6)
          (by positivity) hs_nn
      _ = s ^ 7 := by ring
  have h_H₁b_s7 : ‖H₁ * b‖ ≤ s ^ 7 :=
    calc _ ≤ ‖H₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 6 * β := mul_le_mul (le_trans hH₁_le hHa6) le_rfl hβ_nn
          (by positivity)
      _ ≤ s ^ 6 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 6) hβ_le
          (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_a3F₂_s7 : ‖a ^ 3 * F₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a ^ 3‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 4 := mul_le_mul (norm_pow_le _ _)
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_F₁b3_s7 : ‖F₁ * b ^ 3‖ ≤ s ^ 7 :=
    calc _ ≤ ‖F₁‖ * ‖b ^ 3‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 3 := mul_le_mul (le_trans hF₁_le hFa4)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_F₁F₂_s7 : ‖F₁ * F₂‖ ≤ s ^ 7 := by
    have h_step : ‖F₁ * F₂‖ ≤ s ^ 8 :=
      calc ‖F₁ * F₂‖ ≤ ‖F₁‖ * ‖F₂‖ := norm_mul_le _ _
        _ ≤ α ^ 4 * β ^ 4 := mul_le_mul (le_trans hF₁_le hFa4)
            (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
        _ ≤ s ^ 4 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
            (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
        _ = s ^ 8 := by ring
    have h_s8_le_s7 : s ^ 8 ≤ s ^ 7 := by
      have h_eq : s ^ 8 = s ^ 7 * s := by ring
      rw [h_eq]
      have hs_le1 : s ≤ 1 := by linarith
      nlinarith [pow_nonneg hs_nn 7]
    linarith
  have h_a2G₂_s7 : ‖a ^ 2 * G₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a ^ 2‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 5 := mul_le_mul (norm_pow_le _ _)
          (le_trans hG₂_le hGb5) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 5 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 5) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_G₁b2_s7 : ‖G₁ * b ^ 2‖ ≤ s ^ 7 :=
    calc _ ≤ ‖G₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β ^ 2 := mul_le_mul (le_trans hG₁_le hGa5)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 5 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  -- ‖R‖ ≤ 6·s⁵ via R_eq_neg_deg5_residual + norm_R_residual_sum_le.
  have hR_neg : R = -(G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂)) := by
    have h := R_eq_neg_deg5_residual 𝕂 (exp a) (exp b) a b
    simp only [hR_def, hG₁_def, hG₂_def, hF₁_def, hF₂_def, hE₁_def, hE₂_def,
      hD₁_def, hD₂_def, hQ_def, hT₃_def, hT₄_def] at h
    convert h using 1
  have h_aF₂_s5 : ‖a * F₂‖ ≤ s ^ 5 :=
    calc _ ≤ ‖a‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 4 := mul_le_mul_of_nonneg_left (le_trans hF₂_le hFb4) hα_nn
      _ ≤ s * s ^ 4 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 4)
          (by positivity) hs_nn
      _ = s ^ 5 := by ring
  have h_F₁b_s5 : ‖F₁ * b‖ ≤ s ^ 5 :=
    calc _ ≤ ‖F₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β := mul_le_mul (le_trans hF₁_le hFa4) le_rfl hβ_nn (by positivity)
      _ ≤ s ^ 4 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4) hβ_le
          (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have h_G₁_s5 : ‖G₁‖ ≤ s ^ 5 :=
    le_trans hG₁_le (le_trans hGa5 (pow_le_pow_left₀ hα_nn hα_le 5))
  have h_G₂_s5 : ‖G₂‖ ≤ s ^ 5 :=
    le_trans hG₂_le (le_trans hGb5 (pow_le_pow_left₀ hβ_nn hβ_le 5))
  have h_E₁E₂_s6 : ‖E₁ * E₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖E₁‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 3 := mul_le_mul (le_trans hE₁_le hEa3)
          (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_E₁b2_s5 : ‖E₁ * b ^ 2‖ ≤ s ^ 5 :=
    calc _ ≤ ‖E₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 2 := mul_le_mul (le_trans hE₁_le hEa3)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have h_a2E₂_s5 : ‖a ^ 2 * E₂‖ ≤ s ^ 5 :=
    calc _ ≤ ‖a ^ 2‖ * ‖E₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 3 := mul_le_mul (norm_pow_le _ _)
          (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 5 := by ring
  have hR_le : ‖R‖ ≤ 6 * s ^ 5 := by
    rw [hR_neg, norm_neg]
    exact norm_R_residual_sum_le G₁ G₂ F₁ F₂ E₁ E₂ a b hs_nn hs_small_le
      h_G₁_s5 h_G₂_s5 h_aF₂_s5 h_F₁b_s5 h_E₁E₂_s6 h_E₁b2_s5 h_a2E₂_s5
  -- ‖R + T₅‖ ≤ 6·s⁶ via R_plus_T5_eq_neg_deg6_residual.
  have hRT5_neg : R + T₅ = -(H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (F₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂)) := by
    have h := R_plus_T5_eq_neg_deg6_residual 𝕂 (exp a) (exp b) a b
    simp only [hR_def, hH₁_def, hH₂_def, hG₁_def, hG₂_def, hF₁_def, hF₂_def,
      hE₁_def, hE₂_def, hD₁_def, hD₂_def, hQ_def, hT₃_def, hT₄_def, hT₅_def] at h
    convert h using 1
  have h_H₁_s6 : ‖H₁‖ ≤ s ^ 6 :=
    le_trans hH₁_le (le_trans hHa6 (pow_le_pow_left₀ hα_nn hα_le 6))
  have h_H₂_s6 : ‖H₂‖ ≤ s ^ 6 :=
    le_trans hH₂_le (le_trans hHb6 (pow_le_pow_left₀ hβ_nn hβ_le 6))
  have h_aG₂_s6 : ‖a * G₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖a‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 5 := mul_le_mul_of_nonneg_left (le_trans hG₂_le hGb5) hα_nn
      _ ≤ s * s ^ 5 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 5)
          (by positivity) hs_nn
      _ = s ^ 6 := by ring
  have h_G₁b_s6 : ‖G₁ * b‖ ≤ s ^ 6 :=
    calc _ ≤ ‖G₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β := mul_le_mul (le_trans hG₁_le hGa5) le_rfl hβ_nn (by positivity)
      _ ≤ s ^ 5 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5) hβ_le
          (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_a2F₂_s6 : ‖a ^ 2 * F₂‖ ≤ s ^ 6 :=
    calc _ ≤ ‖a ^ 2‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 4 := mul_le_mul (norm_pow_le _ _)
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have h_F₁b2_s6 : ‖F₁ * b ^ 2‖ ≤ s ^ 6 :=
    calc _ ≤ ‖F₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 2 := mul_le_mul (le_trans hF₁_le hFa4)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 6 := by ring
  have hRT5_le : ‖R + T₅‖ ≤ 6 * s ^ 6 := by
    rw [hRT5_neg, norm_neg]
    exact norm_R_plus_T5_residual_sum_le H₁ H₂ G₁ G₂ F₁ F₂ E₁ E₂ a b hs_nn
      h_H₁_s6 h_H₂_s6 h_aG₂_s6 h_G₁b_s6 h_E₁E₂_s6 h_F₁b2_s6 h_a2F₂_s6
  -- Combined tricky bound: ‖z·R+R·z + T22 + T_extra‖ ≤ 28·s⁷.
  have h_combined : ‖z * R + R * z + T22_resid + T_extra‖ ≤ 28 * s ^ 7 := by
    rw [hT22_def, hT_extra_def]
    exact norm_combined_tricky_le z P R T₂ T₃ T₄ T₅ hs_nn hs_small_le
      hz_le hT₂_le hT₃_le hT₄_le hRT5_le hPmT₂mT₃mT₄
  -- I1_septic_RHS bound: ≤ 21·s⁷.
  have hI1_RHS_le :
      ‖I_a + I_b + a * H₂ + H₁ * b +
        ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
        (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) + (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) +
        (2 : 𝕂)⁻¹ • (z * R + R * z) +
        (2 : 𝕂)⁻¹ • T22_resid +
        (2 : 𝕂)⁻¹ • T_extra‖ ≤ 21 * s ^ 7 := by
    have h := norm_I1_septic_residual_RHS_le (𝕂 := 𝕂) a b z I_a I_b H₁ H₂ F₁ F₂ G₁ G₂
      R T22_resid T_extra hs_nn (by norm_num : (0:ℝ) ≤ 28)
      hI_a_s7 hI_b_s7 h_aH₂_s7 h_H₁b_s7 h_a3F₂_s7 h_F₁b3_s7 h_F₁F₂_s7
      h_a2G₂_s7 h_G₁b2_s7 h_combined
    have h21 : (7 + (28 : ℝ) / 2) * s ^ 7 = 21 * s ^ 7 := by ring
    linarith
  -- Bound ‖I₁ - corr₁ - corr₁_5 - corr₁_6‖ ≤ 21·s⁷.
  have hI1_minus_corrs_le :
      ‖I₁ - ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
        (2 : 𝕂)⁻¹ • W5 -
        (2 : 𝕂)⁻¹ • W6‖ ≤ 21 * s ^ 7 := by
    rw [hI₁_quartic, hI1_decomp_full]
    exact hI1_RHS_le
  -- Now bound pieceB''' via pieceB_septic_decomp.
  have hpieceB : ‖y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
      (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
      (6 : 𝕂)⁻¹ • y ^ 6 -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b‖ ≤ 91 * s ^ 7 := by
    rw [pieceB_septic_decomp 𝕂 a b]
    -- For S₁', convert from QPI form to SPI form for T₃ in corr₁, then apply H1.
    have hI₁_eq_form :
        (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b =
        y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
          (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b := by
      rw [← hH1]
    have hT3_QPI_eq_SPI :
        (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b) =
        (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 := by abel
    have hS1_le :
        ‖(y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
            (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b) -
          ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
            (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
            (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
            (2 : 𝕂)⁻¹ • (z * ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
                (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) +
              ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
                (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) * z) -
            (2 : 𝕂)⁻¹ • T₂ ^ 2) -
          (2 : 𝕂)⁻¹ • W5 -
          (2 : 𝕂)⁻¹ • W6‖ ≤ 21 * s ^ 7 := by
      rw [hT3_QPI_eq_SPI]
      rw [← hI₁_eq_form]
      exact hI1_minus_corrs_le
    -- S₂' = ⅓·(y³-z³) - corr₂ - corr₂_5 - corr₂_6, bound via I2_septic_residual.
    have hyzP : y = z + P := by rw [hP_def]; abel
    have hzeq : z = y - P := by rw [hP_def]; abel
    -- I2 inputs: K_PmT4=6, K_P2=15, K_PzP=13, K_P3=15.
    have hP2_etc_le : ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ ≤ 15 * s ^ 6 := by
      have h := norm_T22_sub_P2_etc_le P T₂ T₃ hs_nn hP_le_s2 hT₂_le hT₃_le hPmT₂ hPmT₂mT₃
      have h_eq : P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ =
          -(T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) := by noncomm_ring
      rw [h_eq, norm_neg]; exact h
    have hPzP_etc_le : ‖P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂‖ ≤ 13 * s ^ 7 :=
      norm_PzP_sub_T2zT2_etc_le z P T₂ T₃ hs_nn hs_small_le hz_le hT₂_le hT₃_le hPmT₂mT₃
    have hP3_le : ‖P ^ 3 - T₂ ^ 3‖ ≤ 15 * s ^ 7 :=
      norm_P3_sub_T23_le P T₂ hs_nn hP_le_s2 hT₂_le hPmT₂
    -- Use pieceB's y3_6 ordering (T₂zT₃, T₂T₃z, T₃zT₂, T₃T₂z).
    have hS2_inner_eq :
        y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3) =
        z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
          (P - T₂ - T₃ - T₄) * z ^ 2 +
        z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) +
        (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂) +
        (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z +
        (P ^ 3 - T₂ ^ 3) := by
      rw [hyzP]; noncomm_ring
    have hS2_inner_le_septic :
        ‖z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
          (P - T₂ - T₃ - T₄) * z ^ 2 +
          z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) +
          (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂) +
          (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z +
          (P ^ 3 - T₂ ^ 3)‖ ≤ 76 * s ^ 7 := by
      have h := norm_I2_septic_residual_RHS_le z P T₂ T₃ T₄ hs_nn
        (by norm_num : (0:ℝ) ≤ 6) (by norm_num : (0:ℝ) ≤ 15)
        (by norm_num : (0:ℝ) ≤ 13) (by norm_num : (0:ℝ) ≤ 15)
        hz_le hPmT₂mT₃mT₄ hP2_etc_le hPzP_etc_le hP3_le
      have h_eq : (3 * 6 + 2 * 15 + 13 + 15 : ℝ) * s ^ 7 = 76 * s ^ 7 := by ring
      linarith
    have hS2_inner_full :
        ‖y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3)‖ ≤ 76 * s ^ 7 := by
      rw [hS2_inner_eq]; exact hS2_inner_le_septic
    have hS2_smul_eq :
        (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
          z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
          z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
          T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
          T₂ ^ 3) =
        (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3)) := by
      simp only [smul_sub]
    have hS2_le :
        ‖(3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3)‖ ≤ 26 * s ^ 7 := by
      rw [hS2_smul_eq]
      have h_s7nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
      have h_const : (3 : ℝ)⁻¹ * 76 ≤ 26 := by norm_num
      calc _ ≤ ‖(3 : 𝕂)⁻¹‖ * ‖y ^ 3 - z ^ 3 -
                (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
                (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
                  z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
                (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
                  z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
                  T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
                  T₂ ^ 3)‖ := norm_smul_le _ _
        _ ≤ (3 : ℝ)⁻¹ * (76 * s ^ 7) := by
            rw [h3eq]; exact mul_le_mul_of_nonneg_left hS2_inner_full (by norm_num)
        _ = ((3 : ℝ)⁻¹ * 76) * s ^ 7 := by ring
        _ ≤ 26 * s ^ 7 := by exact mul_le_mul_of_nonneg_right h_const h_s7nn
    -- S₃' = ¼·(y⁴-z⁴-y4_5-y4_6) inner bound 85·s⁷, after ¼: 22·s⁷.
    have hS3_inner_le : ‖y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) -
        (z ^ 3 * T₃ + z ^ 2 * T₃ * z + z * T₃ * z ^ 2 + T₃ * z ^ 3 +
         z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
         T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2)‖ ≤ 85 * s ^ 7 := by
      have h := norm_y4_sub_z4_sub_y4_5_sub_y4_6_le y P T₂ T₃ hs_nn hy_le2
        (by rw [← hzeq]; exact hz_le) hP_le_s2 hT₂_le hPmT₂ hPmT₂mT₃
      rwa [show y - P = z from hzeq.symm] at h
    have hS3_le : ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) -
        (z ^ 3 * T₃ + z ^ 2 * T₃ * z + z * T₃ * z ^ 2 + T₃ * z ^ 3 +
         z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
         T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2))‖ ≤
        22 * s ^ 7 := by
      have h_s7nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
      have h_const : (4 : ℝ)⁻¹ * 85 ≤ 22 := by norm_num
      calc _ ≤ ‖(4 : 𝕂)⁻¹‖ * ‖y ^ 4 - z ^ 4 -
                (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) -
                (z ^ 3 * T₃ + z ^ 2 * T₃ * z + z * T₃ * z ^ 2 + T₃ * z ^ 3 +
                 z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
                 T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2)‖ :=
            norm_smul_le _ _
        _ ≤ (4 : ℝ)⁻¹ * (85 * s ^ 7) := by
            rw [h4eq]; exact mul_le_mul_of_nonneg_left hS3_inner_le (by norm_num)
        _ = ((4 : ℝ)⁻¹ * 85) * s ^ 7 := by ring
        _ ≤ 22 * s ^ 7 := mul_le_mul_of_nonneg_right h_const h_s7nn
    -- S₄' = ⅕·(y⁵-z⁵-y5_6) inner bound 51·s⁷, after ⅕: 11·s⁷.
    have hS4_inner_le : ‖y ^ 5 - z ^ 5 -
        (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
         z * T₂ * z ^ 3 + T₂ * z ^ 4)‖ ≤ 51 * s ^ 7 := by
      have h := norm_y5_sub_z5_sub_y5_6_le y P T₂ hs_nn hy_le2
        (by rw [← hzeq]; exact hz_le) hP_le_s2 hPmT₂
      rwa [show y - P = z from hzeq.symm] at h
    have hS4_le : ‖(5 : 𝕂)⁻¹ • (y ^ 5 - z ^ 5 -
        (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
         z * T₂ * z ^ 3 + T₂ * z ^ 4))‖ ≤ 11 * s ^ 7 := by
      have h_s7nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
      have h_const : (5 : ℝ)⁻¹ * 51 ≤ 11 := by norm_num
      calc _ ≤ ‖(5 : 𝕂)⁻¹‖ * ‖y ^ 5 - z ^ 5 -
                (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
                 z * T₂ * z ^ 3 + T₂ * z ^ 4)‖ := norm_smul_le _ _
        _ ≤ (5 : ℝ)⁻¹ * (51 * s ^ 7) := by
            rw [h5eq]; exact mul_le_mul_of_nonneg_left hS4_inner_le (by norm_num)
        _ = ((5 : ℝ)⁻¹ * 51) * s ^ 7 := by ring
        _ ≤ 11 * s ^ 7 := mul_le_mul_of_nonneg_right h_const h_s7nn
    -- S₅ = ⅙·(y⁶-z⁶) inner bound 63·s⁷, after ⅙: 11·s⁷.
    have hS5_inner_le : ‖y ^ 6 - z ^ 6‖ ≤ 63 * s ^ 7 := by
      have h := norm_pow6_sub_zpow6_le y P hs_nn hy_le2
        (by rw [← hzeq]; exact hz_le) hP_le_s2
      rwa [show y - P = z from hzeq.symm] at h
    have hS5_le : ‖(6 : 𝕂)⁻¹ • (y ^ 6 - z ^ 6)‖ ≤ 11 * s ^ 7 := by
      have h_s7nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
      have h_const : (6 : ℝ)⁻¹ * 63 ≤ 11 := by norm_num
      calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖y ^ 6 - z ^ 6‖ := norm_smul_le _ _
        _ ≤ (6 : ℝ)⁻¹ * (63 * s ^ 7) := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left hS5_inner_le (by norm_num)
        _ = ((6 : ℝ)⁻¹ * 63) * s ^ 7 := by ring
        _ ≤ 11 * s ^ 7 := mul_le_mul_of_nonneg_right h_const h_s7nn
    -- Triangle inequality on the 5-piece sum: S₁'+S₂'-S₃'+S₄'-S₅.
    -- Unfold set-bound vars in hS_i_le to match the goal's unfolded form.
    simp only [hy_def, hz_def, hT₂_def, hT₃_def, hT₄_def, hT₅_def, hW5_def, hW6_def,
      hT_extra_def] at hS1_le hS2_le hS3_le hS4_le hS5_le
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl)
      le_rfl).trans ?_
    have h_sum := add_le_add (add_le_add (add_le_add (add_le_add hS1_le hS2_le) hS3_le)
      hS4_le) hS5_le
    have h_eq : (21 : ℝ) * s ^ 7 + 26 * s ^ 7 + 22 * s ^ 7 + 11 * s ^ 7 + 11 * s ^ 7
        = 91 * s ^ 7 := by ring
    linarith
  -- COMBINE pieceA + pieceB'''.
  calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
          (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 +
          (6 : 𝕂)⁻¹ • y ^ 6‖ +
        ‖y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
          (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
          (6 : 𝕂)⁻¹ • y ^ 6 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
          bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b‖ := norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 7 / (2 - Real.exp s) + 91 * s ^ 7 := by
        linarith [hpieceA, hpieceB]
    _ ≤ (Real.exp s - 1) ^ 7 / (2 - Real.exp s) +
        91 * s ^ 7 / (2 - Real.exp s) := by
        gcongr
        rw [le_div_iff₀ hdenom]
        nlinarith [pow_nonneg hs_nn 7]
    _ = ((Real.exp s - 1) ^ 7 + 91 * s ^ 7) / (2 - Real.exp s) :=
        (add_div _ _ _).symm
    _ ≤ 1000 * s ^ 7 / (2 - Real.exp s) := by
        apply div_le_div_of_nonneg_right _ hdenom.le
        linarith [hexp7, pow_nonneg hs_nn 7]

include 𝕂 in
/-- **Order-7 BCH remainder bound** (public theorem, T2-F7e step 4):

  `‖bch(a, b) - (a+b) - ½[a,b] - C₃ - C₄ - bqt - bch_sextic_term‖ ≤
   1000010 · s⁷ / (2 - exp(s))`  for `s < log 2`.

Proof: case split on `s ≥ 1/10` (uses `norm_bch_septic_remainder_large_s_le`,
fully proved) vs. `s < 1/10` (uses `norm_bch_septic_remainder_small_s_le`,
fully proved via `pieceB_septic_decomp` + 5 sub-piece bounds).

This is the deg-7+ remainder of the BCH series after subtracting the
through-deg-6 expansion. It's the order-7 analog of `norm_bch_sextic_remainder_le`
and the foundation for extending the cubic template to discharge the parent
Tier-2 axiom (T2-F7e). -/
theorem norm_bch_septic_remainder_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b‖ ≤
      1000010 * (‖a‖ + ‖b‖) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  by_cases hs : 1 / 10 ≤ ‖a‖ + ‖b‖
  · -- Large-s: ‖LHS‖ ≤ 1000010·s⁷/(2-exp(s)) directly.
    exact norm_bch_septic_remainder_large_s_le (𝕂 := 𝕂) a b hab hs
  · -- Small-s: ‖LHS‖ ≤ 1000·s⁷/(2-exp(s)) ≤ 1000010·s⁷/(2-exp(s)).
    push_neg at hs
    have h_small := norm_bch_septic_remainder_small_s_le (𝕂 := 𝕂) a b hab hs
    have hexp_lt : Real.exp (‖a‖ + ‖b‖) < 2 := by
      calc Real.exp (‖a‖ + ‖b‖) < Real.exp (Real.log 2) := Real.exp_strictMono hab
        _ = 2 := Real.exp_log (by norm_num)
    have hdenom : 0 < 2 - Real.exp (‖a‖ + ‖b‖) := by linarith
    have hs_nn : 0 ≤ ‖a‖ + ‖b‖ := by positivity
    calc _ ≤ 1000 * (‖a‖ + ‖b‖) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := h_small
      _ ≤ 1000010 * (‖a‖ + ‖b‖) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
          apply div_le_div_of_nonneg_right _ hdenom.le
          have : 1000 * (‖a‖ + ‖b‖) ^ 7 ≤ 1000010 * (‖a‖ + ‖b‖) ^ 7 := by
            nlinarith [pow_nonneg hs_nn 7]
          linarith

include 𝕂 in
/-- **PieceA bound for the octic small-s discharge.**

The deg-8 log-series tail bound applied to `y := exp(a)·exp(b) - 1`, expressed
in terms of `s := ‖a‖+‖b‖` rather than `‖y‖`. For `s < 1/10` (with `s < log 2`),

  `‖logOnePlus y - y + y²/2 - y³/3 + y⁴/4 - y⁵/5 + y⁶/6 - y⁷/7‖
   ≤ 3 · s⁸ / (2 - exp(s))`.

Combines `norm_logOnePlus_sub_sub_sub_sub_sub_sub_sub_le` (LogSeries.lean,
deg-7 log truncation tail `≤ ‖y‖⁸/(1-‖y‖)`) with `real_exp_sub_one_pow8_le_small`
(`(exp s - 1)⁸ ≤ 3·s⁸` for `s ≤ 1/10`). The denominator conversion uses
`‖y‖ ≤ exp s - 1`, so `1 - ‖y‖ ≥ 2 - exp s`. Constant is 3 (not 2 as for the
septic pieceA) because `(1 + 1/10)⁸ ≈ 2.144 > 2`.

Foundation for the eventual `norm_bch_octic_remainder_small_s_le` discharge
of `norm_bch_octic_remainder_small_s_axiom` (analog of the septic discharge
in session 19; the deg-8+ analog of the septic pieceA bound used inline in
`norm_bch_septic_remainder_small_s_le`). -/
private theorem norm_bch_octic_pieceA_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖logOnePlus (𝕂 := 𝕂) (exp a * exp b - 1) - (exp a * exp b - 1) +
      (2 : 𝕂)⁻¹ • (exp a * exp b - 1) ^ 2 -
      (3 : 𝕂)⁻¹ • (exp a * exp b - 1) ^ 3 +
      (4 : 𝕂)⁻¹ • (exp a * exp b - 1) ^ 4 -
      (5 : 𝕂)⁻¹ • (exp a * exp b - 1) ^ 5 +
      (6 : 𝕂)⁻¹ • (exp a * exp b - 1) ^ 6 -
      (7 : 𝕂)⁻¹ • (exp a * exp b - 1) ^ 7‖ ≤
      3 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set s := ‖a‖ + ‖b‖ with hs_def
  set y := exp a * exp b - 1 with hy_def
  set α := ‖a‖
  set β := ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hs_small_le : s ≤ 1 / 10 := hs_small.le
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have hy_eq : y = (exp a - 1) * exp b + (exp b - 1) := by
      rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [hy_eq]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          apply add_le_add
          · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
              (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hE1_nn : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
  have hexp8_le : (Real.exp s - 1) ^ 8 ≤ 3 * s ^ 8 :=
    real_exp_sub_one_pow8_le_small hs_nn hs_small_le
  calc _ ≤ ‖y‖ ^ 8 / (1 - ‖y‖) :=
          norm_logOnePlus_sub_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) y hy_lt
    _ ≤ (Real.exp s - 1) ^ 8 / (2 - Real.exp s) :=
        div_le_div₀ (pow_nonneg hE1_nn 8)
          (pow_le_pow_left₀ (norm_nonneg _) hy_le 8) hdenom (by linarith)
    _ ≤ 3 * s ^ 8 / (2 - Real.exp s) := by
        apply div_le_div_of_nonneg_right _ hdenom.le
        linarith

set_option maxHeartbeats 64000000 in
include 𝕂 in
/-- **Eighth-order BCH remainder, small-s case** (octic stepping stone, fully proved).

For `‖a‖+‖b‖ < 1/10` and `‖a‖+‖b‖ < log 2`:

  `‖bch(a, b) - through-deg-7 expansion‖ ≤ 1000 · s⁸ / (2 - exp(s))`.

Proof mirrors `norm_bch_septic_remainder_small_s_le` at one degree higher, using
`octic_pure_identity` (the deg-7 cancellation), `pieceB_octic_decomp` (the
central decomposition into 6 pieces), `norm_combined_tricky_octic_le` (35·s⁸
for I₁'s "tricky" cluster), `norm_I1_octic_residual_RHS_le` (≤ 25·s⁸ for I₁),
`norm_I2_octic_residual_RHS_le` (171·s⁸ for I₂'s inner with K_PmT5=6, K_P2'=16,
K_PzP'=16, K_P3'=105), and the inner bounds for S₃'..S₆ via
`norm_y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_le` (285·s⁸),
`norm_y5_sub_z5_sub_y5_6_sub_y5_7_le` (141·s⁸),
`norm_y6_sub_z6_sub_y6_7_le` (87·s⁸), and `norm_pow7_sub_zpow7_le` (127·s⁸).
Total pieceB'''' ≤ 217·s⁸. Combined with pieceA ≤ 3·s⁸/(2-exp(s)) gives
≤ 220·s⁸/(2-exp(s)) ≤ 1000·s⁸/(2-exp(s)). -/
private theorem norm_bch_octic_remainder_small_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
      bch_septic_term 𝕂 a b‖ ≤
      1000 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  -- SETUP.
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖
  set β := ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hs_small_le : s ≤ 1 / 10 := hs_small.le
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hs1 : s < 1 := by linarith
  have hs_le_one : s ≤ 1 := hs1.le
  have hs34 : s < 3 / 4 := by linarith
  have hs56 : s < 5 / 6 := by linarith
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  set y := exp a * exp b - 1 with hy_def
  set z := a + b with hz_def
  set P := y - z with hP_def
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have hy_eq : y = (exp a - 1) * exp b + (exp b - 1) := by
      rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [hy_eq]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          apply add_le_add
          · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
              (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn,
         Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  have hy_le2 : ‖y‖ ≤ 2 * s := by
    calc ‖y‖ ≤ Real.exp s - 1 := hy_le
      _ ≤ s + s ^ 2 := by linarith
      _ ≤ 2 * s := by nlinarith [sq_nonneg s]
  have hz_le : ‖z‖ ≤ s := by rw [hz_def]; exact norm_add_le _ _
  -- Exp remainders D, E, F, G, H, I, J.
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set G₁ := F₁ - (24 : 𝕂)⁻¹ • a ^ 4 with hG₁_def
  set G₂ := F₂ - (24 : 𝕂)⁻¹ • b ^ 4 with hG₂_def
  set H₁ := G₁ - (120 : 𝕂)⁻¹ • a ^ 5 with hH₁_def
  set H₂ := G₂ - (120 : 𝕂)⁻¹ • b ^ 5 with hH₂_def
  set I_a := H₁ - (720 : 𝕂)⁻¹ • a ^ 6 with hI_a_def
  set I_b := H₂ - (720 : 𝕂)⁻¹ • b ^ 6 with hI_b_def
  set J_a := I_a - (5040 : 𝕂)⁻¹ • a ^ 7 with hJ_a_def
  set J_b := I_b - (5040 : 𝕂)⁻¹ • b ^ 7 with hJ_b_def
  set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
  set W_H1 := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
      z * P - P * z - P ^ 2 with hW_H1_def
  set T₂ := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2 with hT₂_def
  set T₃ := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
      (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 with hT₃_def
  set T₄ := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
      (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
      (24 : 𝕂)⁻¹ • b ^ 4 with hT₄_def
  set T₅ := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
      (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
      (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5 with hT₅_def
  set T₆ := (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
      (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
      (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
      (720 : 𝕂)⁻¹ • b ^ 6 with hT₆_def
  set W5 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
      (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
      (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
      (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂) with hW5_def
  set W6 := (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
      (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
      (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
      (360 : 𝕂)⁻¹ • b ^ 6 -
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) with hW6_def
  set W7 := (2520 : 𝕂)⁻¹ • a ^ 7 + (360 : 𝕂)⁻¹ • (a ^ 6 * b) +
      (120 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (72 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
      (72 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (120 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
      (360 : 𝕂)⁻¹ • (a * b ^ 6) + (2520 : 𝕂)⁻¹ • b ^ 7 -
      (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z) with hW7_def
  -- Norm bounds for D, E, F, G, H, I, J.
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖α‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hα_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDa_nn,
         Real.norm_eq_abs, abs_of_nonneg hα_nn] at h
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖β‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hβ_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDb_nn,
         Real.norm_eq_abs, abs_of_nonneg hβ_nn] at h
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hG₁_le : ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hG₂_le : ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
    norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hGa5 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 ≤ α ^ 5 :=
    real_exp_fifth_order_le_quintic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hGb5 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 ≤ β ^ 5 :=
    real_exp_fifth_order_le_quintic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hH₁_le : ‖H₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hH₂_le : ‖H₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hHa6 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 ≤
      α ^ 6 :=
    real_exp_sixth_order_le_sextic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hHb6 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 ≤
      β ^ 6 :=
    real_exp_sixth_order_le_sextic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hI_a_le : ‖I_a‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hI_b_le : ‖I_b‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hIa7 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 -
      α ^ 6 / 720 ≤ α ^ 7 :=
    real_exp_seventh_order_le_septic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hIb7 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 -
      β ^ 6 / 720 ≤ β ^ 7 :=
    real_exp_seventh_order_le_septic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- New: J_a, J_b at deg-8.
  have hJ_a_le : ‖J_a‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 -
      α ^ 5 / 120 - α ^ 6 / 720 - α ^ 7 / 5040 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) a
  have hJ_b_le : ‖J_b‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 -
      β ^ 5 / 120 - β ^ 6 / 720 - β ^ 7 / 5040 :=
    norm_exp_sub_one_sub_sub_sub_sub_sub_sub_sub_le (𝕂 := 𝕂) b
  have hJa8 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 - α ^ 5 / 120 -
      α ^ 6 / 720 - α ^ 7 / 5040 ≤ α ^ 8 :=
    real_exp_eighth_order_le_octic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hJb8 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 - β ^ 5 / 120 -
      β ^ 6 / 720 - β ^ 7 / 5040 ≤ β ^ 8 :=
    real_exp_eighth_order_le_octic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  -- ‖P‖ ≤ s² and friends.
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
    have hP_split : P = a * (exp b - 1) + D₁ * exp b + D₂ := by
      simp only [hP_def, hy_def, hz_def, hD₁_def, hD₂_def]; noncomm_ring
    calc ‖P‖ = ‖a * (exp b - 1) + D₁ * exp b + D₂‖ := by rw [hP_split]
      _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
          calc _ ≤ ‖a * (exp b - 1) + D₁ * exp b‖ + ‖D₂‖ := norm_add_le _ _
            _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
                gcongr; exact norm_add_le _ _
      _ ≤ α * (Real.exp β - 1) + (Real.exp α - 1 - α) * Real.exp β +
          (Real.exp β - 1 - β) := by
          have h1 : ‖a * (exp b - 1)‖ ≤ α * (Real.exp β - 1) :=
            calc _ ≤ ‖a‖ * ‖exp b - 1‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_exp_sub_one_le (𝕂 := 𝕂) b
          have h2 : ‖D₁ * exp b‖ ≤ (Real.exp α - 1 - α) * Real.exp β :=
            calc _ ≤ ‖D₁‖ * ‖exp b‖ := norm_mul_le _ _
              _ ≤ _ := mul_le_mul hD₁_le (norm_exp_le (𝕂 := 𝕂) b)
                  (norm_nonneg _) (by linarith)
          linarith [hD₂_le]
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  have hP_le_s2 : ‖P‖ ≤ s ^ 2 := le_trans hP_le hEs2
  have hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3 := by
    have hS_eq : P - T₂ = E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂ := by
      simp only [hP_def, hy_def, hT₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hz_def]
      noncomm_ring
    rw [hS_eq]
    have hE₁_s3 : ‖E₁‖ ≤ α ^ 3 := le_trans hE₁_le hEa3
    have hE₂_s3 : ‖E₂‖ ≤ β ^ 3 := le_trans hE₂_le hEb3
    have haD₂ : ‖a * D₂‖ ≤ α * β ^ 2 :=
      calc _ ≤ ‖a‖ * ‖D₂‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans hD₂_le hDb2) hα_nn
    have hD₁b : ‖D₁ * b‖ ≤ α ^ 2 * β :=
      calc _ ≤ ‖D₁‖ * ‖b‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) le_rfl hβ_nn (by positivity)
    have hDD : ‖D₁ * D₂‖ ≤ α ^ 2 * β ^ 2 :=
      calc _ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
            (norm_nonneg _) (by positivity)
    calc ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖
        ≤ ‖E₁‖ + ‖E₂‖ + ‖a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖ := by
          have := norm_add_le E₁ E₂
          have := norm_add_le (E₁ + E₂) (a * D₂)
          have := norm_add_le (E₁ + E₂ + a * D₂) (D₁ * b)
          have := norm_add_le (E₁ + E₂ + a * D₂ + D₁ * b) (D₁ * D₂)
          linarith
      _ ≤ α ^ 3 + β ^ 3 + α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 := by
          linarith [hE₁_s3, hE₂_s3, haD₂, hD₁b, hDD]
      _ ≤ 5 * s ^ 3 := by
          nlinarith [pow_le_pow_left₀ hα_nn hα_le 3, pow_le_pow_left₀ hβ_nn hβ_le 3,
            pow_le_pow_left₀ hα_nn hα_le 2, pow_le_pow_left₀ hβ_nn hβ_le 2,
            pow_nonneg hs_nn 4]
  have hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4 := by
    have h := norm_P_sub_T2_sub_T3_le (𝕂 := 𝕂) a b hs_nn hs34 hα_le hβ_le
    have hP_unfold : P = exp a * exp b - 1 - (a + b) := by
      rw [hP_def, hy_def, hz_def]
    rw [hP_unfold, hT₂_def, hT₃_def]
    exact h
  have hPmT₂mT₃mT₄ : ‖P - T₂ - T₃ - T₄‖ ≤ 6 * s ^ 5 := by
    have h := norm_P_sub_T2_sub_T3_sub_T4_le (𝕂 := 𝕂) a b hs_nn hs34 hα_le hβ_le
    have hP_unfold : P = exp a * exp b - 1 - (a + b) := by
      rw [hP_def, hy_def, hz_def]
    rw [hP_unfold, hT₂_def, hT₃_def, hT₄_def]
    exact h
  -- New: deg-6 P-tail.
  have hPmT₂mT₃mT₄mT₅ : ‖P - T₂ - T₃ - T₄ - T₅‖ ≤ 6 * s ^ 6 := by
    have h := norm_P_sub_T2_sub_T3_sub_T4_sub_T5_le (𝕂 := 𝕂) a b hs_nn hs34 hα_le hβ_le
    have hP_unfold : P = exp a * exp b - 1 - (a + b) := by
      rw [hP_def, hy_def, hz_def]
    rw [hP_unfold, hT₂_def, hT₃_def, hT₄_def, hT₅_def]
    exact h
  have h2_le : ‖(2 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h3eq : ‖(3 : 𝕂)⁻¹‖ = (3 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h4eq : ‖(4 : 𝕂)⁻¹‖ = (4 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h5eq : ‖(5 : 𝕂)⁻¹‖ = (5 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h7eq : ‖(7 : 𝕂)⁻¹‖ = (7 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hT₂_le : ‖T₂‖ ≤ s ^ 2 := by
    have h1 : ‖a * b‖ ≤ α * β := norm_mul_le _ _
    have h2 : ‖(2:𝕂)⁻¹ • a^2‖ ≤ α^2 :=
      calc _ ≤ 1 * ‖a‖ ^ 2 := (norm_smul_le _ _).trans
              (mul_le_mul h2_le (norm_pow_le a 2) (norm_nonneg _) (by norm_num))
        _ = α^2 := one_mul _
    have h3 : ‖(2:𝕂)⁻¹ • b^2‖ ≤ β^2 :=
      calc _ ≤ 1 * ‖b‖ ^ 2 := (norm_smul_le _ _).trans
              (mul_le_mul h2_le (norm_pow_le b 2) (norm_nonneg _) (by norm_num))
        _ = β^2 := one_mul _
    have htriangle : ‖T₂‖ ≤ ‖a * b‖ + ‖(2:𝕂)⁻¹ • a^2‖ + ‖(2:𝕂)⁻¹ • b^2‖ := by
      rw [hT₂_def]
      have n1 := norm_add_le (a * b + (2:𝕂)⁻¹ • a^2) ((2:𝕂)⁻¹ • b^2)
      have n2 := norm_add_le (a * b) ((2:𝕂)⁻¹ • a^2)
      linarith
    have hs2 : s^2 = α^2 + 2*α*β + β^2 := by rw [hs_def]; ring
    have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
    linarith
  have hT₃_le : ‖T₃‖ ≤ s ^ 3 := by
    have hT1 : ‖(6:𝕂)⁻¹ • a^3‖ ≤ α^3 / 6 := by
      calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖a^3‖ := norm_smul_le _ _
        _ ≤ (6:ℝ)⁻¹ * α^3 := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
        _ = α^3 / 6 := by ring
    have hT2_norm : ‖(2:𝕂)⁻¹ • (a^2*b)‖ ≤ α^2 * β / 2 := by
      have hab_le : ‖a^2*b‖ ≤ α^2 * β :=
        calc _ ≤ ‖a^2‖ * ‖b‖ := norm_mul_le _ _
          _ ≤ α^2 * β := mul_le_mul (norm_pow_le _ _) le_rfl hβ_nn (by positivity)
      calc _ ≤ ‖(2:𝕂)⁻¹‖ * ‖a^2*b‖ := norm_smul_le _ _
        _ ≤ (2:ℝ)⁻¹ * (α^2 * β) := by
            rw [h2eq]; exact mul_le_mul_of_nonneg_left hab_le (by norm_num)
        _ = α^2 * β / 2 := by ring
    have hT3 : ‖(2:𝕂)⁻¹ • (a*b^2)‖ ≤ α * β^2 / 2 := by
      have hab_le : ‖a*b^2‖ ≤ α * β^2 :=
        calc _ ≤ ‖a‖ * ‖b^2‖ := norm_mul_le _ _
          _ ≤ α * β^2 := mul_le_mul le_rfl (norm_pow_le _ _) (by positivity) hα_nn
      calc _ ≤ ‖(2:𝕂)⁻¹‖ * ‖a*b^2‖ := norm_smul_le _ _
        _ ≤ (2:ℝ)⁻¹ * (α * β^2) := by
            rw [h2eq]; exact mul_le_mul_of_nonneg_left hab_le (by norm_num)
        _ = α * β^2 / 2 := by ring
    have hT4_norm : ‖(6:𝕂)⁻¹ • b^3‖ ≤ β^3 / 6 := by
      calc _ ≤ ‖(6:𝕂)⁻¹‖ * ‖b^3‖ := norm_smul_le _ _
        _ ≤ (6:ℝ)⁻¹ * β^3 := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by norm_num)
        _ = β^3 / 6 := by ring
    have htriangle : ‖T₃‖ ≤ ‖(6:𝕂)⁻¹ • a^3‖ + ‖(2:𝕂)⁻¹ • (a^2*b)‖ +
        ‖(2:𝕂)⁻¹ • (a*b^2)‖ + ‖(6:𝕂)⁻¹ • b^3‖ := by
      rw [hT₃_def]
      have n1 := norm_add_le ((6:𝕂)⁻¹ • a^3 + (2:𝕂)⁻¹ • (a^2*b) +
        (2:𝕂)⁻¹ • (a*b^2)) ((6:𝕂)⁻¹ • b^3)
      have n2 := norm_add_le ((6:𝕂)⁻¹ • a^3 + (2:𝕂)⁻¹ • (a^2*b)) ((2:𝕂)⁻¹ • (a*b^2))
      have n3 := norm_add_le ((6:𝕂)⁻¹ • a^3) ((2:𝕂)⁻¹ • (a^2*b))
      linarith
    have hs3 : s^3 = α^3 + 3*α^2*β + 3*α*β^2 + β^3 := by rw [hs_def]; ring
    have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
    have hα2β : 0 ≤ α^2 * β := mul_nonneg (sq_nonneg _) hβ_nn
    have hαβ2 : 0 ≤ α * β^2 := mul_nonneg hα_nn (sq_nonneg _)
    nlinarith [pow_nonneg hα_nn 3, pow_nonneg hβ_nn 3]
  have hT₄_le : ‖T₄‖ ≤ s ^ 4 := by
    rw [hT₄_def]; exact norm_T4_le (𝕂 := 𝕂) a b hs_nn hα_le hβ_le
  have hT₅_le : ‖T₅‖ ≤ s ^ 5 := by
    rw [hT₅_def]; exact norm_T5_le (𝕂 := 𝕂) a b hs_nn hα_le hβ_le
  -- New: T₆ bound.
  have hT₆_le : ‖T₆‖ ≤ s ^ 6 := by
    rw [hT₆_def]; exact norm_T6_le (𝕂 := 𝕂) a b hs_nn hα_le hβ_le
  -- H1 identity.
  have hH1 : y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 =
      (2 : 𝕂)⁻¹ • W_H1 := by
    suffices h : (2 : 𝕂) • (y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2) = (2 : 𝕂) • ((2 : 𝕂)⁻¹ • W_H1) by
      have hinj : Function.Injective ((2 : 𝕂) • · : 𝔸 → 𝔸) := by
        intro x₀ y₀ hxy; have := congrArg ((2 : 𝕂)⁻¹ • ·) hxy
        simp only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] at this; exact this
      exact hinj h
    rw [smul_smul, mul_inv_cancel₀ h2ne, one_smul]
    simp only [hE₁_def, hE₂_def, hD₁_def, hD₂_def, hP_def, hy_def, hW_H1_def, hz_def,
      smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h2ne, one_smul, two_smul]
    noncomm_ring
  -- Decomposition: LHS = pieceA + pieceB''''.
  have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b - bch_quintic_term 𝕂 a b -
      bch_sextic_term 𝕂 a b - bch_septic_term 𝕂 a b =
      (logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
        (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 + (6 : 𝕂)⁻¹ • y ^ 6 -
        (7 : 𝕂)⁻¹ • y ^ 7) +
      (y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
        (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
        (6 : 𝕂)⁻¹ • y ^ 6 + (7 : 𝕂)⁻¹ • y ^ 7 -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
        bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
        bch_septic_term 𝕂 a b) := by
    unfold bch; rw [hz_def]; abel
  rw [hdecomp]
  -- Bound pieceA via norm_bch_octic_pieceA_le.
  have hpieceA : ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
      (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 +
      (6 : 𝕂)⁻¹ • y ^ 6 - (7 : 𝕂)⁻¹ • y ^ 7‖ ≤
      3 * s ^ 8 / (2 - Real.exp s) := by
    have h := norm_bch_octic_pieceA_le (𝕂 := 𝕂) a b hab hs_small
    rw [← hy_def] at h
    exact h
  -- Define I₁ via H1+quartic_identity, and the cluster vars R, T22, T_extra, T_extra2.
  set I₁ := (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 -
      bch_cubic_term 𝕂 a b with hI₁_def
  have hI₁_quartic : I₁ =
      F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
      (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
      (2 : 𝕂)⁻¹ • P ^ 2 := by
    rw [hI₁_def]; exact quartic_identity 𝕂 (exp a) (exp b) a b
  set R := T₃ - E₁ - E₂ - Q + T₄ with hR_def
  set T22_resid := T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂ with hT22_def
  set T_extra := z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z with hT_extra_def
  set T_extra2 := z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z
    with hT_extra2_def
  -- Apply I1_octic_residual_decomp_eq.
  have hI1_decomp_full :
      (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
        (2 : 𝕂)⁻¹ • P ^ 2) -
        ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
          (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
          (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
          (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
        (2 : 𝕂)⁻¹ • W5 -
        (2 : 𝕂)⁻¹ • W6 -
        (2 : 𝕂)⁻¹ • W7 =
      J_a + J_b + a * I_b + I_a * b +
      ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
      (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) + (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) +
      (2 : 𝕂)⁻¹ • (z * R + R * z) +
      (2 : 𝕂)⁻¹ • T22_resid +
      (2 : 𝕂)⁻¹ • T_extra +
      (2 : 𝕂)⁻¹ • T_extra2 := by
    have h := I1_octic_residual_decomp_eq 𝕂 (exp a) (exp b) a b
    simp only [hJ_a_def, hJ_b_def, hI_a_def, hI_b_def, hH₁_def, hH₂_def,
      hG₁_def, hG₂_def, hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def,
      hQ_def, hR_def, hT22_def, hT_extra_def, hT_extra2_def, hP_def, hy_def,
      hz_def, hT₂_def, hT₃_def, hT₄_def, hT₅_def, hT₆_def, hW5_def, hW6_def,
      hW7_def] at h
    convert h using 1
  -- Per-component norm bounds at deg-8.
  have hJ_a_s8 : ‖J_a‖ ≤ s ^ 8 :=
    le_trans hJ_a_le (le_trans hJa8 (pow_le_pow_left₀ hα_nn hα_le 8))
  have hJ_b_s8 : ‖J_b‖ ≤ s ^ 8 :=
    le_trans hJ_b_le (le_trans hJb8 (pow_le_pow_left₀ hβ_nn hβ_le 8))
  have h_aI_b_s8 : ‖a * I_b‖ ≤ s ^ 8 :=
    calc _ ≤ ‖a‖ * ‖I_b‖ := norm_mul_le _ _
      _ ≤ α * β ^ 7 := mul_le_mul_of_nonneg_left
          (le_trans hI_b_le hIb7) hα_nn
      _ ≤ s * s ^ 7 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 7)
          (by positivity) hs_nn
      _ = s ^ 8 := by ring
  have h_I_ab_s8 : ‖I_a * b‖ ≤ s ^ 8 :=
    calc _ ≤ ‖I_a‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 7 * β := mul_le_mul (le_trans hI_a_le hIa7) le_rfl hβ_nn (by positivity)
      _ ≤ s ^ 7 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 7) hβ_le
          (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_a3G₂_s8 : ‖a ^ 3 * G₂‖ ≤ s ^ 8 :=
    calc _ ≤ ‖a ^ 3‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 5 := mul_le_mul (norm_pow_le _ _)
          (le_trans hG₂_le hGb5) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 5 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 5) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_G₁b3_s8 : ‖G₁ * b ^ 3‖ ≤ s ^ 8 :=
    calc _ ≤ ‖G₁‖ * ‖b ^ 3‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β ^ 3 := mul_le_mul (le_trans hG₁_le hGa5)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 5 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_F₁F₂_s8 : ‖F₁ * F₂‖ ≤ s ^ 8 :=
    calc ‖F₁ * F₂‖ ≤ ‖F₁‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 4 := mul_le_mul (le_trans hF₁_le hFa4)
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_a2H₂_s8 : ‖a ^ 2 * H₂‖ ≤ s ^ 8 :=
    calc _ ≤ ‖a ^ 2‖ * ‖H₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 6 := mul_le_mul (norm_pow_le _ _)
          (le_trans hH₂_le hHb6) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 6 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 6) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  have h_H₁b2_s8 : ‖H₁ * b ^ 2‖ ≤ s ^ 8 :=
    calc _ ≤ ‖H₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 6 * β ^ 2 := mul_le_mul (le_trans hH₁_le hHa6)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 6 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 6)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 8 := by ring
  -- ‖R + T₅ + T₆‖ ≤ 7·s⁷ via R_plus_T5_plus_T6_eq_neg_deg7_residual + norm sum bound.
  have hRT5T6_neg : R + T₅ + T₆ = -(I_a + I_b + a * H₂ + H₁ * b + F₁ * F₂ +
      (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂) +
      (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * G₂)) := by
    have h := R_plus_T5_plus_T6_eq_neg_deg7_residual 𝕂 (exp a) (exp b) a b
    simp only [hR_def, hI_a_def, hI_b_def, hH₁_def, hH₂_def, hG₁_def, hG₂_def,
      hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hQ_def, hT₃_def,
      hT₄_def, hT₅_def, hT₆_def] at h
    convert h using 1
  have h_I_a_s7 : ‖I_a‖ ≤ s ^ 7 :=
    le_trans hI_a_le (le_trans hIa7 (pow_le_pow_left₀ hα_nn hα_le 7))
  have h_I_b_s7 : ‖I_b‖ ≤ s ^ 7 :=
    le_trans hI_b_le (le_trans hIb7 (pow_le_pow_left₀ hβ_nn hβ_le 7))
  have h_aH₂_s7 : ‖a * H₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a‖ * ‖H₂‖ := norm_mul_le _ _
      _ ≤ α * β ^ 6 := mul_le_mul_of_nonneg_left (le_trans hH₂_le hHb6) hα_nn
      _ ≤ s * s ^ 6 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 6)
          (by positivity) hs_nn
      _ = s ^ 7 := by ring
  have h_H₁b_s7 : ‖H₁ * b‖ ≤ s ^ 7 :=
    calc _ ≤ ‖H₁‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ α ^ 6 * β := mul_le_mul (le_trans hH₁_le hHa6) le_rfl hβ_nn (by positivity)
      _ ≤ s ^ 6 * s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 6) hβ_le
          (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_F₁b3_s7 : ‖F₁ * b ^ 3‖ ≤ s ^ 7 :=
    calc _ ≤ ‖F₁‖ * ‖b ^ 3‖ := norm_mul_le _ _
      _ ≤ α ^ 4 * β ^ 3 := mul_le_mul (le_trans hF₁_le hFa4)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 4 * s ^ 3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4)
          (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_a3F₂_s7 : ‖a ^ 3 * F₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a ^ 3‖ * ‖F₂‖ := norm_mul_le _ _
      _ ≤ α ^ 3 * β ^ 4 := mul_le_mul (norm_pow_le _ _)
          (le_trans hF₂_le hFb4) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 3 * s ^ 4 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
          (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_G₁b2_s7 : ‖G₁ * b ^ 2‖ ≤ s ^ 7 :=
    calc _ ≤ ‖G₁‖ * ‖b ^ 2‖ := norm_mul_le _ _
      _ ≤ α ^ 5 * β ^ 2 := mul_le_mul (le_trans hG₁_le hGa5)
          (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 5 * s ^ 2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 5)
          (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_a2G₂_s7 : ‖a ^ 2 * G₂‖ ≤ s ^ 7 :=
    calc _ ≤ ‖a ^ 2‖ * ‖G₂‖ := norm_mul_le _ _
      _ ≤ α ^ 2 * β ^ 5 := mul_le_mul (norm_pow_le _ _)
          (le_trans hG₂_le hGb5) (norm_nonneg _) (by positivity)
      _ ≤ s ^ 2 * s ^ 5 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
          (pow_le_pow_left₀ hβ_nn hβ_le 5) (by positivity) (by positivity)
      _ = s ^ 7 := by ring
  have h_F₁F₂_s8_septic : ‖F₁ * F₂‖ ≤ s ^ 8 := h_F₁F₂_s8
  have hRT5T6_le : ‖R + T₅ + T₆‖ ≤ 7 * s ^ 7 := by
    rw [hRT5T6_neg, norm_neg]
    exact norm_R_plus_T5_plus_T6_residual_sum_le I_a I_b H₁ H₂ G₁ G₂ F₁ F₂ a b
      hs_nn hs_le_one h_I_a_s7 h_I_b_s7 h_aH₂_s7 h_H₁b_s7 h_F₁F₂_s8_septic
      h_F₁b3_s7 h_a3F₂_s7 h_G₁b2_s7 h_a2G₂_s7
  -- Combined tricky bound: ‖z·R+R·z + T22 + T_extra + T_extra2‖ ≤ 35·s⁸.
  have h_combined : ‖z * R + R * z + T22_resid + T_extra + T_extra2‖ ≤ 35 * s ^ 8 := by
    rw [hT22_def, hT_extra_def, hT_extra2_def]
    exact norm_combined_tricky_octic_le z P R T₂ T₃ T₄ T₅ T₆ hs_nn hs_small_le
      hz_le hT₂_le hT₃_le hT₄_le hT₅_le hRT5T6_le hPmT₂mT₃mT₄mT₅
  -- I1_octic_RHS bound: ≤ 25·s⁸.
  have hI1_RHS_le :
      ‖J_a + J_b + a * I_b + I_a * b +
        ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
        (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) + (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) +
        (2 : 𝕂)⁻¹ • (z * R + R * z) +
        (2 : 𝕂)⁻¹ • T22_resid +
        (2 : 𝕂)⁻¹ • T_extra +
        (2 : 𝕂)⁻¹ • T_extra2‖ ≤ 25 * s ^ 8 := by
    have h := norm_I1_octic_residual_RHS_le (𝕂 := 𝕂) a b z J_a J_b I_a I_b H₁ H₂
      G₁ G₂ F₁ F₂ R T22_resid T_extra T_extra2 hs_nn (by norm_num : (0:ℝ) ≤ 35)
      hJ_a_s8 hJ_b_s8 h_aI_b_s8 h_I_ab_s8 h_a3G₂_s8 h_G₁b3_s8 h_F₁F₂_s8
      h_a2H₂_s8 h_H₁b2_s8 h_combined
    have h25 : (7 + (35 : ℝ) / 2) * s ^ 8 ≤ 25 * s ^ 8 := by
      have : (7 + (35 : ℝ) / 2) ≤ 25 := by norm_num
      nlinarith [pow_nonneg hs_nn 8]
    linarith
  -- Bound ‖I₁ - corr₁ - corr₁_5 - corr₁_6 - corr₁_7‖ ≤ 25·s⁸.
  have hI1_minus_corrs_le :
      ‖I₁ - ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
        (2 : 𝕂)⁻¹ • W5 -
        (2 : 𝕂)⁻¹ • W6 -
        (2 : 𝕂)⁻¹ • W7‖ ≤ 25 * s ^ 8 := by
    rw [hI₁_quartic, hI1_decomp_full]
    exact hI1_RHS_le
  -- Now bound pieceB'''' via pieceB_octic_decomp.
  have hpieceB : ‖y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
      (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
      (6 : 𝕂)⁻¹ • y ^ 6 + (7 : 𝕂)⁻¹ • y ^ 7 -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
      bch_septic_term 𝕂 a b‖ ≤ 217 * s ^ 8 := by
    rw [pieceB_octic_decomp 𝕂 a b]
    -- For S₁', convert from QPI form to SPI form for T₃ in corr₁, then apply H1.
    have hI₁_eq_form :
        (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b =
        y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
          (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b := by
      rw [← hH1]
    have hT3_QPI_eq_SPI :
        (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b) =
        (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 := by abel
    have hS1_le :
        ‖(y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
            (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b) -
          ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
            (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
            (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
            (2 : 𝕂)⁻¹ • (z * ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
                (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) +
              ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
                (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) * z) -
            (2 : 𝕂)⁻¹ • T₂ ^ 2) -
          (2 : 𝕂)⁻¹ • W5 -
          (2 : 𝕂)⁻¹ • W6 -
          (2 : 𝕂)⁻¹ • W7‖ ≤ 25 * s ^ 8 := by
      rw [hT3_QPI_eq_SPI]
      rw [← hI₁_eq_form]
      exact hI1_minus_corrs_le
    -- S₂' = ⅓·(y³-z³ - y3_5 - y3_6 - y3_7), bound via I2_octic_residual.
    have hyzP : y = z + P := by rw [hP_def]; abel
    have hzeq : z = y - P := by rw [hP_def]; abel
    -- I2 octic inputs: K_PmT5=6, K_P2'=16, K_PzP'=16, K_P3'=105.
    have hP2_etc_le : ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
        T₂ * T₄ - T₃ * T₃ - T₄ * T₂‖ ≤ 16 * s ^ 7 := by
      exact norm_P2_etc_octic_le P T₂ T₃ T₄ hs_nn hs_small_le hT₂_le hT₃_le
        hT₄_le hPmT₂mT₃mT₄
    have hPzP_etc_le : ‖P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
        T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂‖ ≤ 16 * s ^ 8 :=
      norm_PzP_etc_octic_le z P T₂ T₃ T₄ hs_nn hs_small_le hz_le hT₂_le hT₃_le
        hT₄_le hPmT₂mT₃mT₄
    have hP3_le : ‖P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2‖ ≤
        105 * s ^ 8 :=
      norm_P3_etc_octic_le P T₂ T₃ hs_nn hs_small_le hP_le_s2 hT₂_le hT₃_le
        hPmT₂ hPmT₂mT₃
    have hS2_inner_eq :
        y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3) -
          (z * z * T₅ + z * T₂ * T₄ + z * T₃ * T₃ + z * T₄ * T₂ + z * T₅ * z +
            T₂ * z * T₄ + T₂ * T₂ * T₃ + T₂ * T₃ * T₂ + T₂ * T₄ * z +
            T₃ * z * T₃ + T₃ * T₂ * T₂ + T₃ * T₃ * z +
            T₄ * z * T₂ + T₄ * T₂ * z + T₅ * z * z) =
        z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) + z * (P - T₂ - T₃ - T₄ - T₅) * z +
          (P - T₂ - T₃ - T₄ - T₅) * z ^ 2 +
        z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
             T₂ * T₄ - T₃ * T₃ - T₄ * T₂) +
        (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
             T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂) +
        (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
             T₂ * T₄ - T₃ * T₃ - T₄ * T₂) * z +
        (P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2) := by
      rw [hyzP]; noncomm_ring
    have hS2_inner_le_octic :
        ‖z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) + z * (P - T₂ - T₃ - T₄ - T₅) * z +
          (P - T₂ - T₃ - T₄ - T₅) * z ^ 2 +
          z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
               T₂ * T₄ - T₃ * T₃ - T₄ * T₂) +
          (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
               T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂) +
          (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
               T₂ * T₄ - T₃ * T₃ - T₄ * T₂) * z +
          (P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2)‖ ≤
        171 * s ^ 8 := by
      have h := norm_I2_octic_residual_RHS_le z P T₂ T₃ T₄ T₅ hs_nn
        (by norm_num : (0:ℝ) ≤ 6) (by norm_num : (0:ℝ) ≤ 16)
        (by norm_num : (0:ℝ) ≤ 16) (by norm_num : (0:ℝ) ≤ 105)
        hz_le hPmT₂mT₃mT₄mT₅ hP2_etc_le hPzP_etc_le hP3_le
      have h_eq : (3 * 6 + 2 * 16 + 16 + 105 : ℝ) * s ^ 8 = 171 * s ^ 8 := by ring
      linarith
    have hS2_inner_full :
        ‖y ^ 3 - z ^ 3 - (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3) -
          (z * z * T₅ + z * T₂ * T₄ + z * T₃ * T₃ + z * T₄ * T₂ + z * T₅ * z +
            T₂ * z * T₄ + T₂ * T₂ * T₃ + T₂ * T₃ * T₂ + T₂ * T₄ * z +
            T₃ * z * T₃ + T₃ * T₂ * T₂ + T₃ * T₃ * z +
            T₄ * z * T₂ + T₄ * T₂ * z + T₅ * z * z)‖ ≤ 171 * s ^ 8 := by
      rw [hS2_inner_eq]; exact hS2_inner_le_octic
    have hS2_smul_eq :
        (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
          z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
        (3 : 𝕂)⁻¹ • (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
          z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
          T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
          T₂ ^ 3) -
        (3 : 𝕂)⁻¹ • (z * z * T₅ + z * T₂ * T₄ + z * T₃ * T₃ + z * T₄ * T₂ +
          z * T₅ * z +
          T₂ * z * T₄ + T₂ * T₂ * T₃ + T₂ * T₃ * T₂ + T₂ * T₄ * z +
          T₃ * z * T₃ + T₃ * T₂ * T₂ + T₃ * T₃ * z +
          T₄ * z * T₂ + T₄ * T₂ * z + T₅ * z * z) =
        (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3 -
          (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3) -
          (z * z * T₅ + z * T₂ * T₄ + z * T₃ * T₃ + z * T₄ * T₂ + z * T₅ * z +
            T₂ * z * T₄ + T₂ * T₂ * T₃ + T₂ * T₃ * T₂ + T₂ * T₄ * z +
            T₃ * z * T₃ + T₃ * T₂ * T₂ + T₃ * T₃ * z +
            T₄ * z * T₂ + T₄ * T₂ * z + T₅ * z * z)) := by
      simp only [smul_sub]
    have hS2_le :
        ‖(3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
            z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
          (3 : 𝕂)⁻¹ • (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
            z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
            T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
            T₂ ^ 3) -
          (3 : 𝕂)⁻¹ • (z * z * T₅ + z * T₂ * T₄ + z * T₃ * T₃ + z * T₄ * T₂ +
            z * T₅ * z +
            T₂ * z * T₄ + T₂ * T₂ * T₃ + T₂ * T₃ * T₂ + T₂ * T₄ * z +
            T₃ * z * T₃ + T₃ * T₂ * T₂ + T₃ * T₃ * z +
            T₄ * z * T₂ + T₄ * T₂ * z + T₅ * z * z)‖ ≤ 57 * s ^ 8 := by
      rw [hS2_smul_eq]
      have h_s8nn : (0 : ℝ) ≤ s ^ 8 := pow_nonneg hs_nn 8
      calc _ ≤ ‖(3 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
        _ ≤ (3 : ℝ)⁻¹ * (171 * s ^ 8) := by
            rw [h3eq]; exact mul_le_mul_of_nonneg_left hS2_inner_full (by norm_num)
        _ = ((3 : ℝ)⁻¹ * 171) * s ^ 8 := by ring
        _ = 57 * s ^ 8 := by ring
    -- S₃' = ¼·(y⁴-z⁴-y4_5-y4_6-y4_7) inner ≤ 285·s⁸, after ¼: ≤ 72·s⁸.
    have hP2_T22 : ‖P ^ 2 - T₂ ^ 2‖ ≤ 10 * s ^ 5 :=
      norm_P2_sub_T22_le P T₂ hs_nn hP_le_s2 hT₂_le hPmT₂
    have hP2_etc_deg6 : ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ ≤ 15 * s ^ 6 := by
      have h := norm_T22_sub_P2_etc_le P T₂ T₃ hs_nn hP_le_s2 hT₂_le hT₃_le hPmT₂ hPmT₂mT₃
      have h_eq : P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ =
          -(T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) := by noncomm_ring
      rw [h_eq, norm_neg]; exact h
    have hP3_T23 : ‖P ^ 3 - T₂ ^ 3‖ ≤ 15 * s ^ 7 :=
      norm_P3_sub_T23_le P T₂ hs_nn hP_le_s2 hT₂_le hPmT₂
    have hS3_inner_le : ‖y ^ 4 - (y - P) ^ 4 -
        ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
         (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) -
        ((y - P) ^ 3 * T₃ + (y - P) ^ 2 * T₃ * (y - P) +
          (y - P) * T₃ * (y - P) ^ 2 + T₃ * (y - P) ^ 3 +
          (y - P) ^ 2 * T₂ ^ 2 + (y - P) * T₂ * (y - P) * T₂ +
          (y - P) * T₂ ^ 2 * (y - P) +
          T₂ * (y - P) ^ 2 * T₂ + T₂ * (y - P) * T₂ * (y - P) +
          T₂ ^ 2 * (y - P) ^ 2) -
        ((y - P) * (y - P) * (y - P) * T₄ +
          (y - P) * (y - P) * T₂ * T₃ +
          (y - P) * (y - P) * T₃ * T₂ +
          (y - P) * (y - P) * T₄ * (y - P) +
          (y - P) * T₂ * (y - P) * T₃ +
          (y - P) * T₂ * T₂ * T₂ +
          (y - P) * T₂ * T₃ * (y - P) +
          (y - P) * T₃ * (y - P) * T₂ +
          (y - P) * T₃ * T₂ * (y - P) +
          (y - P) * T₄ * (y - P) * (y - P) +
          T₂ * (y - P) * (y - P) * T₃ +
          T₂ * (y - P) * T₂ * T₂ +
          T₂ * (y - P) * T₃ * (y - P) +
          T₂ * T₂ * (y - P) * T₂ +
          T₂ * T₂ * T₂ * (y - P) +
          T₂ * T₃ * (y - P) * (y - P) +
          T₃ * (y - P) * (y - P) * T₂ +
          T₃ * (y - P) * T₂ * (y - P) +
          T₃ * T₂ * (y - P) * (y - P) +
          T₄ * (y - P) * (y - P) * (y - P))‖ ≤ 285 * s ^ 8 := by
      have h := norm_y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_le y P T₂ T₃ T₄ hs_nn
        hs_le_one (by rw [← hzeq]; exact hz_le) hP_le_s2 hT₂_le hPmT₂ hPmT₂mT₃
        hPmT₂mT₃mT₄ hP2_T22 hP2_etc_deg6 hP3_T23
      exact h
    -- Show the inner equals z^3·T₂ + ... = (y-P)^3·T₂ + ... etc. (just use rewrite z = y - P)
    have hS3_inner_le' : ‖y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) -
        (z ^ 3 * T₃ + z ^ 2 * T₃ * z + z * T₃ * z ^ 2 + T₃ * z ^ 3 +
         z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
         T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2) -
        (z * z * z * T₄ +
          z * z * T₂ * T₃ +
          z * z * T₃ * T₂ +
          z * z * T₄ * z +
          z * T₂ * z * T₃ +
          z * T₂ * T₂ * T₂ +
          z * T₂ * T₃ * z +
          z * T₃ * z * T₂ +
          z * T₃ * T₂ * z +
          z * T₄ * z * z +
          T₂ * z * z * T₃ +
          T₂ * z * T₂ * T₂ +
          T₂ * z * T₃ * z +
          T₂ * T₂ * z * T₂ +
          T₂ * T₂ * T₂ * z +
          T₂ * T₃ * z * z +
          T₃ * z * z * T₂ +
          T₃ * z * T₂ * z +
          T₃ * T₂ * z * z +
          T₄ * z * z * z)‖ ≤ 285 * s ^ 8 := by
      rwa [show y - P = z from hzeq.symm] at hS3_inner_le
    have hS3_le : ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) -
        (z ^ 3 * T₃ + z ^ 2 * T₃ * z + z * T₃ * z ^ 2 + T₃ * z ^ 3 +
         z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
         T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2) -
        (z * z * z * T₄ +
          z * z * T₂ * T₃ +
          z * z * T₃ * T₂ +
          z * z * T₄ * z +
          z * T₂ * z * T₃ +
          z * T₂ * T₂ * T₂ +
          z * T₂ * T₃ * z +
          z * T₃ * z * T₂ +
          z * T₃ * T₂ * z +
          z * T₄ * z * z +
          T₂ * z * z * T₃ +
          T₂ * z * T₂ * T₂ +
          T₂ * z * T₃ * z +
          T₂ * T₂ * z * T₂ +
          T₂ * T₂ * T₂ * z +
          T₂ * T₃ * z * z +
          T₃ * z * z * T₂ +
          T₃ * z * T₂ * z +
          T₃ * T₂ * z * z +
          T₄ * z * z * z))‖ ≤ 72 * s ^ 8 := by
      have h_s8nn : (0 : ℝ) ≤ s ^ 8 := pow_nonneg hs_nn 8
      have h_const : (4 : ℝ)⁻¹ * 285 ≤ 72 := by norm_num
      calc _ ≤ ‖(4 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
        _ ≤ (4 : ℝ)⁻¹ * (285 * s ^ 8) := by
            rw [h4eq]; exact mul_le_mul_of_nonneg_left hS3_inner_le' (by norm_num)
        _ = ((4 : ℝ)⁻¹ * 285) * s ^ 8 := by ring
        _ ≤ 72 * s ^ 8 := mul_le_mul_of_nonneg_right h_const h_s8nn
    -- S₄' = ⅕·(y⁵-z⁵-y5_6-y5_7) inner ≤ 141·s⁸, after ⅕: ≤ 29·s⁸.
    have hS4_inner_le_octic : ‖y ^ 5 - (y - P) ^ 5 -
        ((y - P) ^ 4 * T₂ + (y - P) ^ 3 * T₂ * (y - P) +
         (y - P) ^ 2 * T₂ * (y - P) ^ 2 + (y - P) * T₂ * (y - P) ^ 3 +
         T₂ * (y - P) ^ 4) -
        ((y - P) * (y - P) * (y - P) * (y - P) * T₃ +
          (y - P) * (y - P) * (y - P) * T₃ * (y - P) +
          (y - P) * (y - P) * T₃ * (y - P) * (y - P) +
          (y - P) * T₃ * (y - P) * (y - P) * (y - P) +
          T₃ * (y - P) * (y - P) * (y - P) * (y - P) +
          (y - P) * (y - P) * (y - P) * T₂ * T₂ +
          (y - P) * (y - P) * T₂ * (y - P) * T₂ +
          (y - P) * (y - P) * T₂ * T₂ * (y - P) +
          (y - P) * T₂ * (y - P) * (y - P) * T₂ +
          (y - P) * T₂ * (y - P) * T₂ * (y - P) +
          (y - P) * T₂ * T₂ * (y - P) * (y - P) +
          T₂ * (y - P) * (y - P) * (y - P) * T₂ +
          T₂ * (y - P) * (y - P) * T₂ * (y - P) +
          T₂ * (y - P) * T₂ * (y - P) * (y - P) +
          T₂ * T₂ * (y - P) * (y - P) * (y - P))‖ ≤ 141 * s ^ 8 := by
      exact norm_y5_sub_z5_sub_y5_6_sub_y5_7_le y P T₂ T₃ hs_nn hs_le_one
        hy_le2 (by rw [← hzeq]; exact hz_le) hP_le_s2 hT₂_le hPmT₂ hPmT₂mT₃
        hP2_T22
    have hS4_inner_le' : ‖y ^ 5 - z ^ 5 -
        (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
          z * T₂ * z ^ 3 + T₂ * z ^ 4) -
        (z * z * z * z * T₃ +
          z * z * z * T₂ * T₂ +
          z * z * z * T₃ * z +
          z * z * T₂ * z * T₂ +
          z * z * T₂ * T₂ * z +
          z * z * T₃ * z * z +
          z * T₂ * z * z * T₂ +
          z * T₂ * z * T₂ * z +
          z * T₂ * T₂ * z * z +
          z * T₃ * z * z * z +
          T₂ * z * z * z * T₂ +
          T₂ * z * z * T₂ * z +
          T₂ * z * T₂ * z * z +
          T₂ * T₂ * z * z * z +
          T₃ * z * z * z * z)‖ ≤ 141 * s ^ 8 := by
      rw [show y - P = z from hzeq.symm] at hS4_inner_le_octic
      -- Lemma's order differs from pieceB's order — bridge via abel.
      convert hS4_inner_le_octic using 2
      abel
    have hS4_le : ‖(5 : 𝕂)⁻¹ • (y ^ 5 - z ^ 5 -
        (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
          z * T₂ * z ^ 3 + T₂ * z ^ 4) -
        (z * z * z * z * T₃ +
          z * z * z * T₂ * T₂ +
          z * z * z * T₃ * z +
          z * z * T₂ * z * T₂ +
          z * z * T₂ * T₂ * z +
          z * z * T₃ * z * z +
          z * T₂ * z * z * T₂ +
          z * T₂ * z * T₂ * z +
          z * T₂ * T₂ * z * z +
          z * T₃ * z * z * z +
          T₂ * z * z * z * T₂ +
          T₂ * z * z * T₂ * z +
          T₂ * z * T₂ * z * z +
          T₂ * T₂ * z * z * z +
          T₃ * z * z * z * z))‖ ≤ 29 * s ^ 8 := by
      have h_s8nn : (0 : ℝ) ≤ s ^ 8 := pow_nonneg hs_nn 8
      have h_const : (5 : ℝ)⁻¹ * 141 ≤ 29 := by norm_num
      calc _ ≤ ‖(5 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
        _ ≤ (5 : ℝ)⁻¹ * (141 * s ^ 8) := by
            rw [h5eq]; exact mul_le_mul_of_nonneg_left hS4_inner_le' (by norm_num)
        _ = ((5 : ℝ)⁻¹ * 141) * s ^ 8 := by ring
        _ ≤ 29 * s ^ 8 := mul_le_mul_of_nonneg_right h_const h_s8nn
    -- S₅' = ⅙·(y⁶-z⁶-y6_7) inner ≤ 87·s⁸, after ⅙: ≤ 15·s⁸.
    have hS5_inner_le_octic : ‖y ^ 6 - (y - P) ^ 6 -
        ((y - P) ^ 5 * T₂ + (y - P) ^ 4 * T₂ * (y - P) +
         (y - P) ^ 3 * T₂ * (y - P) ^ 2 + (y - P) ^ 2 * T₂ * (y - P) ^ 3 +
         (y - P) * T₂ * (y - P) ^ 4 + T₂ * (y - P) ^ 5)‖ ≤ 87 * s ^ 8 := by
      exact norm_y6_sub_z6_sub_y6_7_le y P T₂ hs_nn hy_le2
        (by rw [← hzeq]; exact hz_le) hP_le_s2 hPmT₂
    have hS5_inner_le' : ‖y ^ 6 - z ^ 6 -
        (z * z * z * z * z * T₂ +
          z * z * z * z * T₂ * z +
          z * z * z * T₂ * z * z +
          z * z * T₂ * z * z * z +
          z * T₂ * z * z * z * z +
          T₂ * z * z * z * z * z)‖ ≤ 87 * s ^ 8 := by
      rw [show y - P = z from hzeq.symm] at hS5_inner_le_octic
      -- Lemma uses z^k, pieceB uses z*z*…*z — bridge via noncomm_ring.
      convert hS5_inner_le_octic using 2
      noncomm_ring
    have hS5_le : ‖(6 : 𝕂)⁻¹ • (y ^ 6 - z ^ 6 -
        (z * z * z * z * z * T₂ +
          z * z * z * z * T₂ * z +
          z * z * z * T₂ * z * z +
          z * z * T₂ * z * z * z +
          z * T₂ * z * z * z * z +
          T₂ * z * z * z * z * z))‖ ≤ 15 * s ^ 8 := by
      have h_s8nn : (0 : ℝ) ≤ s ^ 8 := pow_nonneg hs_nn 8
      have h_const : (6 : ℝ)⁻¹ * 87 ≤ 15 := by norm_num
      calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * _ := norm_smul_le _ _
        _ ≤ (6 : ℝ)⁻¹ * (87 * s ^ 8) := by
            rw [h6eq]; exact mul_le_mul_of_nonneg_left hS5_inner_le' (by norm_num)
        _ = ((6 : ℝ)⁻¹ * 87) * s ^ 8 := by ring
        _ ≤ 15 * s ^ 8 := mul_le_mul_of_nonneg_right h_const h_s8nn
    -- S₆ = ⅐·(y⁷-z⁷) inner ≤ 127·s⁸, after ⅐: ≤ 19·s⁸.
    have hS6_inner_le : ‖y ^ 7 - z ^ 7‖ ≤ 127 * s ^ 8 := by
      have h := norm_pow7_sub_zpow7_le y P hs_nn hy_le2
        (by rw [← hzeq]; exact hz_le) hP_le_s2
      rwa [show y - P = z from hzeq.symm] at h
    have hS6_le : ‖(7 : 𝕂)⁻¹ • (y ^ 7 - z ^ 7)‖ ≤ 19 * s ^ 8 := by
      have h_s8nn : (0 : ℝ) ≤ s ^ 8 := pow_nonneg hs_nn 8
      have h_const : (7 : ℝ)⁻¹ * 127 ≤ 19 := by norm_num
      calc _ ≤ ‖(7 : 𝕂)⁻¹‖ * ‖y ^ 7 - z ^ 7‖ := norm_smul_le _ _
        _ ≤ (7 : ℝ)⁻¹ * (127 * s ^ 8) := by
            rw [h7eq]; exact mul_le_mul_of_nonneg_left hS6_inner_le (by norm_num)
        _ = ((7 : ℝ)⁻¹ * 127) * s ^ 8 := by ring
        _ ≤ 19 * s ^ 8 := mul_le_mul_of_nonneg_right h_const h_s8nn
    -- Triangle inequality on the 6-piece sum: S₁'+S₂'-S₃'+S₄'-S₅'+S₆.
    -- Unfold set-bound vars in hS_i_le to match the goal's unfolded form.
    simp only [hy_def, hz_def, hT₂_def, hT₃_def, hT₄_def, hT₅_def, hT₆_def,
      hW5_def, hW6_def, hW7_def, hT_extra_def,
      hT_extra2_def] at hS1_le hS2_le hS3_le hS4_le hS5_le hS6_le
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl)
      le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl)
      le_rfl) le_rfl) le_rfl).trans ?_
    have h_sum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hS1_le
      hS2_le) hS3_le) hS4_le) hS5_le) hS6_le
    have h_eq : (25 : ℝ) * s ^ 8 + 57 * s ^ 8 + 72 * s ^ 8 + 29 * s ^ 8 + 15 * s ^ 8 +
        19 * s ^ 8 = 217 * s ^ 8 := by ring
    linarith
  -- COMBINE pieceA + pieceB''''.
  calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
          (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4 - (5 : 𝕂)⁻¹ • y ^ 5 +
          (6 : 𝕂)⁻¹ • y ^ 6 - (7 : 𝕂)⁻¹ • y ^ 7‖ +
        ‖y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
          (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
          (6 : 𝕂)⁻¹ • y ^ 6 + (7 : 𝕂)⁻¹ • y ^ 7 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
          bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
          bch_septic_term 𝕂 a b‖ := norm_add_le _ _
    _ ≤ 3 * s ^ 8 / (2 - Real.exp s) + 217 * s ^ 8 := by linarith [hpieceA, hpieceB]
    _ ≤ 3 * s ^ 8 / (2 - Real.exp s) +
        217 * s ^ 8 / (2 - Real.exp s) := by
        gcongr
        rw [le_div_iff₀ hdenom]
        nlinarith [pow_nonneg hs_nn 8]
    _ = (3 * s ^ 8 + 217 * s ^ 8) / (2 - Real.exp s) := (add_div _ _ _).symm
    _ ≤ 1000 * s ^ 8 / (2 - Real.exp s) := by
        apply div_le_div_of_nonneg_right _ hdenom.le
        nlinarith [pow_nonneg hs_nn 8]

include 𝕂 in
/-- **Order-8 BCH remainder bound** (public theorem):

  `‖bch(a, b) - (a+b) - ½[a,b] - C₃ - C₄ - bqt - bch_sextic_term - bch_septic_term‖ ≤
   10000110 · s⁸ / (2 - exp(s))`  for `s < log 2`.

This is the deg-8+ remainder of the BCH series after subtracting the
through-deg-7 expansion. It's the order-8 analog of `norm_bch_septic_remainder_le`
and the foundation for extending the cubic template to discharge the parent
deg-9 stepping-stone `symmetric_bch_septic_sub_poly_axiom` (the deg-9 analog
of T2-F7e).

Proof: case split on `s ≥ 1/10` (uses `norm_bch_octic_remainder_large_s_le`,
fully proved) vs. `s < 1/10` (uses `norm_bch_octic_remainder_small_s_axiom`,
stepping-stone awaiting discharge; analog of session-18 septic
small-s axiom → session-19 discharge). -/
theorem norm_bch_octic_remainder_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
      bch_septic_term 𝕂 a b‖ ≤
      10000110 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  by_cases hs : 1 / 10 ≤ ‖a‖ + ‖b‖
  · -- Large-s: ‖LHS‖ ≤ 10000110·s⁸/(2-exp(s)) directly.
    exact norm_bch_octic_remainder_large_s_le (𝕂 := 𝕂) a b hab hs
  · -- Small-s: ‖LHS‖ ≤ 1000·s⁸/(2-exp(s)) ≤ 10000110·s⁸/(2-exp(s)).
    push_neg at hs
    have h_small := norm_bch_octic_remainder_small_s_le (𝕂 := 𝕂) a b hab hs
    have hexp_lt : Real.exp (‖a‖ + ‖b‖) < 2 := by
      calc Real.exp (‖a‖ + ‖b‖) < Real.exp (Real.log 2) := Real.exp_strictMono hab
        _ = 2 := Real.exp_log (by norm_num)
    have hdenom : 0 < 2 - Real.exp (‖a‖ + ‖b‖) := by linarith
    have hs_nn : 0 ≤ ‖a‖ + ‖b‖ := by positivity
    calc _ ≤ 1000 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) := h_small
      _ ≤ 10000110 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
          apply div_le_div_of_nonneg_right _ hdenom.le
          have : 1000 * (‖a‖ + ‖b‖) ^ 8 ≤ 10000110 * (‖a‖ + ‖b‖) ^ 8 := by
            nlinarith [pow_nonneg hs_nn 8]
          linarith

/-- The cubic coefficient of the *symmetric* BCH expansion.

For `Z(a,b) = bch(bch(a/2, b), a/2)`, this is the degree-3 part:
`Z = (a+b) + symmetric_bch_cubic a b + O(s⁵)`.

The quadratic commutator `[a/2,b]` cancels by symmetry (proved in H2). -/
noncomputable def symmetric_bch_cubic (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] (a b : 𝔸) : 𝔸 :=
  bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) - (a + b)

include 𝕂 in
/-- The symmetric BCH cubic coefficient satisfies ‖E₃(a,b)‖ ≤ 300·s³. -/
theorem norm_symmetric_bch_cubic_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 a b‖ ≤ 300 * (‖a‖ + ‖b‖) ^ 3 :=
  norm_symmetric_bch_sub_add_le (𝕂 := 𝕂) a b hab

/-! ### Oddness of symmetric BCH -/

include 𝕂 in
/-- The triple product `exp(a/2)·exp(b)·exp(a/2)` equals `exp(bch(bch(a/2,b),a/2))`. -/
theorem exp_symmetric_bch (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    exp (bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a)) =
    exp ((2 : 𝕂)⁻¹ • a) * exp b * exp ((2 : 𝕂)⁻¹ • a) := by
  set a' := (2 : 𝕂)⁻¹ • a
  set s := ‖a‖ + ‖b‖
  -- Norm setup: ‖a'‖ ≤ ‖a‖/2
  have h_half : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha' : ‖a'‖ ≤ ‖a‖ / 2 := by
    calc ‖a'‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half]; ring
  have hln2 : (1 : ℝ) / 4 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    linarith [real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1:ℝ)/4 < 5/6)]
  -- s₁ = ‖a'‖+‖b‖ < ln 2 for first BCH
  have hs₁ : ‖a'‖ + ‖b‖ < Real.log 2 := by linarith [norm_nonneg a]
  -- First BCH: exp(bch(a',b)) = exp(a')*exp(b)
  have h1 : exp (bch (𝕂 := 𝕂) a' b) = exp a' * exp b := exp_bch (𝕂 := 𝕂) a' b hs₁
  -- s₂ = ‖bch(a',b)‖+‖a'‖ < ln 2 for second BCH
  set z := bch (𝕂 := 𝕂) a' b
  have hδ_le : ‖z - (a' + b)‖ ≤ 3 * (‖a'‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a'‖ + ‖b‖)) :=
    norm_bch_sub_add_le (𝕂 := 𝕂) a' b hs₁
  have hz_le : ‖z‖ ≤ ‖a'‖ + ‖b‖ + 3 * (‖a'‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a'‖ + ‖b‖)) := by
    calc ‖z‖ = ‖(z - (a' + b)) + (a' + b)‖ := by congr 1; abel
      _ ≤ ‖z - (a' + b)‖ + ‖a' + b‖ := norm_add_le _ _
      _ ≤ 3 * (‖a'‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a'‖ + ‖b‖)) + (‖a'‖ + ‖b‖) :=
          add_le_add hδ_le (norm_add_le a' b)
      _ = _ := by ring
  have hs₂ : ‖z‖ + ‖a'‖ < Real.log 2 := by
    have hs₁_nn : 0 ≤ ‖a'‖ + ‖b‖ := by positivity
    have hs₁_lt : ‖a'‖ + ‖b‖ < 1 / 4 := by linarith [norm_nonneg a]
    have hexp_le : Real.exp (‖a'‖ + ‖b‖) ≤ 1 + (‖a'‖ + ‖b‖) + (‖a'‖ + ‖b‖) ^ 2 := by
      nlinarith [real_exp_third_order_le_cube hs₁_nn (by linarith : ‖a'‖ + ‖b‖ < 5/6)]
    have hdenom : (11 : ℝ) / 16 ≤ 2 - Real.exp (‖a'‖ + ‖b‖) := by nlinarith
    -- ‖z‖+‖a'‖ ≤ (2‖a'‖+‖b‖) + quad ≤ s + 3/11 < 1/4+3/11 = 23/44 < 6/11 < ln 2
    have h2a'b_le : 2 * ‖a'‖ + ‖b‖ ≤ s := by linarith
    have hquad_bound : 3 * (‖a'‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a'‖ + ‖b‖)) ≤ 3 / 11 := by
      rw [div_le_div_iff₀ (by linarith : 0 < 2 - Real.exp (‖a'‖ + ‖b‖)) (by norm_num : (0:ℝ) < 11)]
      nlinarith [sq_nonneg (‖a'‖ + ‖b‖), norm_nonneg a', norm_nonneg b,
                 sq_nonneg (1/4 - (‖a'‖ + ‖b‖))]
    have hza : ‖z‖ + ‖a'‖ ≤ s + 3 / 11 := by linarith [hz_le]
    -- 23/44 < 6/11 < ln 2
    have hln2_611 : (6 : ℝ) / 11 < Real.log 2 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
      have := real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 6/11)
        (by norm_num : (6:ℝ)/11 < 5/6)
      nlinarith
    linarith
  -- Second BCH: exp(bch(z,a')) = exp(z)*exp(a')
  have h2 : exp (bch (𝕂 := 𝕂) z a') = exp z * exp a' := exp_bch (𝕂 := 𝕂) z a' hs₂
  rw [h2, h1, mul_assoc]

set_option maxHeartbeats 1600000 in
include 𝕂 in
/-- The symmetric BCH is an odd function: `Z(a,b) + Z(-a,-b) = 0` where
`Z(a,b) = bch(bch(a/2,b),a/2)`. -/
theorem symmetric_bch_add_neg (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) +
    bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • (-a)) (-b)) ((2 : 𝕂)⁻¹ • (-a)) = 0 := by
  -- Chain-of-neighborhoods argument, following logOnePlus_exp_sub_one.
  set s := ‖a‖ + ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  set instℝ := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℝ 𝔸 := instℝ
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Define h(t) = Z(ta,tb) + Z(-ta,-tb)
  -- Use -((2:𝕂)⁻¹ • (t•a)) instead of (2:𝕂)⁻¹ • (-(t•a)) for cleaner unfolding
  set h : ℝ → 𝔸 := fun t =>
    bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • (t • a)) (t • b)) ((2 : 𝕂)⁻¹ • (t • a)) +
    bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) (-((2 : 𝕂)⁻¹ • (t • a))) (-(t • b)))
      (-((2 : 𝕂)⁻¹ • (t • a)))
  suffices h1 : h 1 = 0 by
    -- h 1 has -((2:𝕂)⁻¹ • a) while goal has (2:𝕂)⁻¹ • (-a); convert via smul_neg
    simp only [smul_neg]
    simpa [h] using h1
  -- Auxiliary constants
  have hln2 : (1 : ℝ) / 4 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    linarith [real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1:ℝ)/4 < 5/6)]
  have h_half : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hnorm_t : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖t • a‖ + ‖t • b‖ ≤ s := by
    intro t ht0 ht1
    calc ‖t • a‖ + ‖t • b‖ ≤ |t| * ‖a‖ + |t| * ‖b‖ := by
          gcongr <;> exact norm_smul_le t _
      _ = |t| * s := by ring
      _ ≤ 1 * s := by gcongr; exact abs_le.mpr ⟨by linarith, ht1⟩
      _ = s := one_mul s
  -- Step 1: h(0) = 0
  have h0 : h 0 = 0 := by
    simp only [h, zero_smul, smul_zero, neg_zero]
    have : bch (𝕂 := 𝕂) 0 0 = (0 : 𝔸) := by
      unfold bch; simp [exp_zero, mul_one, logOnePlus, logSeriesTerm, tsum_zero]
    simp [this]
  -- Step 2: exp(h(t)) = 1 for t ∈ [0,1]
  have hexp_ht : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → exp (h t) = 1 := by
    intro t ht0 ht1
    set ta := t • a; set tb := t • b
    have hts : ‖ta‖ + ‖tb‖ < 1 / 4 := lt_of_le_of_lt (hnorm_t t ht0 ht1) hab
    have hts_neg : ‖-ta‖ + ‖-tb‖ < 1 / 4 := by rwa [norm_neg, norm_neg]
    set a₂ := (2 : 𝕂)⁻¹ • ta
    -- exp of symmetric bch
    have hexpZ := exp_symmetric_bch (𝕂 := 𝕂) ta tb hts
    have hexpZ_neg := exp_symmetric_bch (𝕂 := 𝕂) (-ta) (-tb) hts_neg
    rw [smul_neg] at hexpZ_neg
    set Z := bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) a₂ tb) a₂
    set Z_neg := bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) (-a₂) (-tb)) (-a₂)
    -- Triple product: exp(Z)*exp(Z_neg) = 1 and exp(Z_neg)*exp(Z) = 1
    have haa : exp a₂ * exp (-a₂) = 1 := by
      rw [← exp_add_of_commute (Commute.neg_right (Commute.refl a₂)), add_neg_cancel, exp_zero]
    have hbb : exp tb * exp (-tb) = 1 := by
      rw [← exp_add_of_commute (Commute.neg_right (Commute.refl tb)), add_neg_cancel, exp_zero]
    have haa' : exp (-a₂) * exp a₂ = 1 := by
      rw [← exp_add_of_commute (Commute.neg_left (Commute.refl a₂)), neg_add_cancel, exp_zero]
    have hbb' : exp (-tb) * exp tb = 1 := by
      rw [← exp_add_of_commute (Commute.neg_left (Commute.refl tb)), neg_add_cancel, exp_zero]
    have hprod : exp Z * exp Z_neg = 1 := by
      rw [hexpZ, hexpZ_neg]
      calc exp a₂ * exp tb * exp a₂ * (exp (-a₂) * exp (-tb) * exp (-a₂))
          = exp a₂ * exp tb * (exp a₂ * exp (-a₂)) * exp (-tb) * exp (-a₂) := by noncomm_ring
        _ = exp a₂ * exp tb * 1 * exp (-tb) * exp (-a₂) := by rw [haa]
        _ = exp a₂ * (exp tb * exp (-tb)) * exp (-a₂) := by noncomm_ring
        _ = exp a₂ * 1 * exp (-a₂) := by rw [hbb]
        _ = exp a₂ * exp (-a₂) := by noncomm_ring
        _ = 1 := haa
    have hprod' : exp Z_neg * exp Z = 1 := by
      rw [hexpZ, hexpZ_neg]
      calc exp (-a₂) * exp (-tb) * exp (-a₂) * (exp a₂ * exp tb * exp a₂)
          = exp (-a₂) * exp (-tb) * (exp (-a₂) * exp a₂) * exp tb * exp a₂ := by noncomm_ring
        _ = exp (-a₂) * exp (-tb) * 1 * exp tb * exp a₂ := by rw [haa']
        _ = exp (-a₂) * (exp (-tb) * exp tb) * exp a₂ := by noncomm_ring
        _ = exp (-a₂) * 1 * exp a₂ := by rw [hbb']
        _ = exp (-a₂) * exp a₂ := by noncomm_ring
        _ = 1 := haa'
    -- Units structure for commutativity
    set u : 𝔸ˣ := ⟨exp Z, exp Z_neg, hprod, hprod'⟩
    -- y = exp Z - 1, y_neg = exp Z_neg - 1
    -- Commutativity chain: y ↔ y_neg ↔ logOnePlus(y) ↔ logOnePlus(y_neg)
    have hcomm_y_yneg : Commute (exp Z - 1) (exp Z_neg - 1) :=
      ((show Commute (exp Z - 1) (↑u) from by
        show (exp Z - 1) * exp Z = exp Z * (exp Z - 1); noncomm_ring).units_inv_right
      ).sub_right (Commute.one_right _)
    -- Z = logOnePlus(y) where y = exp(bch(a₂,tb))*exp(a₂)-1
    -- By bch definition, Z = logOnePlus(exp(bch(a₂,tb))*exp(a₂)-1)
    -- And exp(bch(a₂,tb))*exp(a₂)-1 = exp(a₂)*exp(tb)*exp(a₂)-1 = exp Z - 1
    have ha₂_tb : ‖a₂‖ + ‖tb‖ < Real.log 2 := by
      have hta_le : ‖ta‖ + ‖tb‖ ≤ s := hnorm_t t ht0 ht1
      calc ‖a₂‖ + ‖tb‖ ≤ ‖ta‖ / 2 + ‖tb‖ := by
            gcongr; calc ‖a₂‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖ta‖ := norm_smul_le _ _
              _ = ‖ta‖ / 2 := by rw [h_half]; ring
        _ ≤ s := by linarith [norm_nonneg ta]
        _ < 1 / 4 := hab
        _ < Real.log 2 := hln2
    have hexp_inner : exp (bch (𝕂 := 𝕂) a₂ tb) = exp a₂ * exp tb :=
      exp_bch (𝕂 := 𝕂) a₂ tb ha₂_tb
    -- Commutativity of Z and Z_neg via logOnePlus structure
    -- Z = bch(bch(a₂,tb),a₂) = logOnePlus(w) where w = exp(bch(a₂,tb))*exp(a₂)-1
    -- We show w commutes with w_neg, then use commute_logOnePlus_of_commute
    -- w = exp(a₂)*exp(tb)*exp(a₂) - 1 = exp Z - 1 (by hexp_inner and hexpZ)
    -- So Commute w w_neg ↔ Commute (exp Z - 1) (exp Z_neg - 1) = hcomm_y_yneg
    -- Z = logOnePlus(w): by definition of bch, Z is logOnePlus applied to w
    -- We use: commute_logOnePlus_of_commute applied to w and w_neg
    -- Since Z = logOnePlus(w), this gives Commute Z w_neg = Commute Z (exp Z_neg - 1)
    -- Then similarly for Z_neg = logOnePlus(w_neg)
    -- Step A: show w = exp Z - 1 (so commute_logOnePlus_of_commute on w gives commute on Z)
    have hw_eq : exp (bch (𝕂 := 𝕂) a₂ tb) * exp a₂ - 1 = exp Z - 1 := by
      congr 1; rw [hexp_inner]; exact hexpZ.symm
    have ha₂_neg_tb : ‖-a₂‖ + ‖-tb‖ < Real.log 2 := by rw [norm_neg, norm_neg]; exact ha₂_tb
    have hexp_inner_neg : exp (bch (𝕂 := 𝕂) (-a₂) (-tb)) = exp (-a₂) * exp (-tb) :=
      exp_bch (𝕂 := 𝕂) (-a₂) (-tb) ha₂_neg_tb
    have hw_neg_eq : exp (bch (𝕂 := 𝕂) (-a₂) (-tb)) * exp (-a₂) - 1 = exp Z_neg - 1 := by
      congr 1; rw [hexp_inner_neg]; exact hexpZ_neg.symm
    -- Step B: Z = logOnePlus(w), and Commute w (exp Z_neg - 1)
    -- w = exp(bch a₂ tb)*exp a₂ - 1 = exp Z - 1 (by hw_eq)
    -- So Commute w (exp Z_neg - 1) follows from hcomm_y_yneg (after rewriting w)
    -- Z is definitionally logOnePlus(exp(bch(a₂,tb))*exp(a₂)-1), so
    -- commute_logOnePlus_of_commute gives Commute Z (exp Z_neg - 1)
    have hcomm_w_wneg : Commute (exp (bch (𝕂 := 𝕂) a₂ tb) * exp a₂ - 1) (exp Z_neg - 1) := by
      rw [hw_eq]; exact hcomm_y_yneg
    have hcomm_Z_yneg : Commute Z (exp Z_neg - 1) :=
      commute_logOnePlus_of_commute (𝕂 := 𝕂) _ _ hcomm_w_wneg
    -- Step C: Z_neg = logOnePlus(w_neg), and Commute w_neg Z
    have hcomm_wneg_Z : Commute (exp (bch (𝕂 := 𝕂) (-a₂) (-tb)) * exp (-a₂) - 1) Z := by
      rw [hw_neg_eq]; exact hcomm_Z_yneg.symm
    have hcomm_Z_Zneg : Commute Z Z_neg :=
      (commute_logOnePlus_of_commute (𝕂 := 𝕂) _ _ hcomm_wneg_Z).symm
    -- exp(h(t)) = exp(Z + Z_neg) = exp(Z) * exp(Z_neg) = 1
    have hht_eq : h t = Z + Z_neg := rfl
    rw [hht_eq, exp_add_of_commute hcomm_Z_Zneg, hprod]
  -- Step 3: h is continuous on [0, 1]
  have hcont : ContinuousOn h (Set.Icc 0 1) := by
    -- h is a sum; show each summand is continuous
    -- Each bch(x,y) = logOnePlus(exp x * exp y - 1) is logOnePlus of a continuous function
    set ρ := Real.exp s - 1
    have hρ_lt : ρ < 1 := by
      have : Real.exp s < 2 := lt_of_lt_of_eq
        (Real.exp_strictMono (by linarith : s < Real.log 2)) (Real.exp_log (by norm_num))
      linarith
    have hnorm_half_smul : ∀ x : 𝔸, ‖(2 : 𝕂)⁻¹ • x‖ ≤ ‖x‖ / 2 := by
      intro x; calc ‖(2 : 𝕂)⁻¹ • x‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖x‖ := norm_smul_le _ _
        _ = ‖x‖ / 2 := by rw [h_half]; ring
    -- ‖exp f * exp g - 1‖ ≤ exp(‖f‖+‖g‖)-1
    have hprod_le : ∀ (f g : 𝔸), ‖exp f * exp g - 1‖ ≤ Real.exp (‖f‖ + ‖g‖) - 1 := by
      intro f g
      have : exp f * exp g - 1 = (exp f - 1) * exp g + (exp g - 1) := by
        rw [sub_mul, one_mul]; abel
      rw [this]
      calc ‖(exp f - 1) * exp g + (exp g - 1)‖
          ≤ ‖(exp f - 1) * exp g‖ + ‖exp g - 1‖ := norm_add_le _ _
        _ ≤ ‖exp f - 1‖ * ‖exp g‖ + ‖exp g - 1‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ (Real.exp ‖f‖ - 1) * Real.exp ‖g‖ + (Real.exp ‖g‖ - 1) :=
            add_le_add (mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) f)
              (norm_exp_le (𝕂 := 𝕂) g) (norm_nonneg _)
              (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg f))))
              (norm_exp_sub_one_le (𝕂 := 𝕂) g)
        _ = _ := by rw [Real.exp_add]; ring
    -- ‖exp p * exp q * exp p - 1‖ ≤ exp(2‖p‖+‖q‖)-1 ≤ ρ
    have htriple_le : ∀ (p q : 𝔸), ‖p‖ + ‖q‖ + ‖p‖ ≤ s →
        ‖exp p * exp q * exp p - 1‖ ≤ ρ := by
      intro p q hpq
      have hfact : exp p * exp q * exp p - 1 =
        exp p * (exp q * exp p - 1) + (exp p - 1) := by noncomm_ring
      rw [hfact]
      calc ‖exp p * (exp q * exp p - 1) + (exp p - 1)‖
          ≤ ‖exp p * (exp q * exp p - 1)‖ + ‖exp p - 1‖ := norm_add_le _ _
        _ ≤ ‖exp p‖ * ‖exp q * exp p - 1‖ + ‖exp p - 1‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ Real.exp ‖p‖ * (Real.exp (‖q‖ + ‖p‖) - 1) + (Real.exp ‖p‖ - 1) :=
            add_le_add (mul_le_mul (norm_exp_le (𝕂 := 𝕂) p)
              (hprod_le q p) (norm_nonneg _)
              (Real.exp_pos _).le) (norm_exp_sub_one_le (𝕂 := 𝕂) p)
        _ = Real.exp (‖p‖ + ‖q‖ + ‖p‖) - 1 := by
            have : Real.exp (‖p‖ + ‖q‖ + ‖p‖) =
              Real.exp ‖p‖ * Real.exp (‖q‖ + ‖p‖) := by
              rw [show ‖p‖ + ‖q‖ + ‖p‖ = ‖p‖ + (‖q‖ + ‖p‖) from by ring, Real.exp_add]
            rw [this]; ring
        _ ≤ ρ := sub_le_sub_right (Real.exp_le_exp.mpr hpq) 1
    have hcf : Continuous (fun t : ℝ => (2 : 𝕂)⁻¹ • (t • a)) :=
      continuous_const.smul (continuous_id.smul continuous_const)
    have hcg : Continuous (fun t : ℝ => t • b) := continuous_id.smul continuous_const
    have hnorm_fg : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖(2 : 𝕂)⁻¹ • (t • a)‖ + ‖t • b‖ ≤ s := by
      intro t ht; linarith [hnorm_half_smul (t • a), hnorm_t t ht.1 ht.2, norm_nonneg (t • a)]
    have hnorm_triple : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖(2 : 𝕂)⁻¹ • (t • a)‖ + ‖t • b‖ + ‖(2 : 𝕂)⁻¹ • (t • a)‖ ≤ s := by
      intro t ht; linarith [hnorm_half_smul (t • a), hnorm_t t ht.1 ht.2]
    -- Continuity of bch(f(t), g(t)) when ‖f‖+‖g‖ ≤ s on [0,1]
    have hcont_bch : ∀ (f g : ℝ → 𝔸), Continuous f → Continuous g →
        (∀ t ∈ Set.Icc 0 1, ‖f t‖ + ‖g t‖ ≤ s) →
        ContinuousOn (fun t => bch (𝕂 := 𝕂) (f t) (g t)) (Set.Icc 0 1) := by
      intro f g hf hg hfg
      show ContinuousOn (fun t => logOnePlus (𝕂 := 𝕂) (exp (f t) * exp (g t) - 1)) _
      exact (continuousOn_logOnePlus (𝕂 := 𝕂) hρ_lt).comp
        (((NormedSpace.exp_continuous.comp hf).mul
          (NormedSpace.exp_continuous.comp hg)).sub continuous_const |>.continuousOn)
        (fun t ht => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (hprod_le _ _).trans (sub_le_sub_right (Real.exp_le_exp.mpr (hfg t ht)) 1))
    have hcont_inner_pos := hcont_bch _ _ hcf hcg hnorm_fg
    have hcont_inner_neg := hcont_bch _ _ hcf.neg hcg.neg
      (fun t ht => by rw [norm_neg, norm_neg]; exact hnorm_fg t ht)
    -- h = outer_bch_pos + outer_bch_neg
    -- outer_bch(t) = logOnePlus(exp(inner_bch(t))*exp(a₂(t))-1)
    -- inner map continuous, outer maps into closedBall via triple product bound
    apply ContinuousOn.add
    · show ContinuousOn (fun t => logOnePlus (𝕂 := 𝕂)
        (exp (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • (t • a)) (t • b)) *
          exp ((2 : 𝕂)⁻¹ • (t • a)) - 1)) (Set.Icc 0 1)
      exact (continuousOn_logOnePlus (𝕂 := 𝕂) hρ_lt).comp
        ((NormedSpace.exp_continuous.comp_continuousOn' hcont_inner_pos
          |>.mul (NormedSpace.exp_continuous.comp hcf).continuousOn).sub continuousOn_const)
        (fun t ht => by
          rw [Metric.mem_closedBall, dist_zero_right]
          have hts' : ‖(2 : 𝕂)⁻¹ • (t • a)‖ + ‖t • b‖ < Real.log 2 := by
            linarith [hnorm_fg t ht]
          rw [show exp (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • (t • a)) (t • b)) =
            exp ((2 : 𝕂)⁻¹ • (t • a)) * exp (t • b) from exp_bch _ _ hts']
          exact htriple_le _ _ (hnorm_triple t ht))
    · show ContinuousOn (fun t => logOnePlus (𝕂 := 𝕂)
        (exp (bch (𝕂 := 𝕂) (-((2 : 𝕂)⁻¹ • (t • a))) (-(t • b))) *
          exp (-((2 : 𝕂)⁻¹ • (t • a))) - 1)) (Set.Icc 0 1)
      exact (continuousOn_logOnePlus (𝕂 := 𝕂) hρ_lt).comp
        ((NormedSpace.exp_continuous.comp_continuousOn' hcont_inner_neg
          |>.mul (NormedSpace.exp_continuous.comp hcf.neg).continuousOn).sub continuousOn_const)
        (fun t ht => by
          rw [Metric.mem_closedBall, dist_zero_right]
          have hts' : ‖-((2 : 𝕂)⁻¹ • (t • a))‖ + ‖-(t • b)‖ < Real.log 2 := by
            rw [norm_neg, norm_neg]; linarith [hnorm_fg t ht]
          rw [show exp (bch (𝕂 := 𝕂) (-((2 : 𝕂)⁻¹ • (t • a))) (-(t • b))) =
            exp (-((2 : 𝕂)⁻¹ • (t • a))) * exp (-(t • b)) from exp_bch _ _ hts']
          exact htriple_le _ _ (by simp only [norm_neg]; exact hnorm_triple t ht))
    /- h(t) = bch(bch(a₂(t),b(t)),a₂(t)) + bch(bch(-a₂(t),-b(t)),-a₂(t))
    -- bch(x,y) = logOnePlus(exp(x)*exp(y)-1)
    -- So each bch is logOnePlus composed with a continuous function mapping into the unit ball
    -- Each summand is bch(bch(f(t),g(t)),f(t)) = logOnePlus(exp(bch(f,g))*exp(f)-1)
    -- The exp(bch(f,g))*exp(f) = exp(f)*exp(g)*exp(f) by exp_bch, so the argument is
    -- exp(f)*exp(g)*exp(f)-1 which has norm ≤ exp(2‖f‖+‖g‖)-1 ≤ exp(s)-1 < 1
    set ρ := Real.exp s - 1
    have hρ_lt : ρ < 1 := by
      have : Real.exp s < 2 := lt_of_lt_of_eq
        (Real.exp_strictMono (by linarith : s < Real.log 2)) (Real.exp_log (by norm_num))
      linarith
    -- Helper: norm bound for triple product ‖exp p * exp q * exp p - 1‖ ≤ exp(2‖p‖+‖q‖)-1
    have htriple_le : ∀ (p q : 𝔸), ‖p‖ + ‖q‖ + ‖p‖ ≤ s →
        ‖exp p * exp q * exp p - 1‖ ≤ ρ := by
      intro p q hpq
      -- Factor and bound using exp estimates
      have hfact : exp p * exp q * exp p - 1 =
        exp p * (exp q * exp p - 1) + (exp p - 1) := by noncomm_ring
      have hfact2 : exp q * exp p - 1 = (exp q - 1) * exp p + (exp p - 1) := by
        rw [sub_mul, one_mul]; abel
      rw [hfact]
      have h1 : ‖exp p * (exp q * exp p - 1) + (exp p - 1)‖ ≤
          ‖exp p‖ * ‖exp q * exp p - 1‖ + ‖exp p - 1‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_mul_le _ _) _)
      have h2 : ‖exp q * exp p - 1‖ ≤ Real.exp (‖q‖ + ‖p‖) - 1 := by
        rw [hfact2]
        calc ‖(exp q - 1) * exp p + (exp p - 1)‖
            ≤ ‖exp q - 1‖ * ‖exp p‖ + ‖exp p - 1‖ :=
              (norm_add_le _ _).trans (add_le_add_right (norm_mul_le _ _) _)
          _ ≤ (Real.exp ‖q‖ - 1) * Real.exp ‖p‖ + (Real.exp ‖p‖ - 1) := by
              gcongr
              · exact norm_exp_sub_one_le (𝕂 := 𝕂) q
              · exact norm_exp_le (𝕂 := 𝕂) p
              · exact norm_exp_sub_one_le (𝕂 := 𝕂) p
          _ = _ := by rw [Real.exp_add]; ring
      calc ‖exp p * (exp q * exp p - 1) + (exp p - 1)‖
          ≤ ‖exp p‖ * ‖exp q * exp p - 1‖ + ‖exp p - 1‖ := h1
        _ ≤ Real.exp ‖p‖ * (Real.exp (‖q‖ + ‖p‖) - 1) + (Real.exp ‖p‖ - 1) := by
            gcongr
            · exact norm_exp_le (𝕂 := 𝕂) p
            · exact norm_exp_sub_one_le (𝕂 := 𝕂) p
        _ = Real.exp (‖p‖ + ‖q‖ + ‖p‖) - 1 := by rw [Real.exp_add, Real.exp_add]; ring
        _ ≤ ρ := by gcongr
    -- Continuity of basic functions
    have hcf : Continuous (fun t : ℝ => (2 : 𝕂)⁻¹ • (t • a)) :=
      continuous_const.smul (continuous_id.smul continuous_const)
    have hcg : Continuous (fun t : ℝ => t • b) := continuous_id.smul continuous_const
    -- Norm bound: ‖a₂(t)‖ + ‖tb(t)‖ + ‖a₂(t)‖ ≤ s for t ∈ [0,1]
    have hnorm_half_smul : ∀ x : 𝔸, ‖(2 : 𝕂)⁻¹ • x‖ ≤ ‖x‖ / 2 := by
      intro x; calc ‖(2 : 𝕂)⁻¹ • x‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖x‖ := norm_smul_le _ _
        _ = ‖x‖ / 2 := by rw [h_half]; ring
    have hnorm_triple : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖(2 : 𝕂)⁻¹ • (t • a)‖ + ‖t • b‖ + ‖(2 : 𝕂)⁻¹ • (t • a)‖ ≤ s := by
      intro t ht
      have h1 := hnorm_half_smul (t • a)
      calc ‖(2 : 𝕂)⁻¹ • (t • a)‖ + ‖t • b‖ + ‖(2 : 𝕂)⁻¹ • (t • a)‖
          ≤ ‖t • a‖ / 2 + ‖t • b‖ + ‖t • a‖ / 2 := by linarith
        _ = ‖t • a‖ + ‖t • b‖ := by ring
        _ ≤ s := hnorm_t t ht.1 ht.2
    -- Inner bch continuity
    have hnorm_fg : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖(2 : 𝕂)⁻¹ • (t • a)‖ + ‖t • b‖ ≤ s := by
      intro t ht; linarith [hnorm_triple t ht, norm_nonneg ((2 : 𝕂)⁻¹ • (t • a))]
    -- Helper: ‖exp f * exp g - 1‖ ≤ exp(‖f‖+‖g‖)-1
    have hprod_le : ∀ (f g : 𝔸), ‖exp f * exp g - 1‖ ≤ Real.exp (‖f‖ + ‖g‖) - 1 := by
      intro f g
      have hfact : exp f * exp g - 1 = (exp f - 1) * exp g + (exp g - 1) := by
        rw [sub_mul, one_mul]; abel
      rw [hfact]
      calc ‖(exp f - 1) * exp g + (exp g - 1)‖
          ≤ ‖exp f - 1‖ * ‖exp g‖ + ‖exp g - 1‖ :=
            (norm_add_le _ _).trans (add_le_add_right (norm_mul_le _ _) _)
        _ ≤ (Real.exp ‖f‖ - 1) * Real.exp ‖g‖ + (Real.exp ‖g‖ - 1) := by
            gcongr
            · exact norm_exp_sub_one_le (𝕂 := 𝕂) f
            · exact norm_exp_le (𝕂 := 𝕂) g
            · exact norm_exp_sub_one_le (𝕂 := 𝕂) g
        _ = _ := by rw [Real.exp_add]; ring
    -- Continuity of bch(f(t), g(t)) when f, g continuous and ‖f‖+‖g‖ ≤ s on [0,1]
    have hcont_bch : ∀ (f g : ℝ → 𝔸), Continuous f → Continuous g →
        (∀ t ∈ Set.Icc 0 1, ‖f t‖ + ‖g t‖ ≤ s) →
        ContinuousOn (fun t => bch (𝕂 := 𝕂) (f t) (g t)) (Set.Icc 0 1) := by
      intro f g hf hg hfg
      show ContinuousOn (fun t => logOnePlus (𝕂 := 𝕂) (exp (f t) * exp (g t) - 1)) _
      apply (continuousOn_logOnePlus (𝕂 := 𝕂) hρ_lt).comp
      · exact ((NormedSpace.exp_continuous.comp hf).mul
            (NormedSpace.exp_continuous.comp hg)).sub continuous_const |>.continuousOn
      · intro t ht; rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖exp (f t) * exp (g t) - 1‖ ≤ Real.exp (‖f t‖ + ‖g t‖) - 1 := hprod_le _ _
          _ ≤ ρ := by gcongr; exact hfg t ht
    have hcont_inner_pos := hcont_bch _ _ hcf hcg hnorm_fg
    have hcont_inner_neg := hcont_bch _ _ hcf.neg hcg.neg (by
      intro t ht; rw [norm_neg, norm_neg]; exact hnorm_fg t ht)
    -- Now prove h = sum of two summands, each continuous
    apply ContinuousOn.add
    · -- First summand: logOnePlus(exp(inner_bch)*exp(a₂)-1) where inner_bch = bch(a₂,tb)
      show ContinuousOn
        (fun t => logOnePlus (𝕂 := 𝕂) (exp (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • (t • a)) (t • b)) *
          exp ((2 : 𝕂)⁻¹ • (t • a)) - 1)) (Set.Icc 0 1)
      apply (continuousOn_logOnePlus (𝕂 := 𝕂) hρ_lt).comp
      · exact (NormedSpace.exp_continuous.continuousOn.comp hcont_inner_pos Set.Subset.rfl
          |>.mul (NormedSpace.exp_continuous.comp hcf).continuousOn).sub continuousOn_const
      · intro t ht; rw [Metric.mem_closedBall, dist_zero_right]
        have hts' : ‖(2 : 𝕂)⁻¹ • (t • a)‖ + ‖t • b‖ < Real.log 2 := by
          linarith [hnorm_fg t ht]
        -- exp(bch(a₂,tb))*exp(a₂) = exp(a₂)*exp(tb)*exp(a₂) by exp_bch
        have hexpb := exp_bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • (t • a)) (t • b) hts'
        rw [hexpb]; exact htriple_le _ _ (hnorm_triple t ht)
    · -- Second summand: same with negated arguments
      show ContinuousOn
        (fun t => logOnePlus (𝕂 := 𝕂) (exp (bch (𝕂 := 𝕂) (-((2 : 𝕂)⁻¹ • (t • a))) (-(t • b))) *
          exp (-((2 : 𝕂)⁻¹ • (t • a))) - 1)) (Set.Icc 0 1)
      apply (continuousOn_logOnePlus (𝕂 := 𝕂) hρ_lt).comp
      · exact (NormedSpace.exp_continuous.continuousOn.comp hcont_inner_neg Set.Subset.rfl
          |>.mul (NormedSpace.exp_continuous.comp hcf.neg).continuousOn).sub continuousOn_const
      · intro t ht; rw [Metric.mem_closedBall, dist_zero_right]
        have hts' : ‖-((2 : 𝕂)⁻¹ • (t • a))‖ + ‖-(t • b)‖ < Real.log 2 := by
          rw [norm_neg, norm_neg]; linarith [hnorm_fg t ht]
        have hexpb := exp_bch (𝕂 := 𝕂) (-((2 : 𝕂)⁻¹ • (t • a))) (-(t • b)) hts'
        rw [hexpb]
        -- ‖exp(-a₂)*exp(-tb)*exp(-a₂)-1‖ ≤ ρ via htriple_le with norms of negations
        exact htriple_le _ _ (by rw [norm_neg, norm_neg, norm_neg]; exact hnorm_triple t ht) -/
  -- Step 4-6: Chain of neighborhoods argument (same as logOnePlus_exp_sub_one)
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have huc := hcompact.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (Real.log 2) (Real.log_pos (by norm_num))
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN_pos : 0 < N := by
    rcases N with _ | n
    · simp at hN; linarith [div_pos one_pos hδ_pos]
    · exact Nat.succ_pos n
  suffices hind : ∀ k : ℕ, k ≤ N → h (k / N) = 0 by
    have := hind N le_rfl
    rwa [show (N : ℝ) / N = 1 from div_self (Nat.cast_ne_zero.mpr (by omega))] at this
  intro k hk
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have hk_le : k ≤ N := by omega
    have hprev := ih hk_le
    have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have hkN_mem : (k : ℝ) / N ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg k) hN_pos_real.le,
       div_le_one_of_le₀ (Nat.cast_le.mpr hk_le) hN_pos_real.le⟩
    have hk1N_mem : ((k+1 : ℕ) : ℝ) / N ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hN_pos_real.le,
       div_le_one_of_le₀ (Nat.cast_le.mpr hk) hN_pos_real.le⟩
    have h1N_lt : (1 : ℝ) / N < δ := by
      rw [one_div]
      exact (inv_lt_comm₀ hδ_pos hN_pos_real).mp (by rwa [one_div] at hN)
    have hdist' : dist ((↑(k + 1) : ℝ) / ↑N) (↑k / ↑N) < δ := by
      rw [dist_comm, Real.dist_eq, show (k : ℝ) / N - ((k + 1 : ℕ) : ℝ) / N = -(1 / N) from by
        push_cast; field_simp; ring, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / N)]
      exact h1N_lt
    have hnorm_small : ‖h ((k+1 : ℕ) / N) - h (k / N)‖ < Real.log 2 := by
      rw [← dist_eq_norm]; exact hδ _ hk1N_mem _ hkN_mem hdist'
    rw [hprev, sub_zero] at hnorm_small
    have hexp1 : exp (h ((k+1 : ℕ) / N)) = 1 :=
      hexp_ht _ hk1N_mem.1 hk1N_mem.2
    exact exp_eq_one_of_norm_lt (𝕂 := 𝕂) _ hexp1 hnorm_small

include 𝕂 in
/-- The symmetric BCH cubic coefficient is an odd function:
`E₃(-a,-b) = -E₃(a,b)`. -/
theorem symmetric_bch_cubic_neg (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    symmetric_bch_cubic 𝕂 (-a) (-b) = -(symmetric_bch_cubic 𝕂 a b) := by
  unfold symmetric_bch_cubic
  have h := symmetric_bch_add_neg (𝕂 := 𝕂) a b hab
  have hZ_neg : bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • (-a)) (-b)) ((2 : 𝕂)⁻¹ • (-a)) =
      -(bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a)) :=
    eq_neg_of_add_eq_zero_right h
  rw [hZ_neg]; abel

/-- The cubic-polynomial part of the symmetric BCH deviation `Z(a,b) - (a+b)`.

Computed explicitly as `-(1/24)·[a,[a,b]] + (1/12)·[b,[b,a]]`, the classical
third-order Strang splitting coefficient. Homogeneous of degree 3 in `(a, b)`.
Derived from `bch_cubic_term(½a, b) + (1/16)·[[a,b],a] + bch_cubic_term(½a+b, ½a)`,
which is the degree-3 part of the expansion of `bch(bch(½a, b), ½a) - (a+b)`. -/
noncomputable def symmetric_bch_cubic_poly (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
  -((24 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)) +
  (12 : 𝕂)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Homogeneity of `symmetric_bch_cubic_poly`**: `sym_E₃(c·a, c·b) = c³·sym_E₃(a, b)`.

Used to close the small-s case of `norm_symmetric_bch_cubic_sub_smul_le`: the
c³-scaling mismatch between `symmetric_bch_cubic` and `c³·symmetric_bch_cubic` is
absorbed into the quintic remainder after subtracting this homogeneous polynomial. -/
theorem symmetric_bch_cubic_poly_smul (a b : 𝔸) (c : 𝕂) :
    symmetric_bch_cubic_poly 𝕂 (c • a) (c • b) =
      c ^ 3 • symmetric_bch_cubic_poly 𝕂 a b := by
  -- Helper: triple-product homogeneity (same as in bch_cubic_term_smul)
  have triple : ∀ x y z : 𝔸,
      (c • x) * ((c • y) * (c • z)) = c ^ 3 • (x * (y * z)) := by
    intro x y z
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1; ring
  have triple' : ∀ x y z : 𝔸,
      ((c • x) * (c • y)) * (c • z) = c ^ 3 • (x * y * z) := by
    intro x y z
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1; ring
  unfold symmetric_bch_cubic_poly
  simp only [mul_sub, sub_mul, triple, triple', ← smul_sub,
    smul_comm ((24 : 𝕂)⁻¹) (c ^ 3), smul_comm ((12 : 𝕂)⁻¹) (c ^ 3),
    ← smul_add, ← smul_neg]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Norm bound for `symmetric_bch_cubic_poly`: `‖sym_E₃(a,b)‖ ≤ s³`. -/
theorem norm_symmetric_bch_cubic_poly_le (a b : 𝔸) :
    ‖symmetric_bch_cubic_poly 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 3 := by
  unfold symmetric_bch_cubic_poly
  set α := ‖a‖; set β := ‖b‖
  have hα_nn : (0:ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0:ℝ) ≤ β := norm_nonneg b
  -- Norms of the two scalars: ‖(24:𝕂)⁻¹‖ = 1/24 ≤ 1, ‖(12:𝕂)⁻¹‖ = 1/12 ≤ 1
  have h24_le : ‖(24 : 𝕂)⁻¹‖ ≤ 1 := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h12_le : ‖(12 : 𝕂)⁻¹‖ ≤ 1 := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  -- ‖[a,[a,b]]‖ ≤ 4·α²·β  (via two levels of triangle inequality + norm_mul_le)
  have h_aab : ‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 * α ^ 2 * β := by
    have hab_le : ‖a * b - b * a‖ ≤ 2 * α * β := by
      calc ‖a * b - b * a‖ ≤ ‖a * b‖ + ‖b * a‖ := by
            rw [sub_eq_add_neg]
            exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ α * β + β * α := by gcongr <;> exact norm_mul_le _ _
        _ = 2 * α * β := by ring
    calc ‖a * (a * b - b * a) - (a * b - b * a) * a‖
        ≤ ‖a * (a * b - b * a)‖ + ‖(a * b - b * a) * a‖ := by
          rw [sub_eq_add_neg]
          exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ α * (2 * α * β) + (2 * α * β) * α := by
          gcongr
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hab_le hα_nn)
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hab_le hα_nn)
      _ = 4 * α ^ 2 * β := by ring
  have h_bba : ‖b * (b * a - a * b) - (b * a - a * b) * b‖ ≤ 4 * α * β ^ 2 := by
    have hba_le : ‖b * a - a * b‖ ≤ 2 * α * β := by
      calc ‖b * a - a * b‖ ≤ ‖b * a‖ + ‖a * b‖ := by
            rw [sub_eq_add_neg]
            exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ β * α + α * β := by gcongr <;> exact norm_mul_le _ _
        _ = 2 * α * β := by ring
    calc ‖b * (b * a - a * b) - (b * a - a * b) * b‖
        ≤ ‖b * (b * a - a * b)‖ + ‖(b * a - a * b) * b‖ := by
          rw [sub_eq_add_neg]
          exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ β * (2 * α * β) + (2 * α * β) * β := by
          gcongr
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hba_le hβ_nn)
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hba_le hβ_nn)
      _ = 4 * α * β ^ 2 := by ring
  -- Bound each scaled commutator
  have h1 : ‖(24 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)‖ ≤ α ^ 2 * β := by
    calc _ ≤ ‖(24 : 𝕂)⁻¹‖ * ‖_‖ := norm_smul_le _ _
      _ ≤ (1 / 24 : ℝ) * (4 * α ^ 2 * β) := by
          have : ‖(24 : 𝕂)⁻¹‖ = (1 / 24 : ℝ) := by
            rw [norm_inv, RCLike.norm_ofNat]; norm_num
          rw [this]; gcongr
      _ ≤ α ^ 2 * β := by nlinarith [sq_nonneg α, hβ_nn]
  have h2 : ‖(12 : 𝕂)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)‖ ≤ α * β ^ 2 := by
    calc _ ≤ ‖(12 : 𝕂)⁻¹‖ * ‖_‖ := norm_smul_le _ _
      _ ≤ (1 / 12 : ℝ) * (4 * α * β ^ 2) := by
          have : ‖(12 : 𝕂)⁻¹‖ = (1 / 12 : ℝ) := by
            rw [norm_inv, RCLike.norm_ofNat]; norm_num
          rw [this]; gcongr
      _ ≤ α * β ^ 2 := by nlinarith [sq_nonneg β, hα_nn]
  -- Combine via triangle inequality
  set X : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a
  set Y : 𝔸 := b * (b * a - a * b) - (b * a - a * b) * b
  calc ‖-((24 : 𝕂)⁻¹ • X) + (12 : 𝕂)⁻¹ • Y‖
      ≤ ‖-((24 : 𝕂)⁻¹ • X)‖ + ‖(12 : 𝕂)⁻¹ • Y‖ := norm_add_le _ _
    _ = ‖(24 : 𝕂)⁻¹ • X‖ + ‖(12 : 𝕂)⁻¹ • Y‖ := by rw [norm_neg]
    _ ≤ α ^ 2 * β + α * β ^ 2 := by linarith
    _ ≤ (α + β) ^ 3 := by nlinarith [sq_nonneg (α - β), hα_nn, hβ_nn, sq_nonneg α, sq_nonneg β]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **sym_E₃ alt-form identity**: the closed-form `symmetric_bch_cubic_poly` equals
the alt form `C₃(½a,b) + C₃(½a+b,½a) - (1/16)·DC_a`, where `DC_a = a·[a,b] - [a,b]·a`.

This is the key step relating the explicit polynomial definition to the form that
arises from applying `norm_bch_quintic_remainder_le` twice through the symmetric
composition. Verified by multiplying both sides by 48, clearing scalars, and
`noncomm_ring`. -/
theorem symmetric_bch_cubic_poly_alt_form (a b : 𝔸) :
    symmetric_bch_cubic_poly 𝕂 a b =
      bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
      bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) -
      (16 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a) := by
  unfold symmetric_bch_cubic_poly bch_cubic_term
  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  match_scalars <;> ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Key quartic cancellation for symmetric BCH**: the four degree-4 contributions to
`sym_bch_cubic - sym_E₃` sum to zero as a ring identity.

Specifically, writing `a' = ½a`, the four contributions are:
- A := ½[C₃(a',b), a']  (from the half-commutator ½[w, a'] expansion, w = z-(a'+b))
- B := C₄(a',b)         (the inner BCH quartic)
- C := -(1/96)·[b, DC_a]  (the linear-in-w₂ part of [C₃(z,a') - C₃(a'+b,a')],
                           where w₂ = ½(a'b-ba'); equals (1/12)·([(a'+b),[w₂,a']] +
                           [w₂,[(a'+b),a']] + [a',[a',w₂]]) — verified algebraically)
- D := C₄(a'+b, a')     (the constant part of C₄(z, a'))

The identity `A + B + C + D = 0` holds because, after expansion:
- A + D contributes `(1/48)·[DC_b, a]` (the [DC_a,a] terms cancel between A and D).
- B + C contributes `-(1/48)·[b, DC_a]`.
- And `[DC_b, a] = [b, DC_a]` is itself an associative-algebra identity (both expand
  to `b²a² - 2baba + 2abab - a²b²`). -/
theorem symmetric_bch_quartic_identity (a b : 𝔸) :
    (2 : 𝕂)⁻¹ • (bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b * ((2 : 𝕂)⁻¹ • a) -
                  ((2 : 𝕂)⁻¹ • a) * bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b) +
      bch_quartic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
      -((96 : 𝕂)⁻¹ • (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
                       (a * (a * b - b * a) - (a * b - b * a) * a) * b)) +
      bch_quartic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) = 0 := by
  unfold bch_cubic_term bch_quartic_term
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

set_option maxHeartbeats 16000000 in
include 𝕂 in
/-- **Symmetric BCH quintic remainder bound**: the symmetric BCH deviation equals the
cubic polynomial `symmetric_bch_cubic_poly` up to `O(s⁵)` error. This is the symmetric
analog of `norm_bch_quintic_remainder_le`, obtained by applying the quintic BCH theorem
twice through the composition `bch(bch(½a, b), ½a)` and collecting cubic contributions.

The constant `10⁷` is loose: the dominant contribution comes from the outer-BCH
quintic remainder R₂ at norm `s₂ = ‖z‖+‖a'‖ ≤ 57s/22`, giving R₂ ≤ ~4·10⁶·s⁵.
A tighter form `K·s⁵/(2-exp(2s))` would reduce it (analogous to
`norm_bch_quintic_remainder_le`), but the simpler `K·s⁵` form suffices for
the Suzuki use case. -/
theorem norm_symmetric_bch_cubic_sub_poly_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b‖ ≤
      10000000 * (‖a‖ + ‖b‖) ^ 5 := by
  -- SETUP: a' = ½a, s = ‖a‖+‖b‖, s₁ = ‖a'‖+‖b‖ ≤ s, z = bch(a', b)
  set a' : 𝔸 := (2 : 𝕂)⁻¹ • a with ha'_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set s₁ := ‖a'‖ + ‖b‖ with hs₁_def
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ ‖a‖ / 2 := by
    calc ‖a'‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  have ha'_le_s : ‖a'‖ ≤ s := by
    calc ‖a'‖ ≤ ‖a‖ / 2 := ha'_le
      _ ≤ ‖a‖ := by linarith [norm_nonneg a]
      _ ≤ s := le_add_of_nonneg_right (norm_nonneg b)
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt : s < 1 / 4 := hab
  have hs1 : s < 1 := by linarith
  have hs₁_le : s₁ ≤ s := by
    show ‖a'‖ + ‖b‖ ≤ ‖a‖ + ‖b‖; linarith [ha'_le, norm_nonneg a]
  have hs₁_nn : 0 ≤ s₁ := by positivity
  have hln2 : (1 : ℝ) / 4 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    linarith [real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1:ℝ)/4 < 5/6)]
  have hs₁_lt_log2 : s₁ < Real.log 2 := by linarith
  -- Inner BCH: z = bch(a', b)
  set z := bch (𝕂 := 𝕂) a' b with hz_def
  -- Quintic remainder of inner BCH: R₁ = z - (a'+b) - ½(a'b-ba') - C₃(a',b) - C₄(a',b)
  set R₁ := z - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a') -
      bch_cubic_term 𝕂 a' b - bch_quartic_term 𝕂 a' b with hR₁_def
  -- Bound: ‖R₁‖ ≤ 3000·s₁⁵/(2-exp(s₁))
  have hR₁_le : ‖R₁‖ ≤ 3000 * s₁ ^ 5 / (2 - Real.exp s₁) := by
    rw [hR₁_def]
    exact norm_bch_quintic_remainder_le (𝕂 := 𝕂) a' b hs₁_lt_log2
  -- Quadratic bound: ‖z - (a'+b)‖ ≤ 3·s₁²/(2-exp(s₁))
  have hexp_s₁_lt : Real.exp s₁ < 2 := by
    calc _ < Real.exp (Real.log 2) := Real.exp_strictMono hs₁_lt_log2
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith
  set W := z - (a' + b) with hW_def
  have hW_le : ‖W‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    rw [hW_def]; exact norm_bch_sub_add_le (𝕂 := 𝕂) a' b hs₁_lt_log2
  -- s₂ = ‖z‖ + ‖a'‖ < log 2 (for the second quintic application)
  have hexp_le : Real.exp s₁ ≤ 1 + s₁ + s₁ ^ 2 := by
    nlinarith [real_exp_third_order_le_cube hs₁_nn (by linarith : s₁ < 5/6)]
  have hdenom_lb : (11 : ℝ) / 16 ≤ 2 - Real.exp s₁ := by nlinarith
  have hquad_bound : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 3 / 11 := by
    rw [div_le_div_iff₀ hdenom₁ (by norm_num : (0:ℝ) < 11)]
    nlinarith [sq_nonneg s₁, sq_nonneg (1/4 - s₁)]
  have hz_le : ‖z‖ ≤ s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    calc ‖z‖ = ‖(z - (a' + b)) + (a' + b)‖ := by congr 1; abel
      _ ≤ ‖z - (a' + b)‖ + ‖a' + b‖ := norm_add_le _ _
      _ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) + s₁ := by
          have hsum : ‖a' + b‖ ≤ s₁ := norm_add_le _ _
          linarith [hW_le, hW_def]
      _ = s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by ring
  have hln2_611 : (6 : ℝ) / 11 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    linarith [real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 6/11)
      (by norm_num : (6:ℝ)/11 < 5/6)]
  have hs₂_lt_log2 : ‖z‖ + ‖a'‖ < Real.log 2 := by
    calc ‖z‖ + ‖a'‖ ≤ (s₁ + 3 / 11) + ‖a'‖ := by linarith [hz_le, hquad_bound]
      _ ≤ s + 3 / 11 := by linarith [ha'_le_s]
      _ < 1/4 + 3 / 11 := by linarith
      _ = 23 / 44 := by norm_num
      _ < 6 / 11 := by norm_num
      _ < Real.log 2 := hln2_611
  -- Outer quintic remainder: R₂ = bch(z,a') - (z+a') - ½(z·a'-a'·z) - C₃(z,a') - C₄(z,a')
  set R₂ := bch (𝕂 := 𝕂) z a' - (z + a') - (2 : 𝕂)⁻¹ • (z * a' - a' * z) -
      bch_cubic_term 𝕂 z a' - bch_quartic_term 𝕂 z a' with hR₂_def
  have hR₂_le : ‖R₂‖ ≤ 3000 * (‖z‖ + ‖a'‖) ^ 5 / (2 - Real.exp (‖z‖ + ‖a'‖)) := by
    rw [hR₂_def]
    exact norm_bch_quintic_remainder_le (𝕂 := 𝕂) z a' hs₂_lt_log2
  -- Key commutator helper: ¼[(a'b - ba'), a'] = -(1/16)·DC_a
  set DC_a : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a with hDC_a_def
  -- KEY DECOMPOSITION: sym_bch_cubic - sym_E₃ as a sum of 6 terms.
  -- 1. R₁ + R₂  (each O(s⁵) by quintic BCH)
  -- 2. ½[R₁, a']     (O(s·s⁵) = O(s⁶) ≤ O(s⁵))
  -- 3. ½[C₄(a',b), a']     (O(s⁴·s) = O(s⁵))
  -- 4. quartic_identity_sum = 0 (by symmetric_bch_quartic_identity)
  -- 5. C₃(z,a') - C₃(a'+b, a') - C_d4  (O(s⁵) residual after subtracting
  --    the degree-4 part; the degree-4 part is C_d4 = -(1/96)·[b, DC_a])
  -- 6. C₄(z,a') - C₄(a'+b, a')  (O(s⁵) residual after degree-4)
  --
  -- The algebraic decomposition (provable by `abel` after unfolding R₁, R₂ and
  -- the sym_E₃ → alt form rewrite, plus the quartic identity for degree-4 cancel):
  have hdecomp : symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b =
      R₁ + R₂ +
      (2 : 𝕂)⁻¹ • (R₁ * a' - a' * R₁) +
      (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b) +
      (bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
        -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
      (bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a') := by
    rw [symmetric_bch_cubic_poly_alt_form (𝕂 := 𝕂)]
    have hbch_z_a' : bch (𝕂 := 𝕂) z a' = (z + a') + (2 : 𝕂)⁻¹ • (z * a' - a' * z) +
        bch_cubic_term 𝕂 z a' + bch_quartic_term 𝕂 z a' + R₂ := by
      rw [hR₂_def]; abel
    have hzcom : z * a' - a' * z = (a' + b) * a' - a' * (a' + b) +
        ((z - (a' + b)) * a' - a' * (z - (a' + b))) := by noncomm_ring
    have hW_eq : z - (a' + b) =
        (2 : 𝕂)⁻¹ • (a' * b - b * a') + bch_cubic_term 𝕂 a' b +
          bch_quartic_term 𝕂 a' b + R₁ := by
      rw [hR₁_def, hW_def]; abel
    have hz_eq : z = a' + b + (2 : 𝕂)⁻¹ • (a' * b - b * a') + bch_cubic_term 𝕂 a' b +
        bch_quartic_term 𝕂 a' b + R₁ := by
      rw [show z = (z - (a' + b)) + (a' + b) from by abel, hW_eq]; abel
    have hQI := symmetric_bch_quartic_identity (𝕂 := 𝕂) a b
    show bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) - (a + b) -
        (bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
         bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) -
         (16 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)) = _
    have hbch_inner : bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b = z := by rw [hz_def, ha'_def]
    rw [hbch_inner, hbch_z_a', hzcom, hW_eq]
    have hQI_rearr : bch_quartic_term 𝕂 (a' + b) a' =
        -((2 : 𝕂)⁻¹ • (bch_cubic_term 𝕂 a' b * a' - a' * bch_cubic_term 𝕂 a' b)) -
        bch_quartic_term 𝕂 a' b +
        (96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b) := by
      have h := hQI
      have h' : ((2 : 𝕂)⁻¹ • (bch_cubic_term 𝕂 a' b * a' - a' * bch_cubic_term 𝕂 a' b) +
                  bch_quartic_term 𝕂 a' b +
                  -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))) +
                 bch_quartic_term 𝕂 (a' + b) a' = 0 := by
        simp only [ha'_def, hDC_a_def]
        convert h using 2
      have hW := eq_neg_of_add_eq_zero_right h'
      rw [hW]; abel
    rw [hQI_rearr]
    simp only [smul_sub, smul_add, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
      sub_mul, mul_sub, ha'_def, hDC_a_def, smul_smul,
      show ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = (4 : 𝕂)⁻¹ from by norm_num,
      show ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (4 : 𝕂)⁻¹)) = (16 : 𝕂)⁻¹ from by norm_num,
      show ((2 : 𝕂)⁻¹ * ((4 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = (16 : 𝕂)⁻¹ from by norm_num,
      show ((2 : 𝕂)⁻¹ * (4 : 𝕂)⁻¹) = (8 : 𝕂)⁻¹ from by norm_num,
      show ((4 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = (8 : 𝕂)⁻¹ from by norm_num,
      show ((2 : 𝕂)⁻¹ * (8 : 𝕂)⁻¹) = (16 : 𝕂)⁻¹ from by norm_num,
      show ((8 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = (16 : 𝕂)⁻¹ from by norm_num]
    nth_rewrite 1 [hz_eq]
    simp only [ha'_def, smul_sub, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      show ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = (4 : 𝕂)⁻¹ from by norm_num,
      one_smul, mul_one]
    -- The remaining mismatch: two separate `(2:𝕂)⁻¹ • a` terms on LHS sum to `a` on RHS.
    -- Combine them: 2⁻¹•a + 2⁻¹•a = (2⁻¹+2⁻¹)•a = 1•a = a.
    have h_half_sum : (2 : 𝕂)⁻¹ • a + (2 : 𝕂)⁻¹ • a = a := by
      rw [← add_smul, show ((2 : 𝕂)⁻¹ + (2 : 𝕂)⁻¹) = (1 : 𝕂) from by ring, one_smul]
    -- abel will collect the 2⁻¹•a terms; combined with h_half_sum, equality holds.
    linear_combination (norm := abel) (h_half_sum : (2 : 𝕂)⁻¹ • a + (2 : 𝕂)⁻¹ • a = a)
  rw [hdecomp]
  -- Setup: ‖a'‖ ≤ s/2, ‖a‖ ≤ s, ‖b‖ ≤ s.
  have ha_s : ‖a‖ ≤ s := by have := norm_nonneg b; linarith [hs_def]
  have hb_s : ‖b‖ ≤ s := by have := norm_nonneg a; linarith [hs_def]
  have ha'_s : ‖a'‖ ≤ s / 2 := by
    calc ‖a'‖ ≤ ‖a‖ / 2 := ha'_le
      _ ≤ s / 2 := by linarith
  -- TERM 1: ‖R₁‖ ≤ 5000 · s⁵ (PROVED)
  have hR₁_s5 : ‖R₁‖ ≤ 5000 * s ^ 5 := by
    have h1 : ‖R₁‖ ≤ 3000 * s₁ ^ 5 / (2 - Real.exp s₁) := hR₁_le
    have hX_s5 : 3000 * s₁ ^ 5 / (2 - Real.exp s₁) ≤ 5000 * s ^ 5 := by
      rw [div_le_iff₀ hdenom₁]
      have hs_pow : s₁ ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ hs₁_nn hs₁_le 5
      have hs5_nn : (0 : ℝ) ≤ s ^ 5 := pow_nonneg hs_nn 5
      nlinarith [hdenom_lb, hs_pow, hs5_nn]
    linarith
  -- Bounds on ‖z‖, s₂ = ‖z‖+‖a'‖.
  have hz_mult : ‖z‖ ≤ 23/11 * s := by
    have h1 : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 12 * s / 11 := by
      rw [div_le_iff₀ hdenom₁]
      nlinarith [hdenom_lb, hs₁_nn, sq_nonneg s₁, hs₁_le, hs_nn,
        mul_nonneg hs₁_nn hs_nn, hab]
    calc ‖z‖ ≤ s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := hz_le
      _ ≤ s + 12 * s / 11 := by linarith
      _ = 23/11 * s := by ring
  have hs₂_mult : ‖z‖ + ‖a'‖ ≤ 57/22 * s := by
    calc ‖z‖ + ‖a'‖ ≤ 23/11 * s + s/2 := by linarith [hz_mult, ha'_s]
      _ = 57/22 * s := by ring
  -- ‖z‖+‖a'‖ ≤ 57/88 (absolute) since s ≤ 1/4
  have hs₂_le_const : ‖z‖ + ‖a'‖ ≤ 57 / 88 := by
    calc ‖z‖ + ‖a'‖ ≤ 57/22 * s := hs₂_mult
      _ ≤ 57/22 * (1/4) := by
          have : s ≤ 1/4 := by linarith
          have : (0:ℝ) ≤ 57/22 := by norm_num
          nlinarith
      _ = 57 / 88 := by ring
  have hdenom₂_pos : 0 < 2 - Real.exp (‖z‖ + ‖a'‖) := by
    have : Real.exp (‖z‖ + ‖a'‖) < 2 := by
      calc _ < Real.exp (Real.log 2) := Real.exp_strictMono hs₂_lt_log2
        _ = 2 := Real.exp_log (by norm_num)
    linarith
  -- Tight denom bound via Real.exp_bound' (6th-order Taylor with tight remainder):
  -- exp(57/88) ≤ Σ_{k=0}^5 (57/88)^k/k! + (57/88)^6 · 7/(720·6) ≤ 1.912
  have hexp_57 : Real.exp (57/88) ≤ 23 / 12 := by
    have h := Real.exp_bound' (show (0:ℝ) ≤ 57/88 by norm_num)
      (show (57:ℝ)/88 ≤ 1 by norm_num) (show 0 < 6 by norm_num)
    -- ∑_{m=0}^5 = 1 + x + x²/2 + x³/6 + x⁴/24 + x⁵/120; remainder = x⁶·7/(720·6)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
      pow_zero, pow_one, pow_succ, zero_add] at h
    nlinarith [h, sq_nonneg ((57:ℝ)/88)]
  have hexp_s₂_le : Real.exp (‖z‖ + ‖a'‖) ≤ Real.exp (57/88) :=
    Real.exp_monotone hs₂_le_const
  have hdenom₂_lb : (1 : ℝ) / 12 ≤ 2 - Real.exp (‖z‖ + ‖a'‖) := by
    linarith [hexp_s₂_le, hexp_57]
  -- TERM 2: ‖R₂‖ ≤ K_R₂ · s⁵
  -- R₂ ≤ 3000·(s₂)⁵/(2-exp(s₂)) ≤ 3000·(57/22·s)⁵·12 = 3000·12·(57/22)⁵·s⁵
  -- ≈ 3000·12·116.76 = 4,203,360 → use 5,000,000 with margin.
  have hR₂_s5 : ‖R₂‖ ≤ 5000000 * s ^ 5 := by
    have h1 : ‖R₂‖ ≤ 3000 * (‖z‖ + ‖a'‖) ^ 5 / (2 - Real.exp (‖z‖ + ‖a'‖)) := hR₂_le
    have hX_s5 : 3000 * (‖z‖ + ‖a'‖) ^ 5 / (2 - Real.exp (‖z‖ + ‖a'‖)) ≤
                 5000000 * s ^ 5 := by
      rw [div_le_iff₀ hdenom₂_pos]
      have h_pow : (‖z‖ + ‖a'‖) ^ 5 ≤ (57/22 * s) ^ 5 :=
        pow_le_pow_left₀ (by positivity) hs₂_mult 5
      have h_pow_eq : (57/22 * s) ^ 5 = (57/22)^5 * s ^ 5 := by ring
      have hs5_nn : (0 : ℝ) ≤ s ^ 5 := pow_nonneg hs_nn 5
      nlinarith [hdenom₂_lb, h_pow, hs5_nn]
    linarith
  -- TERM 3: ‖(2:𝕂)⁻¹·(R₁·a' - a'·R₁)‖ ≤ ‖R₁‖·‖a'‖ ≤ 5000·s⁵·s/2 ≤ 5000·s⁵·(1/8) = 625·s⁵
  have hT3 : ‖(2 : 𝕂)⁻¹ • (R₁ * a' - a' * R₁)‖ ≤ 1000 * s ^ 5 := by
    have h2_inv : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
    have hcomm_bound : ‖R₁ * a' - a' * R₁‖ ≤ 2 * ‖R₁‖ * ‖a'‖ := by
      calc ‖R₁ * a' - a' * R₁‖
          ≤ ‖R₁ * a'‖ + ‖a' * R₁‖ := by
            rw [sub_eq_add_neg]
            exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖R₁‖ * ‖a'‖ + ‖a'‖ * ‖R₁‖ := by gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖R₁‖ * ‖a'‖ := by ring
    calc ‖(2 : 𝕂)⁻¹ • (R₁ * a' - a' * R₁)‖
        ≤ ‖(2 : 𝕂)⁻¹‖ * ‖R₁ * a' - a' * R₁‖ := norm_smul_le _ _
      _ = (2 : ℝ)⁻¹ * ‖R₁ * a' - a' * R₁‖ := by rw [h2_inv]
      _ ≤ (2 : ℝ)⁻¹ * (2 * ‖R₁‖ * ‖a'‖) := by
          apply mul_le_mul_of_nonneg_left hcomm_bound (by norm_num)
      _ = ‖R₁‖ * ‖a'‖ := by ring
      _ ≤ (5000 * s ^ 5) * (s / 2) := mul_le_mul hR₁_s5 ha'_s (norm_nonneg _) (by positivity)
      _ ≤ 1000 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5, hs_lt]
  -- TERM 4: ‖(2:𝕂)⁻¹·(C₄(a',b)·a' - a'·C₄(a',b))‖ ≤ ‖C₄(a',b)‖·‖a'‖ ≤ s₁⁴·s/2 ≤ s⁵/2
  have hC₄_s4 : ‖bch_quartic_term 𝕂 a' b‖ ≤ s ^ 4 := by
    calc ‖bch_quartic_term 𝕂 a' b‖ ≤ (‖a'‖ + ‖b‖) ^ 4 := norm_bch_quartic_term_le a' b
      _ = s₁ ^ 4 := by rw [← hs₁_def]
      _ ≤ s ^ 4 := pow_le_pow_left₀ hs₁_nn hs₁_le 4
  have hT4 : ‖(2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' -
      a' * bch_quartic_term 𝕂 a' b)‖ ≤ s ^ 5 := by
    have h2_inv : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
    have hcomm_bound : ‖bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b‖ ≤
        2 * ‖bch_quartic_term 𝕂 a' b‖ * ‖a'‖ := by
      calc ‖bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b‖
          ≤ ‖bch_quartic_term 𝕂 a' b * a'‖ + ‖a' * bch_quartic_term 𝕂 a' b‖ := by
            rw [sub_eq_add_neg]
            exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖bch_quartic_term 𝕂 a' b‖ * ‖a'‖ + ‖a'‖ * ‖bch_quartic_term 𝕂 a' b‖ := by
            gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖bch_quartic_term 𝕂 a' b‖ * ‖a'‖ := by ring
    calc ‖(2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b)‖
        ≤ ‖(2 : 𝕂)⁻¹‖ * ‖bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b‖ :=
          norm_smul_le _ _
      _ = (2 : ℝ)⁻¹ * ‖bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b‖ := by
          rw [h2_inv]
      _ ≤ (2 : ℝ)⁻¹ * (2 * ‖bch_quartic_term 𝕂 a' b‖ * ‖a'‖) :=
          mul_le_mul_of_nonneg_left hcomm_bound (by norm_num)
      _ = ‖bch_quartic_term 𝕂 a' b‖ * ‖a'‖ := by ring
      _ ≤ s ^ 4 * (s / 2) := mul_le_mul hC₄_s4 ha'_s (norm_nonneg _) (by positivity)
      _ ≤ s ^ 5 := by nlinarith [pow_nonneg hs_nn 5, hs_lt]
  -- SETUP for TERMS 5-6: norm bounds for ‖a'+b‖, ‖W‖.
  have hp_s : ‖a' + b‖ ≤ 3 / 2 * s := by
    calc ‖a' + b‖ ≤ ‖a'‖ + ‖b‖ := norm_add_le _ _
      _ ≤ s / 2 + s := by linarith [ha'_s, hb_s]
      _ = 3 / 2 * s := by ring
  have hW_s2 : ‖W‖ ≤ 48 / 11 * s ^ 2 := by
    have hs₁_sq_le : s₁ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs₁_nn hs₁_le 2
    calc ‖W‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) := hW_le
      _ ≤ 3 * s ^ 2 / (11 / 16) := by
          apply div_le_div₀ (by positivity) _ (by norm_num) hdenom_lb
          exact mul_le_mul_of_nonneg_left hs₁_sq_le (by norm_num)
      _ = 48 / 11 * s ^ 2 := by ring
  have hW_nn : (0 : ℝ) ≤ ‖W‖ := norm_nonneg _
  have hp_nn : (0 : ℝ) ≤ ‖a' + b‖ := norm_nonneg _
  -- Commutator norm bounds
  have hcomm_Wa' : ‖W * a' - a' * W‖ ≤ 2 * ‖W‖ * ‖a'‖ := by
    calc ‖W * a' - a' * W‖ ≤ ‖W * a'‖ + ‖a' * W‖ := by
          rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ ‖W‖ * ‖a'‖ + ‖a'‖ * ‖W‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖W‖ * ‖a'‖ := by ring
  have hcomm_pa' : ‖(a' + b) * a' - a' * (a' + b)‖ ≤ 2 * ‖a' + b‖ * ‖a'‖ := by
    calc ‖(a' + b) * a' - a' * (a' + b)‖ ≤ ‖(a' + b) * a'‖ + ‖a' * (a' + b)‖ := by
          rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ ‖a' + b‖ * ‖a'‖ + ‖a'‖ * ‖a' + b‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖a' + b‖ * ‖a'‖ := by ring
  -- TERM 6: Define DC_z - DC_{a'+b} = S6 where S6 is explicit polynomial in (a'+b, W, a').
  set DC_z : 𝔸 := z * (z * a' - a' * z) - (z * a' - a' * z) * z with hDC_z_def
  set DC_p : 𝔸 := (a' + b) * ((a' + b) * a' - a' * (a' + b)) -
      ((a' + b) * a' - a' * (a' + b)) * (a' + b) with hDC_p_def
  set S6 : 𝔸 :=
    ((a' + b) * (W * a' - a' * W) - (W * a' - a' * W) * (a' + b)) +
    (W * ((a' + b) * a' - a' * (a' + b)) - ((a' + b) * a' - a' * (a' + b)) * W) +
    (W * (W * a' - a' * W) - (W * a' - a' * W) * W) with hS6_def
  have hz_eq : z = (a' + b) + W := by rw [hW_def]; abel
  -- Ring identity: DC_z - DC_p = S6 (after z = (a'+b) + W substitution)
  have hDC_diff : DC_z - DC_p = S6 := by
    rw [hDC_z_def, hDC_p_def, hS6_def, hz_eq]; noncomm_ring
  -- bch_quartic_term identity: C₄(z,a') - C₄(a'+b,a') = -(24)⁻¹ • (a' * S6 - S6 * a')
  have hT6_id : bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a' =
      -((24 : 𝕂)⁻¹ • (a' * S6 - S6 * a')) := by
    show -((24 : 𝕂)⁻¹ • (a' * DC_z - DC_z * a')) -
        -((24 : 𝕂)⁻¹ • (a' * DC_p - DC_p * a')) = _
    have hDC_z_eq : DC_z = DC_p + S6 := by
      have h := hDC_diff
      have : DC_z = DC_z - DC_p + DC_p := by abel
      rw [this, h]; abel
    have hinner : a' * DC_z - DC_z * a' - (a' * DC_p - DC_p * a') = a' * S6 - S6 * a' := by
      rw [hDC_z_eq]; noncomm_ring
    calc -((24 : 𝕂)⁻¹ • (a' * DC_z - DC_z * a')) -
          -((24 : 𝕂)⁻¹ • (a' * DC_p - DC_p * a'))
        = (24 : 𝕂)⁻¹ • (a' * DC_p - DC_p * a') -
            (24 : 𝕂)⁻¹ • (a' * DC_z - DC_z * a') := by abel
      _ = (24 : 𝕂)⁻¹ •
            ((a' * DC_p - DC_p * a') - (a' * DC_z - DC_z * a')) := by rw [← smul_sub]
      _ = (24 : 𝕂)⁻¹ •
            (-((a' * DC_z - DC_z * a') - (a' * DC_p - DC_p * a'))) := by rw [neg_sub]
      _ = -((24 : 𝕂)⁻¹ •
            ((a' * DC_z - DC_z * a') - (a' * DC_p - DC_p * a'))) := by rw [smul_neg]
      _ = -((24 : 𝕂)⁻¹ • (a' * S6 - S6 * a')) := by rw [hinner]
  -- Norm bound on S6
  have hS6_bound : ‖S6‖ ≤ 8 * ‖a' + b‖ * ‖W‖ * ‖a'‖ + 4 * ‖W‖ ^ 2 * ‖a'‖ := by
    have h1 : ‖(a' + b) * (W * a' - a' * W) - (W * a' - a' * W) * (a' + b)‖ ≤
        4 * ‖a' + b‖ * ‖W‖ * ‖a'‖ := by
      calc _ ≤ ‖(a' + b) * (W * a' - a' * W)‖ + ‖(W * a' - a' * W) * (a' + b)‖ := by
            rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖a' + b‖ * (2 * ‖W‖ * ‖a'‖) + (2 * ‖W‖ * ‖a'‖) * ‖a' + b‖ := by
            gcongr
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hcomm_Wa' hp_nn)
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hcomm_Wa' hp_nn)
        _ = 4 * ‖a' + b‖ * ‖W‖ * ‖a'‖ := by ring
    have h2 : ‖W * ((a' + b) * a' - a' * (a' + b)) -
        ((a' + b) * a' - a' * (a' + b)) * W‖ ≤ 4 * ‖a' + b‖ * ‖W‖ * ‖a'‖ := by
      calc _ ≤ ‖W * ((a' + b) * a' - a' * (a' + b))‖ +
             ‖((a' + b) * a' - a' * (a' + b)) * W‖ := by
            rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖W‖ * (2 * ‖a' + b‖ * ‖a'‖) + (2 * ‖a' + b‖ * ‖a'‖) * ‖W‖ := by
            gcongr
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hcomm_pa' hW_nn)
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hcomm_pa' hW_nn)
        _ = 4 * ‖a' + b‖ * ‖W‖ * ‖a'‖ := by ring
    have h3 : ‖W * (W * a' - a' * W) - (W * a' - a' * W) * W‖ ≤ 4 * ‖W‖ ^ 2 * ‖a'‖ := by
      calc _ ≤ ‖W * (W * a' - a' * W)‖ + ‖(W * a' - a' * W) * W‖ := by
            rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖W‖ * (2 * ‖W‖ * ‖a'‖) + (2 * ‖W‖ * ‖a'‖) * ‖W‖ := by
            gcongr
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hcomm_Wa' hW_nn)
            · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hcomm_Wa' hW_nn)
        _ = 4 * ‖W‖ ^ 2 * ‖a'‖ := by ring
    calc ‖S6‖ ≤ ‖((a' + b) * (W * a' - a' * W) - (W * a' - a' * W) * (a' + b)) +
                 (W * ((a' + b) * a' - a' * (a' + b)) -
                  ((a' + b) * a' - a' * (a' + b)) * W)‖ +
                ‖W * (W * a' - a' * W) - (W * a' - a' * W) * W‖ := norm_add_le _ _
      _ ≤ ‖(a' + b) * (W * a' - a' * W) - (W * a' - a' * W) * (a' + b)‖ +
          ‖W * ((a' + b) * a' - a' * (a' + b)) -
           ((a' + b) * a' - a' * (a' + b)) * W‖ +
          ‖W * (W * a' - a' * W) - (W * a' - a' * W) * W‖ := by
            linarith [norm_add_le
              ((a' + b) * (W * a' - a' * W) - (W * a' - a' * W) * (a' + b))
              (W * ((a' + b) * a' - a' * (a' + b)) -
               ((a' + b) * a' - a' * (a' + b)) * W)]
      _ ≤ 4 * ‖a' + b‖ * ‖W‖ * ‖a'‖ + 4 * ‖a' + b‖ * ‖W‖ * ‖a'‖ +
          4 * ‖W‖ ^ 2 * ‖a'‖ := by linarith
      _ = 8 * ‖a' + b‖ * ‖W‖ * ‖a'‖ + 4 * ‖W‖ ^ 2 * ‖a'‖ := by ring
  -- TERM 6 norm bound: ‖C₄(z,a') - C₄(a'+b,a')‖ ≤ 2·s⁵
  have hT6 : ‖bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a'‖ ≤ 2 * s ^ 5 := by
    rw [hT6_id]
    have h24_inv : ‖(24 : 𝕂)⁻¹‖ = (24 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
    have hcomm_S6 : ‖a' * S6 - S6 * a'‖ ≤ 2 * ‖a'‖ * ‖S6‖ := by
      calc _ ≤ ‖a' * S6‖ + ‖S6 * a'‖ := by
            rw [sub_eq_add_neg]; exact (norm_add_le _ _).trans (by rw [norm_neg])
        _ ≤ ‖a'‖ * ‖S6‖ + ‖S6‖ * ‖a'‖ := by gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖a'‖ * ‖S6‖ := by ring
    have hS6_nn : (0 : ℝ) ≤ ‖S6‖ := norm_nonneg _
    have ha'_nn : (0 : ℝ) ≤ ‖a'‖ := norm_nonneg _
    have hS6_explicit : ‖S6‖ ≤ 8 * (3/2 * s) * (48/11 * s^2) * (s/2) +
        4 * (48/11 * s^2) ^ 2 * (s/2) := by
      calc ‖S6‖ ≤ 8 * ‖a' + b‖ * ‖W‖ * ‖a'‖ + 4 * ‖W‖ ^ 2 * ‖a'‖ := hS6_bound
        _ ≤ 8 * (3/2 * s) * (48/11 * s^2) * (s/2) + 4 * (48/11 * s^2) ^ 2 * (s/2) := by
            gcongr
    calc ‖-((24 : 𝕂)⁻¹ • (a' * S6 - S6 * a'))‖
        = ‖(24 : 𝕂)⁻¹ • (a' * S6 - S6 * a')‖ := norm_neg _
      _ ≤ ‖(24 : 𝕂)⁻¹‖ * ‖a' * S6 - S6 * a'‖ := norm_smul_le _ _
      _ = (1 / 24) * ‖a' * S6 - S6 * a'‖ := by rw [h24_inv]; ring
      _ ≤ (1 / 24) * (2 * ‖a'‖ * ‖S6‖) := by
          apply mul_le_mul_of_nonneg_left hcomm_S6 (by norm_num)
      _ ≤ (1 / 24) * (2 * (s / 2) *
            (8 * (3/2 * s) * (48/11 * s^2) * (s/2) + 4 * (48/11 * s^2) ^ 2 * (s/2))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul _ hS6_explicit hS6_nn (by positivity)
          apply mul_le_mul_of_nonneg_left ha'_s (by norm_num)
      _ ≤ 2 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5, hs_lt, sq_nonneg s]
  -- TERM 5: C₃(z, a') - C₃(a'+b, a') + (96)⁻¹·[b, DC_a] via cancellation
  set W₂ : 𝔸 := (2 : 𝕂)⁻¹ • (a' * b - b * a') with hW₂_def
  set W_rest : 𝔸 := W - W₂ with hWrest_def
  -- Explicit linear-in-ξ and quadratic-in-ξ polynomials (with p = a'+b)
  -- L(ξ) := ((a'+b)ξ + ξ(a'+b))a' - 2((a'+b)a'ξ + ξa'(a'+b)) + a'((a'+b)ξ + ξ(a'+b))
  --       + a'a'ξ - 2(a'ξa') + ξa'a'
  -- Q(ξ) := ξξa' - 2(ξa'ξ) + a'ξξ
  set L_W : 𝔸 :=
    ((a' + b) * W + W * (a' + b)) * a' -
    ((a' + b) * a' * W + W * a' * (a' + b)) -
    ((a' + b) * a' * W + W * a' * (a' + b)) +
    a' * ((a' + b) * W + W * (a' + b)) +
    a' * a' * W - a' * W * a' - a' * W * a' + W * a' * a' with hL_W_def
  set L_Wrest : 𝔸 :=
    ((a' + b) * W_rest + W_rest * (a' + b)) * a' -
    ((a' + b) * a' * W_rest + W_rest * a' * (a' + b)) -
    ((a' + b) * a' * W_rest + W_rest * a' * (a' + b)) +
    a' * ((a' + b) * W_rest + W_rest * (a' + b)) +
    a' * a' * W_rest - a' * W_rest * a' - a' * W_rest * a' + W_rest * a' * a'
    with hL_Wrest_def
  set L_W2 : 𝔸 :=
    ((a' + b) * W₂ + W₂ * (a' + b)) * a' -
    ((a' + b) * a' * W₂ + W₂ * a' * (a' + b)) -
    ((a' + b) * a' * W₂ + W₂ * a' * (a' + b)) +
    a' * ((a' + b) * W₂ + W₂ * (a' + b)) +
    a' * a' * W₂ - a' * W₂ * a' - a' * W₂ * a' + W₂ * a' * a' with hL_W2_def
  set Q_W : 𝔸 := W * W * a' - W * a' * W - W * a' * W + a' * W * W with hQ_W_def
  -- Identity 1: bch_cubic_term diff = (12)⁻¹•L_W + (12)⁻¹•Q_W
  have hId1 : bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' =
      (12 : 𝕂)⁻¹ • L_W + (12 : 𝕂)⁻¹ • Q_W := by
    rw [hz_eq, hL_W_def, hQ_W_def]
    unfold bch_cubic_term
    simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
      smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
    match_scalars <;> ring
  -- Identity 3: L_W = L_Wrest + L_W2 (linearity in ξ)
  have hId3 : L_W = L_Wrest + L_W2 := by
    rw [hL_W_def, hL_Wrest_def, hL_W2_def, hWrest_def]
    noncomm_ring
  -- Identity 2 (cancellation): (12)⁻¹•L_W2 + (96)⁻¹•(b·DC_a - DC_a·b) = 0
  have hId2 : (12 : 𝕂)⁻¹ • L_W2 + (96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b) = 0 := by
    rw [hL_W2_def, hW₂_def, hDC_a_def, ha'_def]
    simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
      smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
    match_scalars <;> ring
  -- Combine: Term5 = (12)⁻¹•L_Wrest + (12)⁻¹•Q_W
  have hT5_id : bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
        -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b)) =
      (12 : 𝕂)⁻¹ • L_Wrest + (12 : 𝕂)⁻¹ • Q_W := by
    rw [sub_neg_eq_add, hId1, hId3, smul_add]
    have h := hId2
    have rearr :
        (12 : 𝕂)⁻¹ • L_Wrest + (12 : 𝕂)⁻¹ • L_W2 + (12 : 𝕂)⁻¹ • Q_W +
          (96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b) =
        (12 : 𝕂)⁻¹ • L_Wrest + (12 : 𝕂)⁻¹ • Q_W +
          ((12 : 𝕂)⁻¹ • L_W2 + (96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b)) := by abel
    rw [rearr, h, add_zero]
  -- Norm bound on W_rest: W_rest = R₁ + C₃(a',b) + C₄(a',b)
  have hWrest_eq : W_rest = R₁ + bch_cubic_term 𝕂 a' b + bch_quartic_term 𝕂 a' b := by
    rw [hR₁_def]; abel
  have hC₃_ab_le : ‖bch_cubic_term 𝕂 a' b‖ ≤ s ^ 3 := by
    calc _ ≤ (‖a'‖ + ‖b‖) ^ 3 := norm_bch_cubic_term_le a' b
      _ = s₁ ^ 3 := by rw [← hs₁_def]
      _ ≤ s ^ 3 := pow_le_pow_left₀ hs₁_nn hs₁_le 3
  have hWrest_le : ‖W_rest‖ ≤ 5000 * s ^ 5 + s ^ 3 + s ^ 4 := by
    rw [hWrest_eq]
    calc _ ≤ ‖R₁ + bch_cubic_term 𝕂 a' b‖ + ‖bch_quartic_term 𝕂 a' b‖ :=
          norm_add_le _ _
      _ ≤ ‖R₁‖ + ‖bch_cubic_term 𝕂 a' b‖ + ‖bch_quartic_term 𝕂 a' b‖ := by
          linarith [norm_add_le R₁ (bch_cubic_term 𝕂 a' b)]
      _ ≤ 5000 * s ^ 5 + s ^ 3 + s ^ 4 := by linarith [hR₁_s5, hC₃_ab_le, hC₄_s4]
  -- Norm bound on L_Wrest: ≤ 8·‖a'+b‖·‖a'‖·‖W_rest‖ + 4·‖a'‖²·‖W_rest‖
  have hL_Wrest_bound : ‖L_Wrest‖ ≤
      8 * ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ + 4 * ‖a'‖ ^ 2 * ‖W_rest‖ := by
    rw [hL_Wrest_def]
    -- L_Wrest = A + a'*(...) + a'a'W_rest - a'W_rest a' - a'W_rest a' + W_rest a' a'
    -- where A = ((a'+b)*W_rest + W_rest*(a'+b))*a' - 2((a'+b)a'W_rest + W_rest a'(a'+b))
    -- We'll use a series of norm_add_le triangulations.
    have ha'_nn : (0 : ℝ) ≤ ‖a'‖ := norm_nonneg _
    have hWrest_nn : (0 : ℝ) ≤ ‖W_rest‖ := norm_nonneg _
    -- Key mini-bounds:
    have e1 : ‖((a' + b) * W_rest + W_rest * (a' + b)) * a'‖ ≤
        2 * ‖a' + b‖ * ‖W_rest‖ * ‖a'‖ := by
      calc _ ≤ ‖(a' + b) * W_rest + W_rest * (a' + b)‖ * ‖a'‖ := norm_mul_le _ _
        _ ≤ (‖(a' + b) * W_rest‖ + ‖W_rest * (a' + b)‖) * ‖a'‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ (‖a' + b‖ * ‖W_rest‖ + ‖W_rest‖ * ‖a' + b‖) * ‖a'‖ := by
            gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖a' + b‖ * ‖W_rest‖ * ‖a'‖ := by ring
    have e2 : ‖(a' + b) * a' * W_rest + W_rest * a' * (a' + b)‖ ≤
        2 * ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ := by
      calc _ ≤ ‖(a' + b) * a' * W_rest‖ + ‖W_rest * a' * (a' + b)‖ := norm_add_le _ _
        _ ≤ ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ + ‖W_rest‖ * ‖a'‖ * ‖a' + b‖ := by
            gcongr
            · exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) hWrest_nn)
            · exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) hp_nn)
        _ = 2 * ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ := by ring
    have e3 : ‖a' * ((a' + b) * W_rest + W_rest * (a' + b))‖ ≤
        2 * ‖a' + b‖ * ‖W_rest‖ * ‖a'‖ := by
      calc _ ≤ ‖a'‖ * ‖(a' + b) * W_rest + W_rest * (a' + b)‖ := norm_mul_le _ _
        _ ≤ ‖a'‖ * (‖(a' + b) * W_rest‖ + ‖W_rest * (a' + b)‖) := by
            gcongr; exact norm_add_le _ _
        _ ≤ ‖a'‖ * (‖a' + b‖ * ‖W_rest‖ + ‖W_rest‖ * ‖a' + b‖) := by
            gcongr <;> exact norm_mul_le _ _
        _ = 2 * ‖a' + b‖ * ‖W_rest‖ * ‖a'‖ := by ring
    have e4 : ‖a' * a' * W_rest‖ ≤ ‖a'‖ ^ 2 * ‖W_rest‖ := by
      calc _ ≤ ‖a' * a'‖ * ‖W_rest‖ := norm_mul_le _ _
        _ ≤ (‖a'‖ * ‖a'‖) * ‖W_rest‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖a'‖ ^ 2 * ‖W_rest‖ := by ring
    have e5 : ‖a' * W_rest * a'‖ ≤ ‖a'‖ ^ 2 * ‖W_rest‖ := by
      calc _ ≤ ‖a' * W_rest‖ * ‖a'‖ := norm_mul_le _ _
        _ ≤ ‖a'‖ * ‖W_rest‖ * ‖a'‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖a'‖ ^ 2 * ‖W_rest‖ := by ring
    have e6 : ‖W_rest * a' * a'‖ ≤ ‖a'‖ ^ 2 * ‖W_rest‖ := by
      calc _ ≤ ‖W_rest * a'‖ * ‖a'‖ := norm_mul_le _ _
        _ ≤ (‖W_rest‖ * ‖a'‖) * ‖a'‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖a'‖ ^ 2 * ‖W_rest‖ := by ring
    -- Rewrite the L_Wrest expression as a pure sum (replace - with +(-))
    set X1 : 𝔸 := ((a' + b) * W_rest + W_rest * (a' + b)) * a' with hX1
    set X2 : 𝔸 := (a' + b) * a' * W_rest + W_rest * a' * (a' + b) with hX2
    set X3 : 𝔸 := a' * ((a' + b) * W_rest + W_rest * (a' + b)) with hX3
    set X4 : 𝔸 := a' * a' * W_rest with hX4
    set X5 : 𝔸 := a' * W_rest * a' with hX5
    set X6 : 𝔸 := W_rest * a' * a' with hX6
    have hsum_eq : X1 - X2 - X2 + X3 + X4 - X5 - X5 + X6 =
        X1 + -X2 + -X2 + X3 + X4 + -X5 + -X5 + X6 := by abel
    calc ‖X1 - X2 - X2 + X3 + X4 - X5 - X5 + X6‖
        = ‖X1 + -X2 + -X2 + X3 + X4 + -X5 + -X5 + X6‖ := by rw [hsum_eq]
      _ ≤ ‖X1‖ + ‖X2‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ + ‖X5‖ + ‖X5‖ + ‖X6‖ := by
          have a7 := norm_add_le (X1 + -X2 + -X2 + X3 + X4 + -X5 + -X5) X6
          have a6 := norm_add_le (X1 + -X2 + -X2 + X3 + X4 + -X5) (-X5)
          have a5 := norm_add_le (X1 + -X2 + -X2 + X3 + X4) (-X5)
          have a4 := norm_add_le (X1 + -X2 + -X2 + X3) X4
          have a3 := norm_add_le (X1 + -X2 + -X2) X3
          have a2 := norm_add_le (X1 + -X2) (-X2)
          have a1 := norm_add_le X1 (-X2)
          simp only [norm_neg] at a1 a2 a5 a6
          linarith
      _ ≤ 2 * ‖a' + b‖ * ‖W_rest‖ * ‖a'‖ +
          2 * ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ +
          2 * ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ +
          2 * ‖a' + b‖ * ‖W_rest‖ * ‖a'‖ +
          ‖a'‖ ^ 2 * ‖W_rest‖ + ‖a'‖ ^ 2 * ‖W_rest‖ + ‖a'‖ ^ 2 * ‖W_rest‖ +
          ‖a'‖ ^ 2 * ‖W_rest‖ := by linarith [e1, e2, e3, e4, e5, e6]
      _ = 8 * ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ + 4 * ‖a'‖ ^ 2 * ‖W_rest‖ := by ring
  -- Norm bound on Q_W: ≤ 4·‖W‖²·‖a'‖
  have hQ_W_bound : ‖Q_W‖ ≤ 4 * ‖W‖ ^ 2 * ‖a'‖ := by
    rw [hQ_W_def]
    have q1 : ‖W * W * a'‖ ≤ ‖W‖ ^ 2 * ‖a'‖ := by
      calc _ ≤ ‖W * W‖ * ‖a'‖ := norm_mul_le _ _
        _ ≤ (‖W‖ * ‖W‖) * ‖a'‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖W‖ ^ 2 * ‖a'‖ := by ring
    have q2 : ‖W * a' * W‖ ≤ ‖W‖ ^ 2 * ‖a'‖ := by
      calc _ ≤ ‖W * a'‖ * ‖W‖ := norm_mul_le _ _
        _ ≤ (‖W‖ * ‖a'‖) * ‖W‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖W‖ ^ 2 * ‖a'‖ := by ring
    have q3 : ‖a' * W * W‖ ≤ ‖W‖ ^ 2 * ‖a'‖ := by
      calc _ ≤ ‖a' * W‖ * ‖W‖ := norm_mul_le _ _
        _ ≤ (‖a'‖ * ‖W‖) * ‖W‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖W‖ ^ 2 * ‖a'‖ := by ring
    calc ‖W * W * a' - W * a' * W - W * a' * W + a' * W * W‖
        ≤ ‖W * W * a'‖ + ‖W * a' * W‖ + ‖W * a' * W‖ + ‖a' * W * W‖ := by
          have h : W * W * a' - W * a' * W - W * a' * W + a' * W * W =
              W * W * a' + -(W * a' * W) + -(W * a' * W) + a' * W * W := by abel
          rw [h]
          have a3 := norm_add_le (W * W * a' + -(W * a' * W) + -(W * a' * W)) (a' * W * W)
          have a2 := norm_add_le (W * W * a' + -(W * a' * W)) (-(W * a' * W))
          have a1 := norm_add_le (W * W * a') (-(W * a' * W))
          simp only [norm_neg] at a1 a2
          linarith
      _ ≤ ‖W‖ ^ 2 * ‖a'‖ + ‖W‖ ^ 2 * ‖a'‖ + ‖W‖ ^ 2 * ‖a'‖ + ‖W‖ ^ 2 * ‖a'‖ := by
          linarith
      _ = 4 * ‖W‖ ^ 2 * ‖a'‖ := by ring
  -- TERM 5 total bound: ≤ 500·s⁵
  have hT5 : ‖bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
      -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))‖ ≤ 500 * s ^ 5 := by
    rw [hT5_id]
    have h12_inv : ‖(12 : 𝕂)⁻¹‖ = (12 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
    -- ‖(12)⁻¹ • L_Wrest‖ ≤ (1/12) · (8·(3s/2)·(s/2)·‖W_rest‖ + 4·(s/2)²·‖W_rest‖)
    -- ≤ (1/12) · (6s²·‖W_rest‖ + s²·‖W_rest‖) = (7/12)·s²·‖W_rest‖
    -- With ‖W_rest‖ ≤ 5000·s⁵ + s³ + s⁴:
    -- (7/12)·s²·(5000·s⁵ + s³ + s⁴) = (7/12)·(5000·s⁷ + s⁵ + s⁶)
    -- For s ≤ 1/4: s⁷ ≤ s⁵/16, s⁶ ≤ s⁵/4
    -- = (7/12) · (5000/16 + 1 + 1/4) · s⁵ = (7/12) · (312.5 + 1.25) · s⁵ ≈ 183·s⁵
    have hL_Wrest_s : ‖L_Wrest‖ ≤ 7 * s ^ 2 * ‖W_rest‖ := by
      have hWrest_nn : (0 : ℝ) ≤ ‖W_rest‖ := norm_nonneg _
      calc ‖L_Wrest‖ ≤ 8 * ‖a' + b‖ * ‖a'‖ * ‖W_rest‖ + 4 * ‖a'‖ ^ 2 * ‖W_rest‖ :=
            hL_Wrest_bound
        _ ≤ 8 * (3 / 2 * s) * (s / 2) * ‖W_rest‖ + 4 * (s / 2) ^ 2 * ‖W_rest‖ := by
            gcongr
        _ = 6 * s ^ 2 * ‖W_rest‖ + s ^ 2 * ‖W_rest‖ := by ring
        _ = 7 * s ^ 2 * ‖W_rest‖ := by ring
    have hL_Wrest_final : (12 : ℝ)⁻¹ * ‖L_Wrest‖ ≤ 250 * s ^ 5 := by
      calc (12 : ℝ)⁻¹ * ‖L_Wrest‖
          ≤ (12 : ℝ)⁻¹ * (7 * s ^ 2 * ‖W_rest‖) := by
            apply mul_le_mul_of_nonneg_left hL_Wrest_s (by norm_num)
        _ ≤ (12 : ℝ)⁻¹ * (7 * s ^ 2 * (5000 * s ^ 5 + s ^ 3 + s ^ 4)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hWrest_le (by positivity)
        _ ≤ 250 * s ^ 5 := by
            have h5 : (0:ℝ) ≤ s ^ 5 := pow_nonneg hs_nn 5
            have hle : s ≤ 1/4 := by linarith
            have s7_le : s^7 ≤ s^5 * (1/16) := by
              have hrew : s^7 = s^2 * s^5 := by ring
              rw [hrew]
              have hs2 : s^2 ≤ 1/16 := by nlinarith [hle, hs_nn]
              nlinarith [hs2, h5]
            have s6_le : s^6 ≤ s^5 * (1/4) := by
              have hrew : s^6 = s * s^5 := by ring
              rw [hrew]
              nlinarith [hle, h5, hs_nn]
            have expand : (12:ℝ)⁻¹ * (7 * s^2 * (5000 * s^5 + s^3 + s^4)) =
                         (35000/12) * s^7 + (7/12) * s^5 + (7/12) * s^6 := by ring
            rw [expand]
            nlinarith [s7_le, s6_le, h5]
    have hQ_W_s : ‖Q_W‖ ≤ 4 * (48 / 11 * s ^ 2) ^ 2 * (s / 2) := by
      have hW2_nn : (0 : ℝ) ≤ ‖W‖ ^ 2 := sq_nonneg _
      calc ‖Q_W‖ ≤ 4 * ‖W‖ ^ 2 * ‖a'‖ := hQ_W_bound
        _ ≤ 4 * (48 / 11 * s ^ 2) ^ 2 * (s / 2) := by
            gcongr
    have hQ_W_final : (12 : ℝ)⁻¹ * ‖Q_W‖ ≤ 250 * s ^ 5 := by
      calc (12 : ℝ)⁻¹ * ‖Q_W‖
          ≤ (12 : ℝ)⁻¹ * (4 * (48 / 11 * s ^ 2) ^ 2 * (s / 2)) := by
            apply mul_le_mul_of_nonneg_left hQ_W_s (by norm_num)
        _ ≤ 250 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5, hs_lt]
    calc ‖(12 : 𝕂)⁻¹ • L_Wrest + (12 : 𝕂)⁻¹ • Q_W‖
        ≤ ‖(12 : 𝕂)⁻¹ • L_Wrest‖ + ‖(12 : 𝕂)⁻¹ • Q_W‖ := norm_add_le _ _
      _ ≤ ‖(12 : 𝕂)⁻¹‖ * ‖L_Wrest‖ + ‖(12 : 𝕂)⁻¹‖ * ‖Q_W‖ := by
          gcongr <;> exact norm_smul_le _ _
      _ = (12 : ℝ)⁻¹ * ‖L_Wrest‖ + (12 : ℝ)⁻¹ * ‖Q_W‖ := by rw [h12_inv]
      _ ≤ 250 * s ^ 5 + 250 * s ^ 5 := by linarith
      _ = 500 * s ^ 5 := by ring
  -- TRIANGLE INEQUALITY: sum the 6 bounds
  set T₁ := R₁ with hT₁
  set T₂ := R₂ with hT₂
  set T₃ := (2 : 𝕂)⁻¹ • (R₁ * a' - a' * R₁) with hT₃
  set T₄ := (2 : 𝕂)⁻¹ • (bch_quartic_term 𝕂 a' b * a' - a' * bch_quartic_term 𝕂 a' b)
    with hT₄
  set T₅ := bch_cubic_term 𝕂 z a' - bch_cubic_term 𝕂 (a' + b) a' -
        -((96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b)) with hT₅
  set T₆ := bch_quartic_term 𝕂 z a' - bch_quartic_term 𝕂 (a' + b) a' with hT₆
  have hsum_le : ‖T₁ + T₂ + T₃ + T₄ + T₅ + T₆‖ ≤
      ‖T₁‖ + ‖T₂‖ + ‖T₃‖ + ‖T₄‖ + ‖T₅‖ + ‖T₆‖ := by
    have a5 := norm_add_le (T₁ + T₂ + T₃ + T₄ + T₅) T₆
    have a4 := norm_add_le (T₁ + T₂ + T₃ + T₄) T₅
    have a3 := norm_add_le (T₁ + T₂ + T₃) T₄
    have a2 := norm_add_le (T₁ + T₂) T₃
    have a1 := norm_add_le T₁ T₂
    linarith
  calc ‖T₁ + T₂ + T₃ + T₄ + T₅ + T₆‖
      ≤ ‖T₁‖ + ‖T₂‖ + ‖T₃‖ + ‖T₄‖ + ‖T₅‖ + ‖T₆‖ := hsum_le
    _ ≤ 5000 * s ^ 5 + 5000000 * s ^ 5 + 1000 * s ^ 5 + s ^ 5 + 500 * s ^ 5 +
        2 * s ^ 5 := by linarith [hR₁_s5, hR₂_s5, hT3, hT4, hT5, hT6]
    _ = 5006503 * s ^ 5 := by ring
    _ ≤ 10000000 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]


/-! ### Phase A scaffolding for the τ⁵ symmetric-BCH discharge (T2-F7e)

The two private lemmas below mirror the cubic template's R₁/R₂ setup at one
degree higher, packaging `norm_bch_septic_remainder_le` together with the
standard `s₁ ≤ s` and `s₂ := ‖z‖ + ‖a'‖ ≤ (57/22)·s` bounds (where
`a' := ½a`, `z := bch(a', b)`).

They are reused by the eventual `norm_symmetric_bch_quintic_sub_poly_le`
proof (replacing the parent Tier-2 axiom in `SymmetricQuintic.lean`).
-/

set_option maxHeartbeats 800000 in
include 𝕂 in
/-- **Inner BCH septic remainder bound** (T2-F7e Phase A): the inner-BCH leg of
the symmetric BCH composition `bch(bch(½a, b), ½a)`, after subtracting the
explicit through-deg-6 expansion at `(½a, b)`, satisfies an `O(s⁷)` bound for
`s = ‖a‖ + ‖b‖ < 1/4`.

Direct application of `norm_bch_septic_remainder_le` to `(½a, b)` plus the
standard `s₁ := ‖½a‖ + ‖b‖ ≤ s` and `2 - exp(s₁) ≥ 11/16` (from `s₁ ≤ 1/4`).
The bound constant `1500000` is chosen to absorb `1000010·(16/11) ≈ 1454560`
with small margin. -/
theorem norm_bch_inner_septic_remainder_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b - ((2 : 𝕂)⁻¹ • a + b) -
      (2 : 𝕂)⁻¹ • ((2 : 𝕂)⁻¹ • a * b - b * ((2 : 𝕂)⁻¹ • a)) -
      bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b -
      bch_quartic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b -
      bch_quintic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b -
      bch_sextic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b‖ ≤
      1500000 * (‖a‖ + ‖b‖) ^ 7 := by
  set a' : 𝔸 := (2 : 𝕂)⁻¹ • a with ha'_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set s₁ := ‖a'‖ + ‖b‖ with hs₁_def
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ ‖a‖ / 2 := by
    calc ‖a'‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt : s < 1 / 4 := hab
  have hs₁_le : s₁ ≤ s := by
    show ‖a'‖ + ‖b‖ ≤ ‖a‖ + ‖b‖; linarith [ha'_le, norm_nonneg a]
  have hs₁_nn : 0 ≤ s₁ := by positivity
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
  -- Apply norm_bch_septic_remainder_le at (a', b).
  have hR_sept_le :
      ‖bch (𝕂 := 𝕂) a' b - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a') -
        bch_cubic_term 𝕂 a' b - bch_quartic_term 𝕂 a' b -
        bch_quintic_term 𝕂 a' b - bch_sextic_term 𝕂 a' b‖ ≤
        1000010 * s₁ ^ 7 / (2 - Real.exp s₁) :=
    norm_bch_septic_remainder_le (𝕂 := 𝕂) a' b hs₁_lt_log2
  -- Convert to s⁷ bound.
  have hX_s7 : 1000010 * s₁ ^ 7 / (2 - Real.exp s₁) ≤ 1500000 * s ^ 7 := by
    rw [div_le_iff₀ hdenom₁]
    have hs_pow : s₁ ^ 7 ≤ s ^ 7 := pow_le_pow_left₀ hs₁_nn hs₁_le 7
    have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
    nlinarith [hdenom_lb, hs_pow, hs7_nn]
  linarith

set_option maxHeartbeats 1600000 in
include 𝕂 in
/-- **Outer BCH septic remainder bound** (T2-F7e Phase A): the outer-BCH leg of
the symmetric BCH composition `bch(z, ½a)` where `z := bch(½a, b)`, after
subtracting the explicit through-deg-6 expansion at `(z, ½a)`, satisfies an
`O(s⁷)` bound for `s = ‖a‖ + ‖b‖ < 1/4`.

Uses the standard outer-radius bound `s₂ := ‖z‖ + ‖½a‖ ≤ (57/22)·s` (from
`‖z‖ ≤ (23/11)·s`) together with `s₂ ≤ 57/88` and `2 - exp(57/88) ≥ 1/12`
(via `Real.exp_bound'`). The bound constant `12000000000 = 1.2·10¹⁰` is
chosen to absorb `1000010·(57/22)^7·12 ≈ 9.41·10⁹` with comfortable margin. -/
theorem norm_bch_outer_septic_remainder_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) -
      (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b + (2 : 𝕂)⁻¹ • a) -
      (2 : 𝕂)⁻¹ • (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b * ((2 : 𝕂)⁻¹ • a) -
                   ((2 : 𝕂)⁻¹ • a) * bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) -
      bch_cubic_term 𝕂 (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) -
      bch_quartic_term 𝕂 (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) -
      bch_quintic_term 𝕂 (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) -
      bch_sextic_term 𝕂 (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a)‖ ≤
      12000000000 * (‖a‖ + ‖b‖) ^ 7 := by
  set a' : 𝔸 := (2 : 𝕂)⁻¹ • a with ha'_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set s₁ := ‖a'‖ + ‖b‖ with hs₁_def
  set z := bch (𝕂 := 𝕂) a' b with hz_def
  -- Standard scaffolding (mirrors cubic template).
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ ‖a‖ / 2 := by
    calc ‖a'‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  have ha'_le_s : ‖a'‖ ≤ s := by
    calc ‖a'‖ ≤ ‖a‖ / 2 := ha'_le
      _ ≤ ‖a‖ := by linarith [norm_nonneg a]
      _ ≤ s := le_add_of_nonneg_right (norm_nonneg b)
  have ha'_s : ‖a'‖ ≤ s / 2 := by
    calc ‖a'‖ ≤ ‖a‖ / 2 := ha'_le
      _ ≤ s / 2 := by linarith [norm_nonneg b]
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt : s < 1 / 4 := hab
  have hs1 : s < 1 := by linarith
  have hs₁_le : s₁ ≤ s := by
    show ‖a'‖ + ‖b‖ ≤ ‖a‖ + ‖b‖; linarith [ha'_le, norm_nonneg a]
  have hs₁_nn : 0 ≤ s₁ := by positivity
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
  have hquad_bound : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 3 / 11 := by
    rw [div_le_div_iff₀ hdenom₁ (by norm_num : (0:ℝ) < 11)]
    nlinarith [sq_nonneg s₁, sq_nonneg (1/4 - s₁)]
  have hW_le : ‖z - (a' + b)‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    rw [hz_def]; exact norm_bch_sub_add_le (𝕂 := 𝕂) a' b hs₁_lt_log2
  have hz_le : ‖z‖ ≤ s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    calc ‖z‖ = ‖(z - (a' + b)) + (a' + b)‖ := by congr 1; abel
      _ ≤ ‖z - (a' + b)‖ + ‖a' + b‖ := norm_add_le _ _
      _ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) + s₁ := by
          have hsum : ‖a' + b‖ ≤ s₁ := norm_add_le _ _
          linarith
      _ = s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by ring
  have hln2_611 : (6 : ℝ) / 11 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    linarith [real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 6/11)
      (by norm_num : (6:ℝ)/11 < 5/6)]
  have hs₂_lt_log2 : ‖z‖ + ‖a'‖ < Real.log 2 := by
    calc ‖z‖ + ‖a'‖ ≤ (s₁ + 3 / 11) + ‖a'‖ := by linarith [hz_le, hquad_bound]
      _ ≤ s + 3 / 11 := by linarith [ha'_le_s]
      _ < 1/4 + 3 / 11 := by linarith
      _ = 23 / 44 := by norm_num
      _ < 6 / 11 := by norm_num
      _ < Real.log 2 := hln2_611
  -- s₂ ≤ 57/22 · s, the key tightness bound.
  have hz_mult : ‖z‖ ≤ 23/11 * s := by
    have h1 : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 12 * s / 11 := by
      rw [div_le_iff₀ hdenom₁]
      nlinarith [hdenom_lb, hs₁_nn, sq_nonneg s₁, hs₁_le, hs_nn,
        mul_nonneg hs₁_nn hs_nn, hab]
    calc ‖z‖ ≤ s₁ + 3 * s₁ ^ 2 / (2 - Real.exp s₁) := hz_le
      _ ≤ s + 12 * s / 11 := by linarith
      _ = 23/11 * s := by ring
  have hs₂_mult : ‖z‖ + ‖a'‖ ≤ 57/22 * s := by
    calc ‖z‖ + ‖a'‖ ≤ 23/11 * s + s/2 := by linarith [hz_mult, ha'_s]
      _ = 57/22 * s := by ring
  have hs₂_le_const : ‖z‖ + ‖a'‖ ≤ 57 / 88 := by
    calc ‖z‖ + ‖a'‖ ≤ 57/22 * s := hs₂_mult
      _ ≤ 57/22 * (1/4) := by
          have h_step : s ≤ 1/4 := by linarith
          have h_pos : (0:ℝ) ≤ 57/22 := by norm_num
          nlinarith
      _ = 57 / 88 := by ring
  have hdenom₂_pos : 0 < 2 - Real.exp (‖z‖ + ‖a'‖) := by
    have hexp2_lt : Real.exp (‖z‖ + ‖a'‖) < 2 := by
      calc _ < Real.exp (Real.log 2) := Real.exp_strictMono hs₂_lt_log2
        _ = 2 := Real.exp_log (by norm_num)
    linarith
  -- Tight denom bound via Real.exp_bound' (6th-order Taylor): exp(57/88) ≤ 23/12.
  have hexp_57 : Real.exp (57/88) ≤ 23 / 12 := by
    have h := Real.exp_bound' (show (0:ℝ) ≤ 57/88 by norm_num)
      (show (57:ℝ)/88 ≤ 1 by norm_num) (show 0 < 6 by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
      pow_zero, pow_succ, zero_add] at h
    nlinarith [h, sq_nonneg ((57:ℝ)/88)]
  have hexp_s₂_le : Real.exp (‖z‖ + ‖a'‖) ≤ Real.exp (57/88) :=
    Real.exp_monotone hs₂_le_const
  have hdenom₂_lb : (1 : ℝ) / 12 ≤ 2 - Real.exp (‖z‖ + ‖a'‖) := by
    linarith [hexp_s₂_le, hexp_57]
  -- Apply norm_bch_septic_remainder_le at (z, a').
  have hR_sept :
      ‖bch (𝕂 := 𝕂) z a' - (z + a') - (2 : 𝕂)⁻¹ • (z * a' - a' * z) -
        bch_cubic_term 𝕂 z a' - bch_quartic_term 𝕂 z a' -
        bch_quintic_term 𝕂 z a' - bch_sextic_term 𝕂 z a'‖ ≤
        1000010 * (‖z‖ + ‖a'‖) ^ 7 / (2 - Real.exp (‖z‖ + ‖a'‖)) :=
    norm_bch_septic_remainder_le (𝕂 := 𝕂) z a' hs₂_lt_log2
  -- Convert to s⁷.
  -- Numerical: (57/22)^7 ≈ 783.7 ≤ 784. So (‖z‖+‖a'‖)^7 ≤ 784·s^7.
  -- Combined with 1/(2-exp s₂) ≤ 12: 1000010·784·12 ≈ 9.41·10⁹ ≤ 1.2·10¹⁰.
  have h_pow_57 : (‖z‖ + ‖a'‖) ^ 7 ≤ 784 * s ^ 7 := by
    have h1 : (‖z‖ + ‖a'‖) ^ 7 ≤ (57/22 * s) ^ 7 :=
      pow_le_pow_left₀ (by positivity) hs₂_mult 7
    have h2 : (57/22 * s) ^ 7 = (57/22 : ℝ) ^ 7 * s ^ 7 := by ring
    have h3 : ((57 : ℝ) / 22) ^ 7 ≤ 784 := by norm_num
    have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
    calc (‖z‖ + ‖a'‖) ^ 7 ≤ (57/22 * s) ^ 7 := h1
      _ = ((57 : ℝ) / 22) ^ 7 * s ^ 7 := h2
      _ ≤ 784 * s ^ 7 := by nlinarith [h3, hs7_nn]
  have hX_s7 : 1000010 * (‖z‖ + ‖a'‖) ^ 7 / (2 - Real.exp (‖z‖ + ‖a'‖)) ≤
              12000000000 * s ^ 7 := by
    rw [div_le_iff₀ hdenom₂_pos]
    have hs7_nn : (0 : ℝ) ≤ s ^ 7 := pow_nonneg hs_nn 7
    nlinarith [hdenom₂_lb, h_pow_57, hs7_nn]
  linarith


include 𝕂 in
/-- **Quintic remainder for symmetric BCH**: `E₃(c·a, c·b) - c³·E₃(a,b)` is `O(|c|³·s⁵)`.

The `|c|³·s⁵` bound suffices for Suzuki's cancellation: when `Σᵢ cᵢ³ = 0`, the sum
`Σᵢ E₃(cᵢ·a, cᵢ·b) = Σᵢ (E₃(cᵢ·a,cᵢ·b) - cᵢ³·E₃(a,b))` is `O(s⁵)`.

The proof requires establishing that the symmetric BCH is an *odd function* of `(a,b)`:
`bch(bch(-a/2,-b),-a/2) = -bch(bch(a/2,b),a/2)`. This follows from the triple product
identity `exp(a/2)exp(b)exp(a/2) · exp(-a/2)exp(-b)exp(-a/2) = 1`, combined with
commutativity of `logOnePlus(y)` and `logOnePlus((1+y)⁻¹-1)` (both are power series
in `y`) and a chain-of-neighborhoods argument similar to `logOnePlus_exp_sub_one`.
The oddness kills all even-degree Taylor coefficients, so extracting the cubic term
`bch_cubic_term` (degree-3 homogeneous) leaves a quintic+ remainder. -/
theorem norm_symmetric_bch_cubic_sub_smul_le (a b : 𝔸) (c : ℝ)
    (hc : |c| ≤ 1) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 ((↑c : 𝕂) • a) ((↑c : 𝕂) • b) -
      (↑c : 𝕂) ^ 3 • symmetric_bch_cubic 𝕂 a b‖ ≤
      20000000 * |c| ^ 3 * (‖a‖ + ‖b‖) ^ 5 := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs14 : s < 1 / 4 := hab
  -- Key fact: ‖c • a‖ + ‖c • b‖ = |c| · s ≤ s < 1/4
  have hnorm_scale : ‖((↑c : 𝕂) • a)‖ + ‖((↑c : 𝕂) • b)‖ ≤ |c| * s := by
    have hc_norm : ‖(↑c : 𝕂)‖ = |c| := by
      rw [RCLike.norm_ofReal]
    calc ‖((↑c : 𝕂) • a)‖ + ‖((↑c : 𝕂) • b)‖
        ≤ ‖(↑c : 𝕂)‖ * ‖a‖ + ‖(↑c : 𝕂)‖ * ‖b‖ := by
          gcongr <;> exact norm_smul_le _ _
      _ = |c| * s := by rw [hc_norm]; ring
  have hc_nn : 0 ≤ |c| := abs_nonneg c
  have hcs_lt : |c| * s < 1 / 4 := by
    calc |c| * s ≤ 1 * s := by gcongr
      _ = s := one_mul s
      _ < 1 / 4 := hs14
  have hcs_14 : ‖((↑c : 𝕂) • a)‖ + ‖((↑c : 𝕂) • b)‖ < 1 / 4 :=
    lt_of_le_of_lt hnorm_scale hcs_lt
  -- H2 bound on E₃(ca,cb) and on E₃(a,b)
  have h_E3_ca : ‖symmetric_bch_cubic 𝕂 ((↑c : 𝕂) • a) ((↑c : 𝕂) • b)‖ ≤
      300 * (|c| * s) ^ 3 := by
    calc _ ≤ 300 * (‖((↑c : 𝕂) • a)‖ + ‖((↑c : 𝕂) • b)‖) ^ 3 :=
          norm_symmetric_bch_cubic_le (𝕂 := 𝕂) _ _ hcs_14
      _ ≤ 300 * (|c| * s) ^ 3 := by gcongr
  have h_E3_ab : ‖symmetric_bch_cubic 𝕂 a b‖ ≤ 300 * s ^ 3 :=
    norm_symmetric_bch_cubic_le (𝕂 := 𝕂) a b hab
  -- Crude bound: ‖D(c)‖ ≤ 600 |c|³ s³
  have h_crude : ‖symmetric_bch_cubic 𝕂 ((↑c : 𝕂) • a) ((↑c : 𝕂) • b) -
      (↑c : 𝕂) ^ 3 • symmetric_bch_cubic 𝕂 a b‖ ≤ 600 * |c| ^ 3 * s ^ 3 := by
    have hsmul_norm : ‖(↑c : 𝕂) ^ 3 • symmetric_bch_cubic 𝕂 a b‖ ≤
        |c| ^ 3 * (300 * s ^ 3) := by
      have : ‖((↑c : 𝕂) ^ 3)‖ = |c| ^ 3 := by
        rw [norm_pow, RCLike.norm_ofReal]
      calc _ ≤ ‖((↑c : 𝕂) ^ 3)‖ * ‖symmetric_bch_cubic 𝕂 a b‖ := norm_smul_le _ _
        _ ≤ |c| ^ 3 * (300 * s ^ 3) := by rw [this]; gcongr
    calc ‖_‖ ≤ _ + _ := norm_sub_le _ _
      _ ≤ 300 * (|c| * s) ^ 3 + |c| ^ 3 * (300 * s ^ 3) := by linarith
      _ = 600 * |c| ^ 3 * s ^ 3 := by ring
  -- Case split on s² vs 6/100
  by_cases hs_large : 6 / 100 ≤ s ^ 2
  · -- Large s case: crude bound 600·|c|³·s³ ≤ 20·10⁶·|c|³·s⁵ when s² ≥ 0.06
    have h600 : 600 * |c| ^ 3 * s ^ 3 ≤ 20000000 * |c| ^ 3 * s ^ 5 := by
      have hc3_nn : 0 ≤ |c| ^ 3 := pow_nonneg hc_nn 3
      have hs3_nn : 0 ≤ s ^ 3 := pow_nonneg hs_nn 3
      have h1 : 600 * s ^ 3 ≤ 20000000 * s ^ 5 := by
        -- s² ≥ 0.06 ⇒ 20000000·s² ≥ 1200000 ≥ 600
        have hdiff : 20000000 * s ^ 5 - 600 * s ^ 3 = s ^ 3 * (20000000 * s ^ 2 - 600) := by ring
        have h2 : 0 ≤ 20000000 * s ^ 2 - 600 := by linarith
        nlinarith [mul_nonneg hs3_nn h2]
      nlinarith [h1, hc3_nn]
    linarith
  · -- Small s case: s² < 0.06. Use the symmetric quintic remainder bound.
    push_neg at hs_large
    -- Decomposition:
    --   D(c) = [sym_bch_cubic(ca,cb) - sym_E₃(ca,cb)]
    --        + [sym_E₃(ca,cb) - c³·sym_E₃(a,b)]            -- ZERO by homogeneity
    --        + c³·[sym_E₃(a,b) - sym_bch_cubic(a,b)]
    -- Bounds:  ≤ 10⁷·(|c|s)⁵ + 0 + |c|³·10⁷·s⁵ ≤ 2·10⁷·|c|³·s⁵.
    -- Set c' = (↑c : 𝕂)
    set c' : 𝕂 := (↑c : 𝕂) with hc'_def
    have hc'_norm : ‖c'‖ = |c| := by rw [hc'_def, RCLike.norm_ofReal]
    -- Term 1: ‖sym_bch_cubic(c'•a, c'•b) - sym_E₃(c'•a, c'•b)‖ ≤ 10⁷·(|c|s)⁵
    have hT1 : ‖symmetric_bch_cubic 𝕂 (c' • a) (c' • b) -
        symmetric_bch_cubic_poly 𝕂 (c' • a) (c' • b)‖ ≤ 10000000 * (|c| * s) ^ 5 := by
      calc _ ≤ 10000000 * (‖c' • a‖ + ‖c' • b‖) ^ 5 :=
            norm_symmetric_bch_cubic_sub_poly_le (𝕂 := 𝕂) _ _ hcs_14
        _ ≤ 10000000 * (|c| * s) ^ 5 := by gcongr
    -- Homogeneity: sym_E₃(c'•a, c'•b) = c'³ • sym_E₃(a, b)
    have hhom : symmetric_bch_cubic_poly 𝕂 (c' • a) (c' • b) =
        c' ^ 3 • symmetric_bch_cubic_poly 𝕂 a b :=
      symmetric_bch_cubic_poly_smul a b c'
    -- Term 2: ‖c'³ • (sym_E₃(a,b) - sym_bch_cubic(a,b))‖ ≤ |c|³·10⁷·s⁵
    have hT2 : ‖c' ^ 3 • (symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_cubic 𝕂 a b)‖ ≤
        |c| ^ 3 * (10000000 * s ^ 5) := by
      have hc3_norm : ‖c' ^ 3‖ = |c| ^ 3 := by rw [norm_pow, hc'_norm]
      have hbound : ‖symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_cubic 𝕂 a b‖ ≤
          10000000 * s ^ 5 := by
        rw [show symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_cubic 𝕂 a b =
            -(symmetric_bch_cubic 𝕂 a b - symmetric_bch_cubic_poly 𝕂 a b) from by abel]
        rw [norm_neg]
        exact norm_symmetric_bch_cubic_sub_poly_le (𝕂 := 𝕂) a b hab
      calc _ ≤ ‖c' ^ 3‖ * ‖_‖ := norm_smul_le _ _
        _ ≤ |c| ^ 3 * (10000000 * s ^ 5) := by rw [hc3_norm]; gcongr
    -- Combine: D(c) = (sym_bch_cubic(ca,cb) - sym_E₃(ca,cb)) + c'³ • (sym_E₃(a,b) - sym_bch_cubic(a,b))
    have hD_decomp : symmetric_bch_cubic 𝕂 (c' • a) (c' • b) -
        c' ^ 3 • symmetric_bch_cubic 𝕂 a b =
        (symmetric_bch_cubic 𝕂 (c' • a) (c' • b) -
          symmetric_bch_cubic_poly 𝕂 (c' • a) (c' • b)) +
        c' ^ 3 • (symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_cubic 𝕂 a b) := by
      rw [hhom, smul_sub]; abel
    -- Apply triangle inequality
    calc ‖symmetric_bch_cubic 𝕂 (c' • a) (c' • b) -
          c' ^ 3 • symmetric_bch_cubic 𝕂 a b‖
        = ‖_ + _‖ := by rw [hD_decomp]
      _ ≤ ‖symmetric_bch_cubic 𝕂 (c' • a) (c' • b) -
            symmetric_bch_cubic_poly 𝕂 (c' • a) (c' • b)‖ +
          ‖c' ^ 3 • (symmetric_bch_cubic_poly 𝕂 a b - symmetric_bch_cubic 𝕂 a b)‖ :=
            norm_add_le _ _
      _ ≤ 10000000 * (|c| * s) ^ 5 + |c| ^ 3 * (10000000 * s ^ 5) := by linarith
      _ ≤ 20000000 * |c| ^ 3 * s ^ 5 := by
          -- 10⁷·|c|⁵·s⁵ + 10⁷·|c|³·s⁵ ≤ 10⁷·|c|³·s⁵ + 10⁷·|c|³·s⁵ = 2·10⁷·|c|³·s⁵
          have hc5_le_c3 : |c| ^ 5 ≤ |c| ^ 3 := by
            have h_c2 : |c| ^ 2 ≤ 1 := by
              calc |c| ^ 2 ≤ 1 ^ 2 := by gcongr
                _ = 1 := one_pow _
            calc |c| ^ 5 = |c| ^ 3 * |c| ^ 2 := by ring
              _ ≤ |c| ^ 3 * 1 := by
                  apply mul_le_mul_of_nonneg_left h_c2 (pow_nonneg hc_nn 3)
              _ = |c| ^ 3 := mul_one _
          have hcs5 : (|c| * s) ^ 5 = |c| ^ 5 * s ^ 5 := by ring
          calc 10000000 * (|c| * s) ^ 5 + |c| ^ 3 * (10000000 * s ^ 5)
              = 10000000 * |c| ^ 5 * s ^ 5 + 10000000 * |c| ^ 3 * s ^ 5 := by rw [hcs5]; ring
            _ ≤ 10000000 * |c| ^ 3 * s ^ 5 + 10000000 * |c| ^ 3 * s ^ 5 := by
                gcongr
            _ = 20000000 * |c| ^ 3 * s ^ 5 := by ring

end

end BCH

