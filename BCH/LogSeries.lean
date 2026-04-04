/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Banach Algebra Logarithm Series

The logarithm series `log(1+x) = ∑' n, (-1)^n/(n+1) • x^(n+1)` for `‖x‖ < 1`
in a complete normed algebra, together with basic estimates.

## Main definitions

* `logSeriesTerm x n`: the n-th term `(-1)^n/(n+1) • x^(n+1)` of the log series
* `logOnePlus x`: the infinite sum `∑' n, logSeriesTerm x n`

## Main results

* `summable_logSeriesTerm`: the series converges when `‖x‖ < 1`
* `norm_logOnePlus_le`: `‖log(1+x)‖ ≤ ‖x‖/(1-‖x‖)`
* `norm_logOnePlus_sub_le`: `‖log(1+x) - x‖ ≤ ‖x‖²/(1-‖x‖)`
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

noncomputable section

open Finset NormedSpace Topology

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### Definition of the log series -/

/-- The n-th term of the `log(1+x)` series: `(-1)^n / (n+1) • x^(n+1)`.
The series `∑ n, logSeriesTerm x n` gives `x - x²/2 + x³/3 - x⁴/4 + ...`. -/
def logSeriesTerm (x : 𝔸) (n : ℕ) : 𝔸 :=
  ((-1 : 𝕂) ^ n * ((n + 1 : 𝕂)⁻¹)) • x ^ (n + 1)

/-- `log(1+x) = ∑' n, (-1)^n/(n+1) • x^(n+1)` for elements of a Banach algebra. -/
def logOnePlus (x : 𝔸) : 𝔸 := ∑' n, logSeriesTerm (𝕂 := 𝕂) x n

/-! ### Norm estimates for the terms -/

include 𝕂 in
omit [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- The norm of `(-1)^n * (n+1)⁻¹` as a scalar is at most 1. -/
lemma norm_logSeriesCoeff_le (n : ℕ) :
    ‖((-1 : 𝕂) ^ n * ((n + 1 : 𝕂)⁻¹))‖ ≤ 1 := by
  have h1 : ‖((-1 : 𝕂) ^ n)‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hcast : (n : 𝕂) + 1 = ((n + 1 : ℕ) : 𝕂) := by push_cast; ring
  have h2 : ‖((n + 1 : 𝕂)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, hcast, RCLike.norm_natCast]
    exact (inv_le_one₀ (by positivity)).mpr (by exact_mod_cast Nat.succ_pos n)
  rw [norm_mul, h1, one_mul]
  exact h2

include 𝕂 in
omit [CompleteSpace 𝔸] in
/-- The norm of a log series term is bounded by `‖x‖^(n+1)`. -/
lemma norm_logSeriesTerm_le (x : 𝔸) (n : ℕ) :
    ‖logSeriesTerm (𝕂 := 𝕂) x n‖ ≤ ‖x‖ ^ (n + 1) := by
  unfold logSeriesTerm
  calc ‖((-1 : 𝕂) ^ n * ((n + 1 : 𝕂)⁻¹)) • x ^ (n + 1)‖
      ≤ ‖((-1 : 𝕂) ^ n * ((n + 1 : 𝕂)⁻¹))‖ * ‖x ^ (n + 1)‖ := norm_smul_le _ _
    _ ≤ 1 * ‖x ^ (n + 1)‖ := by
        apply mul_le_mul_of_nonneg_right (norm_logSeriesCoeff_le n) (norm_nonneg _)
    _ = ‖x ^ (n + 1)‖ := one_mul _
    _ ≤ ‖x‖ ^ (n + 1) := norm_pow_le x (n + 1)

/-! ### Summability -/

/-- The geometric series `∑ r^(n+1)` is summable when `0 ≤ r < 1`. -/
private lemma summable_geometric_succ {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ => r ^ (n + 1)) := by
  have hsumm := (summable_geometric_of_lt_one h0 h1).mul_left r
  refine hsumm.congr (fun n => ?_)
  ring

include 𝕂 in
/-- The log series `∑ logSeriesTerm x n` converges absolutely when `‖x‖ < 1`. -/
theorem summable_logSeriesTerm (x : 𝔸) (hx : ‖x‖ < 1) :
    Summable (logSeriesTerm (𝕂 := 𝕂) x) :=
  Summable.of_norm_bounded (g := fun n => ‖x‖ ^ (n + 1))
    (summable_geometric_succ (norm_nonneg x) hx)
    (norm_logSeriesTerm_le (𝕂 := 𝕂) x)

include 𝕂 in
omit [CompleteSpace 𝔸] in
/-- The norms of the log series terms are summable when `‖x‖ < 1`. -/
theorem summable_norm_logSeriesTerm (x : 𝔸) (hx : ‖x‖ < 1) :
    Summable (fun n => ‖logSeriesTerm (𝕂 := 𝕂) x n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_logSeriesTerm_le (𝕂 := 𝕂) x)
    (summable_geometric_succ (norm_nonneg x) hx)

/-! ### The 0th term is x -/

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
@[simp]
lemma logSeriesTerm_zero (x : 𝔸) : logSeriesTerm (𝕂 := 𝕂) x 0 = x := by
  simp [logSeriesTerm]

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
@[simp]
lemma logSeriesTerm_one (x : 𝔸) :
    logSeriesTerm (𝕂 := 𝕂) x 1 = -((2 : 𝕂)⁻¹ • x ^ 2) := by
  simp [logSeriesTerm, pow_succ]
  ring

/-! ### Norm bound for the full series -/

include 𝕂 in
omit [CompleteSpace 𝔸] in
/-- `‖log(1+x)‖ ≤ ‖x‖/(1-‖x‖)` when `‖x‖ < 1`. -/
theorem norm_logOnePlus_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖logOnePlus (𝕂 := 𝕂) x‖ ≤ ‖x‖ / (1 - ‖x‖) := by
  unfold logOnePlus
  rw [div_eq_mul_inv]
  have h_geom := (hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖
  have h_eq : (fun i => ‖x‖ * ‖x‖ ^ i) = (fun i => ‖x‖ ^ (i + 1)) := by
    ext n; ring
  rw [h_eq] at h_geom
  exact tsum_of_norm_bounded h_geom (norm_logSeriesTerm_le (𝕂 := 𝕂) x)

/-! ### Remainder bound (log minus linear term) -/

include 𝕂 in
/-- The shifted series `∑'_{n≥1} logSeriesTerm x n` is summable when `‖x‖ < 1`. -/
lemma summable_logSeriesTerm_shift (x : 𝔸) (hx : ‖x‖ < 1) :
    Summable (fun n => logSeriesTerm (𝕂 := 𝕂) x (n + 1)) :=
  (summable_nat_add_iff (f := logSeriesTerm (𝕂 := 𝕂) x) 1).mpr
    (summable_logSeriesTerm (𝕂 := 𝕂) x hx)

include 𝕂 in
/-- `log(1+x) - x = ∑' n, logSeriesTerm x (n+1)`. -/
lemma logOnePlus_sub_eq_tsum (x : 𝔸) (hx : ‖x‖ < 1) :
    logOnePlus (𝕂 := 𝕂) x - x = ∑' n, logSeriesTerm (𝕂 := 𝕂) x (n + 1) := by
  unfold logOnePlus
  rw [(summable_logSeriesTerm (𝕂 := 𝕂) x hx).tsum_eq_zero_add]
  simp [logSeriesTerm_zero (𝕂 := 𝕂)]

include 𝕂 in
/-- `‖log(1+x) - x‖ ≤ ‖x‖²/(1-‖x‖)` when `‖x‖ < 1`. -/
theorem norm_logOnePlus_sub_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖logOnePlus (𝕂 := 𝕂) x - x‖ ≤ ‖x‖ ^ 2 / (1 - ‖x‖) := by
  rw [logOnePlus_sub_eq_tsum (𝕂 := 𝕂) x hx, div_eq_mul_inv]
  -- Bound by ∑' n, ‖x‖^(n+2) = ‖x‖² * ∑' n, ‖x‖^n = ‖x‖²/(1-‖x‖)
  have h_geom := (hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x‖ ^ 2)
  have h_eq : (fun i => ‖x‖ ^ 2 * ‖x‖ ^ i) = (fun i => ‖x‖ ^ (i + 2)) := by
    ext n; ring
  rw [h_eq] at h_geom
  apply tsum_of_norm_bounded h_geom
  intro n
  calc ‖logSeriesTerm (𝕂 := 𝕂) x (n + 1)‖
      ≤ ‖x‖ ^ (n + 1 + 1) := norm_logSeriesTerm_le (𝕂 := 𝕂) x (n + 1)
    _ = ‖x‖ ^ (n + 2) := by ring_nf

/-! ### Remainder bound (log minus linear and quadratic terms) -/

include 𝕂 in
/-- The double-shifted series `∑'_{n≥2} logSeriesTerm x n` is summable when `‖x‖ < 1`. -/
lemma summable_logSeriesTerm_shift2 (x : 𝔸) (hx : ‖x‖ < 1) :
    Summable (fun n => logSeriesTerm (𝕂 := 𝕂) x (n + 2)) :=
  (summable_nat_add_iff (f := logSeriesTerm (𝕂 := 𝕂) x) 2).mpr
    (summable_logSeriesTerm (𝕂 := 𝕂) x hx)

include 𝕂 in
/-- `log(1+x) - x + x²/2 = ∑' n, logSeriesTerm x (n+2)`. -/
lemma logOnePlus_sub_sub_eq_tsum (x : 𝔸) (hx : ‖x‖ < 1) :
    logOnePlus (𝕂 := 𝕂) x - x + (2 : 𝕂)⁻¹ • x ^ 2 =
      ∑' n, logSeriesTerm (𝕂 := 𝕂) x (n + 2) := by
  have hsumm := summable_logSeriesTerm_shift (𝕂 := 𝕂) x hx
  rw [logOnePlus_sub_eq_tsum (𝕂 := 𝕂) x hx, hsumm.tsum_eq_zero_add,
      logSeriesTerm_one (𝕂 := 𝕂)]
  abel

include 𝕂 in
/-- `‖log(1+x) - x + x²/2‖ ≤ ‖x‖³/(1-‖x‖)` when `‖x‖ < 1`. -/
theorem norm_logOnePlus_sub_sub_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖logOnePlus (𝕂 := 𝕂) x - x + (2 : 𝕂)⁻¹ • x ^ 2‖ ≤ ‖x‖ ^ 3 / (1 - ‖x‖) := by
  rw [logOnePlus_sub_sub_eq_tsum (𝕂 := 𝕂) x hx, div_eq_mul_inv]
  have h_geom := (hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x‖ ^ 3)
  have h_eq : (fun i => ‖x‖ ^ 3 * ‖x‖ ^ i) = (fun i => ‖x‖ ^ (i + 3)) := by
    ext n; ring
  rw [h_eq] at h_geom
  apply tsum_of_norm_bounded h_geom
  intro n
  calc ‖logSeriesTerm (𝕂 := 𝕂) x (n + 2)‖
      ≤ ‖x‖ ^ (n + 2 + 1) := norm_logSeriesTerm_le (𝕂 := 𝕂) x (n + 2)
    _ = ‖x‖ ^ (n + 3) := by ring_nf

/-! ### Remainder bound (log minus linear, quadratic, and cubic terms) -/

include 𝕂 in
/-- The triple-shifted series `∑'_{n≥3} logSeriesTerm x n` is summable when `‖x‖ < 1`. -/
lemma summable_logSeriesTerm_shift3 (x : 𝔸) (hx : ‖x‖ < 1) :
    Summable (fun n => logSeriesTerm (𝕂 := 𝕂) x (n + 3)) :=
  (summable_nat_add_iff (f := logSeriesTerm (𝕂 := 𝕂) x) 3).mpr
    (summable_logSeriesTerm (𝕂 := 𝕂) x hx)

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
@[simp]
lemma logSeriesTerm_two (x : 𝔸) :
    logSeriesTerm (𝕂 := 𝕂) x 2 = (3 : 𝕂)⁻¹ • x ^ 3 := by
  simp [logSeriesTerm, pow_succ]
  ring

include 𝕂 in
/-- `log(1+x) - x + x²/2 - x³/3 = ∑' n, logSeriesTerm x (n+3)`. -/
lemma logOnePlus_sub_sub_sub_eq_tsum (x : 𝔸) (hx : ‖x‖ < 1) :
    logOnePlus (𝕂 := 𝕂) x - x + (2 : 𝕂)⁻¹ • x ^ 2 - (3 : 𝕂)⁻¹ • x ^ 3 =
      ∑' n, logSeriesTerm (𝕂 := 𝕂) x (n + 3) := by
  have hsumm := summable_logSeriesTerm_shift2 (𝕂 := 𝕂) x hx
  rw [logOnePlus_sub_sub_eq_tsum (𝕂 := 𝕂) x hx, hsumm.tsum_eq_zero_add,
      logSeriesTerm_two (𝕂 := 𝕂)]
  abel

include 𝕂 in
/-- `‖log(1+x) - x + x²/2 - x³/3‖ ≤ ‖x‖⁴/(1-‖x‖)` when `‖x‖ < 1`. -/
theorem norm_logOnePlus_sub_sub_sub_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖logOnePlus (𝕂 := 𝕂) x - x + (2 : 𝕂)⁻¹ • x ^ 2 - (3 : 𝕂)⁻¹ • x ^ 3‖ ≤
      ‖x‖ ^ 4 / (1 - ‖x‖) := by
  rw [logOnePlus_sub_sub_sub_eq_tsum (𝕂 := 𝕂) x hx, div_eq_mul_inv]
  have h_geom := (hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x‖ ^ 4)
  have h_eq : (fun i => ‖x‖ ^ 4 * ‖x‖ ^ i) = (fun i => ‖x‖ ^ (i + 4)) := by
    ext n; ring
  rw [h_eq] at h_geom
  apply tsum_of_norm_bounded h_geom
  intro n
  calc ‖logSeriesTerm (𝕂 := 𝕂) x (n + 3)‖
      ≤ ‖x‖ ^ (n + 3 + 1) := norm_logSeriesTerm_le (𝕂 := 𝕂) x (n + 3)
    _ = ‖x‖ ^ (n + 4) := by ring_nf

/-! ### The exp ∘ log identity -/

/-! #### Step 1: Real scalar case via `Real.hasSum_pow_div_log_of_abs_lt_one` -/

section RealCase

open Real in
/-- The log series `∑ (-1)^n/(n+1) · t^(n+1)` equals `Real.log(1+t)` for `|t| < 1`.
This connects our `logOnePlus` with the standard real logarithm. -/
lemma hasSum_logSeriesTerm_real {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (logSeriesTerm (𝕂 := ℝ) t) (Real.log (1 + t)) := by
  -- From `hasSum_pow_div_log_of_abs_lt_one`: ∑ x^(n+1)/(n+1) = -log(1-x) for |x| < 1.
  -- Substitute x ↦ -t: ∑ (-t)^(n+1)/(n+1) = -log(1+t).
  -- Since (-t)^(n+1) = (-1)^(n+1) t^(n+1) = -(-1)^n t^(n+1), we get:
  -- ∑ -(-1)^n t^(n+1)/(n+1) = -log(1+t), i.e., ∑ (-1)^n t^(n+1)/(n+1) = log(1+t).
  rw [Real.norm_eq_abs] at ht
  have h_neg : |(-t)| < 1 := by rwa [abs_neg]
  have h1 := hasSum_pow_div_log_of_abs_lt_one h_neg
  -- h1 : HasSum (fun n => (-t)^(n+1) / (n+1)) (-log(1-(-t)))
  -- Simplify: 1-(-t) = 1+t
  simp only [sub_neg_eq_add] at h1
  -- Now negate both sides: HasSum (fun n => -((-t)^(n+1) / (n+1))) (log(1+t))
  have h2 := h1.neg
  simp only [neg_neg] at h2
  -- h2 : HasSum (fun n => -((-t)^(n+1) / (n+1))) (Real.log(1+t))
  -- Need: each term -((-t)^(n+1)/(n+1)) = logSeriesTerm t n
  convert h2 using 1
  ext n
  simp only [logSeriesTerm, smul_eq_mul]
  ring

open Real in
/-- `logOnePlus` for real scalars equals `Real.log(1+t)`. -/
lemma logOnePlus_real_eq {t : ℝ} (ht : ‖t‖ < 1) :
    logOnePlus (𝕂 := ℝ) t = Real.log (1 + t) :=
  (hasSum_logSeriesTerm_real ht).tsum_eq

open Real in
/-- `exp(logOnePlus t) = 1 + t` for real `t` with `|t| < 1`. -/
theorem exp_logOnePlus_real {t : ℝ} (ht : ‖t‖ < 1) :
    NormedSpace.exp (logOnePlus (𝕂 := ℝ) t) = 1 + t := by
  rw [logOnePlus_real_eq ht, ← Real.exp_eq_exp_ℝ]
  -- exp(log(1+t)) = 1+t since 1+t > 0
  apply Real.exp_log
  have ht' : |t| < 1 := by rwa [Real.norm_eq_abs] at ht
  linarith [neg_abs_le t]

end RealCase

/-! #### Step 2: Complex scalar case -/

section ComplexCase

open Complex in
/-- The log series for complex scalars equals `Complex.log(1+z)`. -/
lemma hasSum_logSeriesTerm_complex {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (logSeriesTerm (𝕂 := ℂ) z) (Complex.log (1 + z)) := by
  -- Strategy: use Complex.hasSum_taylorSeries_log and shift the index.
  let g : ℕ → ℂ := fun n => (-1) ^ (n + 1) * z ^ n / ↑n
  have hg := Complex.hasSum_taylorSeries_log hz
  have hg0 : g 0 = 0 := by simp [g]
  -- logSeriesTerm z n = g (n + 1)
  have hterm : logSeriesTerm (𝕂 := ℂ) z = g ∘ (· + 1) := by
    ext n; simp only [logSeriesTerm, smul_eq_mul, g, Function.comp_def]; push_cast; ring
  rw [hterm]
  -- HasSum g s ∧ g 0 = 0  implies  HasSum (g ∘ (· + 1)) s
  -- From hg: ∑' n, g n = log(1+z). Since g 0 = 0 and ∑' n, g n = g 0 + ∑' n, g(n+1),
  -- we get ∑' n, g(n+1) = log(1+z). The shifted series is summable and its sum is log(1+z).
  have hsumm := hg.summable
  have key : ∑' n, (g ∘ (· + 1)) n = Complex.log (1 + z) := by
    have h_split := hsumm.tsum_eq_zero_add
    rw [hg.tsum_eq] at h_split
    simp only [g, Function.comp_def] at h_split ⊢
    simp only [zero_add, pow_zero, Nat.cast_zero, div_zero] at h_split
    exact h_split.symm
  exact ((summable_nat_add_iff (f := g) 1).mpr hsumm).hasSum_iff.mpr key

open Complex in
/-- `logOnePlus` for complex scalars equals `Complex.log(1+z)`. -/
lemma logOnePlus_complex_eq {z : ℂ} (hz : ‖z‖ < 1) :
    logOnePlus (𝕂 := ℂ) z = Complex.log (1 + z) :=
  (hasSum_logSeriesTerm_complex hz).tsum_eq

open Complex in
/-- `exp(logOnePlus z) = 1 + z` for complex `z` with `‖z‖ < 1`. -/
theorem exp_logOnePlus_complex {z : ℂ} (hz : ‖z‖ < 1) :
    NormedSpace.exp (logOnePlus (𝕂 := ℂ) z) = 1 + z := by
  rw [logOnePlus_complex_eq hz, ← Complex.exp_eq_exp_ℂ]
  exact Complex.exp_log (by
    intro h
    have h1 : z = -1 := by linear_combination h
    rw [h1] at hz
    simp at hz)

end ComplexCase

/-! #### Step 3: General Banach algebra case

We prove `exp(logOnePlus x) = 1 + x` for `x : 𝔸` with `‖x‖ < 1`.

**Proof strategy:** The scalar coefficients `(-1)^n/(n+1)` in `logOnePlus` are rational,
so `logOnePlus` and `exp` do not depend on the choice of RCLike scalar field `𝕂`.
We show the identity by the parameter trick: the function `Q(t) = exp(-logOnePlus(t•x)) * (1+t•x)`
satisfies `Q(0) = 1` and `Q'(t) = 0` (by cancellation), hence `Q ≡ 1`, giving the result at `t=1`.

The key sub-results are:
1. `logSeriesTerm_eq_ratSmul`: the log series terms use only rational scalars
2. `hasDerivAt_logOnePlus_smul`: term-by-term differentiation of `logOnePlus(t•x)`
3. Commutativity: all terms are power series in `x`, hence commute
4. The derivative of `Q` vanishes by algebraic cancellation
-/

/-! ##### Scalar independence -/

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- The log series scalar coefficient `(-1)^n/(n+1)` is the same whether computed in `𝕂` or `ℝ`. -/
lemma logSeriesTerm_eq_real (x : 𝔸) (n : ℕ) :
    logSeriesTerm (𝕂 := 𝕂) x n =
      @logSeriesTerm ℝ _ 𝔸 _ (NormedAlgebra.restrictScalars ℝ 𝕂 𝔸) x n := by
  simp only [logSeriesTerm]
  -- Both sides are `c • x^(n+1)` where c = (-1)^n/(n+1), viewed as a scalar in 𝕂 or ℝ.
  -- Since (-1)^n/(n+1) ∈ ℚ, the smul action on 𝔸 agrees by `ratCast_smul_eq`.
  -- The coefficient (-1)^n * (n+1)⁻¹ is rational; use `ratCast_smul_eq` to change the scalar field.
  -- Need Module ℝ 𝔸 explicitly from NormedAlgebra 𝕂 𝔸 via restriction of scalars.
  letI : Module ℝ 𝔸 := (NormedAlgebra.restrictScalars ℝ 𝕂 𝔸).toModule
  conv_lhs => rw [show (-1 : 𝕂) ^ n * ((n + 1 : 𝕂)⁻¹) = (((-1 : ℚ) ^ n * ((n + 1 : ℚ)⁻¹) : ℚ) : 𝕂) from by push_cast; ring]
  conv_rhs => rw [show (-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹) = (((-1 : ℚ) ^ n * ((n + 1 : ℚ)⁻¹) : ℚ) : ℝ) from by push_cast; ring]
  exact ratCast_smul_eq 𝕂 ℝ _ (x ^ (n + 1))

include 𝕂 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- `logOnePlus` is independent of the scalar field. -/
lemma logOnePlus_eq_real (x : 𝔸) :
    logOnePlus (𝕂 := 𝕂) x =
      @logOnePlus ℝ _ 𝔸 _ (NormedAlgebra.restrictScalars ℝ 𝕂 𝔸) x := by
  unfold logOnePlus
  exact tsum_congr (fun n => logSeriesTerm_eq_real (𝕂 := 𝕂) x n)

/-! ##### Auxiliary: Neumann series and invertibility -/

omit [NormOneClass 𝔸] in
/-- For `‖y‖ < 1`, the element `1 + y` is a unit. -/
private lemma isUnit_one_add {y : 𝔸} (hy : ‖y‖ < 1) : IsUnit (1 + y) := by
  rw [show (1 : 𝔸) + y = 1 - (-y) from by simp [sub_neg_eq_add]]
  exact isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])

/-! ##### Helpers for the ODE/constancy argument -/

set_option maxRecDepth 512 in
omit 𝕂 in
private lemma hasDerivAt_logSeriesTerm_smul [NormedAlgebra ℝ 𝔸] (x : 𝔸) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => logSeriesTerm (𝕂 := ℝ) (s • x) n)
      (((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) t := by
  have heq : (fun s => logSeriesTerm (𝕂 := ℝ) (s • x) n) =
      fun s => (((-1 : ℝ) ^ n * (↑(n + 1) : ℝ)⁻¹) * s ^ (n + 1)) • x ^ (n + 1) := by
    ext s; unfold logSeriesTerm; rw [smul_pow]; simp only [smul_smul]; congr 1; push_cast; ring
  rw [heq]
  exact ((hasDerivAt_pow (n + 1) t).const_mul
    ((-1 : ℝ) ^ n * (↑(n + 1) : ℝ)⁻¹)).smul_const (x ^ (n + 1)) |>.congr_deriv (by
    congr 1; rw [show n + 1 - 1 = n from by omega]; field_simp)

set_option maxRecDepth 512 in
omit 𝕂 in
private lemma norm_hasDerivAt_logSeriesTerm_le [NormedAlgebra ℝ 𝔸] (x : 𝔸) (n : ℕ) {r : ℝ}
    (hr : 0 < r) {t : ℝ} (ht : t ∈ Set.Ioo (-r) r) :
    ‖((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)‖ ≤ r ^ n * ‖x‖ ^ (n + 1) := by
  have htabs : |t| < r := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  calc ‖((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)‖
      ≤ ‖(-1 : ℝ) ^ n * t ^ n‖ * ‖x ^ (n + 1)‖ := norm_smul_le _ _
    _ = |t| ^ n * ‖x ^ (n + 1)‖ := by
        congr 1; rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ |t| ^ n * ‖x‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (norm_pow_le x (n + 1)) (pow_nonneg (abs_nonneg t) n)
    _ ≤ r ^ n * ‖x‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) htabs.le n)
          (pow_nonneg (norm_nonneg x) (n + 1))

omit 𝕂 in
private lemma summable_logSeriesTerm_deriv_bound (x : 𝔸) {r : ℝ} (hr : 0 < r) (hrx : r * ‖x‖ < 1) :
    Summable (fun n => r ^ n * ‖x‖ ^ (n + 1)) :=
  ((summable_geometric_of_lt_one (mul_nonneg hr.le (norm_nonneg x)) hrx).mul_left
    ‖x‖).congr fun n => by ring

set_option maxRecDepth 512 in
omit 𝕂 [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma summable_logSeriesTerm_smul_zero [NormedAlgebra ℝ 𝔸] (x : 𝔸) :
    Summable (fun n => logSeriesTerm (𝕂 := ℝ) ((0 : ℝ) • x) n) := by
  have : (fun n => logSeriesTerm (𝕂 := ℝ) ((0 : ℝ) • x) n) = fun _ => 0 := by
    ext n; simp [logSeriesTerm, zero_smul, zero_pow (show n + 1 ≠ 0 by omega)]
  rw [this]; exact summable_zero

set_option maxHeartbeats 400000 in
omit 𝕂 in
private lemma hasDerivAt_logOnePlus_smul [NormedAlgebra ℝ 𝔸] (x : 𝔸)
    (t : ℝ) (ht : |t| * ‖x‖ < 1) :
    HasDerivAt (fun s => logOnePlus (𝕂 := ℝ) (s • x))
      (∑' n, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) t := by
  have hr : ∃ r : ℝ, |t| < r ∧ r * ‖x‖ < 1 := by
    by_cases hx0 : ‖x‖ = 0
    · exact ⟨|t| + 1, by linarith, by simp [hx0]⟩
    · have hxp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
      exact ⟨(|t| + 1 / ‖x‖) / 2, by linarith [(lt_div_iff₀ hxp).mpr ht, one_div_pos.mpr hxp],
        by rw [div_mul_eq_mul_div]
           linarith [show (|t| + 1/‖x‖) * ‖x‖ = |t| * ‖x‖ + 1 from by field_simp]⟩
  obtain ⟨r, htr, hrx⟩ := hr
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (abs_nonneg t) htr
  unfold logOnePlus
  exact hasDerivAt_tsum_of_isPreconnected (summable_logSeriesTerm_deriv_bound x hr0 hrx)
    isOpen_Ioo isPreconnected_Ioo
    (fun n s _ => hasDerivAt_logSeriesTerm_smul x n s)
    (fun n s hs => norm_hasDerivAt_logSeriesTerm_le x n hr0 hs)
    ⟨by linarith, by linarith⟩ (summable_logSeriesTerm_smul_zero x)
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

omit 𝕂 in
private lemma commute_logOnePlus_smul [NormedAlgebra ℝ 𝔸] (x : 𝔸) (t s : ℝ) :
    Commute (logOnePlus (𝕂 := ℝ) (t • x)) (logOnePlus (𝕂 := ℝ) (s • x)) := by
  unfold logOnePlus; apply Commute.tsum_left; intro n; apply Commute.tsum_right; intro m
  unfold logSeriesTerm; rw [smul_pow, smul_pow, smul_smul, smul_smul]
  exact ((Commute.pow_pow (Commute.refl x) (n + 1) (m + 1)).smul_right _).smul_left _

set_option maxHeartbeats 800000 in
omit 𝕂 in
private lemma hasDerivAt_exp_of_hasDerivAt_commute [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸]
    {f : ℝ → 𝔸} {f' : 𝔸} {t : ℝ}
    (hf : HasDerivAt f f' t) (hcomm : ∀ s : ℝ, Commute (f t) (f s - f t)) :
    HasDerivAt (fun s => exp (f s)) (exp (f t) * f') t := by
  suffices h : HasDerivAt (fun s => exp (f s - f t)) f' t by
    rw [show (fun s => exp (f s)) = (fun s => exp (f t) * exp (f s - f t)) from by
      ext s; rw [← exp_add_of_commute (hcomm s)]; congr 1; abel]
    have := (hasDerivAt_const t (exp (f t))).mul h
    simp [exp_zero] at this; exact this
  have hinner : HasDerivAt (fun s => f s - f t) f' t :=
    (hf.sub (hasDerivAt_const t (f t))).congr_deriv (by simp)
  letI : RCLike ℝ := Real.instRCLike
  have := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).comp_hasDerivAt_of_eq t hinner
    (sub_self (f t)).symm
  simp only [Function.comp_def, ContinuousLinearMap.one_apply] at this; exact this

/-! ##### The exp ∘ log identity -/

include 𝕂 in
/-- `exp(log(1+x)) = 1 + x` for `‖x‖ < 1` in a Banach algebra.

This is the fundamental identity connecting the logarithm and exponential series.
The proof first reduces to ℝ scalars (since `logOnePlus` uses only rational coefficients),
then proceeds by the ODE/constancy argument:

The function `Q(t) = exp(-logOnePlus(t•x)) * (1+t•x)` satisfies:
- `Q(0) = exp(0) * 1 = 1`
- `Q'(t) = 0` (by cancellation: the derivative of `exp(-logOnePlus(t•x))` is
  `-exp(-logOnePlus(t•x)) * (1+t•x)⁻¹ * x` using commutativity of power series in `x`,
  and the product rule gives `Q'(t) = -exp(...)*(1+t•x)⁻¹*x*(1+t•x) + exp(...)*x = 0`)

Hence `Q ≡ 1` by `is_const_of_deriv_eq_zero`, giving `exp(logOnePlus(x)) = 1+x` at `t=1`.

The commutativity needed for the chain rule holds because `logOnePlus(t•x)` and its
`t`-derivative `(1+t•x)⁻¹*x` are both elements of `Algebra.elemental ℝ x`, which is
commutative. The `t`-derivative of the log series is computed by `hasDerivAt_tsum`. -/
theorem exp_logOnePlus (x : 𝔸) (hx : ‖x‖ < 1) :
    exp (logOnePlus (𝕂 := 𝕂) x) = 1 + x := by
  -- Reduce to ℝ scalars since the log series is 𝕂-independent
  rw [logOnePlus_eq_real (𝕂 := 𝕂)]
  -- The identity now involves only ℝ-scalars. Both exp and logOnePlus use ℚ-algebra
  -- structure under the hood, so this is purely about the Banach algebra 𝔸 over ℝ.
  -- It suffices to show: (1+x) is a left inverse of exp(-logOnePlus x), because
  -- exp(-logOnePlus x) already has a right inverse exp(logOnePlus x).
  -- We use: exp(y) * exp(-y) = 1 for all y (since y commutes with -y).
  set instℝ := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℝ 𝔸 := instℝ
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set y := @logOnePlus ℝ _ 𝔸 _ instℝ x with hy_def
  -- Goal: exp y = 1 + x
  -- Strategy: show exp(-y) * (1+x) = 1, then multiply both sides on the left by exp(y)
  suffices h : exp (-y) * (1 + x) = 1 by
    have hinv : exp y * exp (-y) = 1 := by
      rw [← exp_add_of_commute (Commute.neg_right (Commute.refl y)), add_neg_cancel, exp_zero]
    calc exp y = exp y * 1 := (mul_one _).symm
    _ = exp y * (exp (-y) * (1 + x)) := by rw [h]
    _ = (exp y * exp (-y)) * (1 + x) := (mul_assoc _ _ _).symm
    _ = 1 * (1 + x) := by rw [hinv]
    _ = 1 + x := one_mul _
  -- Now we need: exp(-logOnePlus x) * (1+x) = 1.
  -- Define Q : ℝ → 𝔸 by Q(t) = exp(-logOnePlus(t•x)) * (1 + t•x).
  -- We show Q ≡ 1 by: Q(0) = 1 and Q is constant (derivative 0).
  let Q : ℝ → 𝔸 := fun t =>
    exp (-@logOnePlus ℝ _ 𝔸 _ instℝ ((t : ℝ) • x)) * (1 + (t : ℝ) • x)
  -- Q(0) = exp(0) * 1 = 1
  have hQ0 : Q 0 = 1 := by
    simp only [Q, zero_smul]
    have : @logOnePlus ℝ _ 𝔸 _ instℝ 0 = 0 := by
      simp [logOnePlus, logSeriesTerm, tsum_zero]
    rw [this, neg_zero, exp_zero, add_zero, mul_one]
  -- Q(1) is what we want
  have hQ1 : Q 1 = exp (-y) * (1 + x) := by
    simp only [Q, one_smul, hy_def]
  -- It suffices to show Q(1) = Q(0), i.e., Q is constant
  rw [← hQ1, show Q 1 = Q 0 from ?_, hQ0]
  -- Use is_const_of_deriv_eq_zero to show Q is constant.
  -- This requires: (1) Q is differentiable, (2) deriv Q = 0 everywhere.
  -- Both follow from term-by-term differentiation of the log series (hasDerivAt_tsum)
  -- and the chain rule for exp in the commutative subalgebra Algebra.elemental ℝ x.
  --
  -- Specifically, the derivative calculation gives:
  -- Q'(t) = [d/dt exp(-logOnePlus(t•x))] * (1+t•x) + exp(-logOnePlus(t•x)) * x
  --       = -exp(-logOnePlus(t•x)) * (1+t•x)⁻¹ * x * (1+t•x) + exp(-logOnePlus(t•x)) * x
  --       = -exp(-logOnePlus(t•x)) * x + exp(-logOnePlus(t•x)) * x   [commutativity in x-algebra]
  --       = 0
  --
  -- The commutativity of x with (1+t•x)⁻¹ holds because both lie in Algebra.elemental ℝ x,
  -- which is commutative (Mathlib.Topology.Algebra.Algebra, instance CommRing (elemental R x)).
  -- The chain rule for exp applies in the commutative setting via hasFDerivAt_exp.
  -- The derivative of logOnePlus(t•x) w.r.t. t is (1+t•x)⁻¹ * x by hasDerivAt_tsum.
  -- Prove Q 1 = Q 0 using IsOpen.is_const_of_deriv_eq_zero on Ioo(−1/‖x‖, 1/‖x‖).
  -- First, show HasDerivAt Q 0 t for all t with |t|·‖x‖ < 1.
  set L := fun (s : ℝ) => @logOnePlus ℝ _ 𝔸 _ instℝ ((s : ℝ) • x) with hL_def
  have hQderiv : ∀ t : ℝ, |t| * ‖x‖ < 1 → HasDerivAt Q 0 t := by
    intro t ht
    -- Derivative of logOnePlus(t•x)
    have hL' := hasDerivAt_logOnePlus_smul x t ht
    -- Commutativity for the exp chain rule
    have hcomm_exp : ∀ s, Commute (-L t) (-L s - (-L t)) := by
      intro s; simp only [neg_sub_neg]
      exact (Commute.refl (L t)).neg_left.sub_right (commute_logOnePlus_smul x t s).neg_left
    -- Chain rule for exp(-logOnePlus(t•x))
    have hexp' := hasDerivAt_exp_of_hasDerivAt_commute hL'.neg hcomm_exp
    -- Derivative of 1 + t•x
    have hlin : HasDerivAt (fun s => 1 + s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x |>.const_add 1
    -- Product rule
    have hQ' := hexp'.mul hlin
    -- Neumann series cancellation: L'(t) * (1 + t•x) = x
    set L't := ∑' n, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)
    have hL'_eq : L't = (∑' n, (-(t • x)) ^ n) * x := by
      -- First show L't = ∑' n, (-(t•x))^n * x using HasSum.mul_right
      have hgeom_summable : Summable (fun n => (-(t • x)) ^ n) := by
        exact summable_geometric_of_norm_lt_one (by rwa [norm_neg, norm_smul, Real.norm_eq_abs])
      calc L't = ∑' n, (-(t • x)) ^ n * x := tsum_congr (fun n => by
              show ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1) = (-(t • x)) ^ n * x
              conv_rhs => rw [show -(t • x) = (-t) • x from (neg_smul t x).symm,
                smul_pow, smul_mul_assoc, ← pow_succ, neg_pow])
        _ = (∑' n, (-(t • x)) ^ n) * x := hgeom_summable.tsum_mul_right x
    have htx_norm : ‖-(t • x)‖ < 1 := by rwa [norm_neg, norm_smul, Real.norm_eq_abs]
    have hcancel : L't * (1 + t • x) = x := by
      rw [hL'_eq, mul_assoc,
        show x * (1 + t • x) = (1 + t • x) * x from
          ((Commute.one_right x).add_right ((Commute.refl x).smul_right t)),
        ← mul_assoc, show (1 : 𝔸) + t • x = 1 - -(t • x) from by simp,
        geom_series_mul_neg _ htx_norm, one_mul]
    -- Conclude Q'(t) = 0
    refine hQ'.congr_deriv ?_
    -- The goal contains `(-fun s => logOnePlus(s • x)) t`; reduce to `-L t`
    change exp (-L t) * (-L't) * (1 + t • x) + exp (-L t) * x = 0
    rw [mul_assoc, neg_mul, ← mul_add, hcancel, neg_add_cancel, mul_zero]
  -- Handle x = 0 separately; for x ≠ 0, use IsOpen.is_const_of_deriv_eq_zero.
  by_cases hx0 : x = 0
  · subst hx0
    show Q 1 = Q 0
    simp only [Q, smul_zero, add_zero, logOnePlus, logSeriesTerm, tsum_zero, neg_zero, exp_zero,
      mul_one]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set s := Set.Ioo (-(1 / ‖x‖)) (1 / ‖x‖) with hs_def
    have hR : 1 < 1 / ‖x‖ := (one_lt_div₀ hxn).mpr hx
    have h0_mem : (0 : ℝ) ∈ s := ⟨by linarith, by linarith⟩
    have h1_mem : (1 : ℝ) ∈ s := ⟨by linarith, by linarith⟩
    have ht_bound : ∀ t ∈ s, |t| * ‖x‖ < 1 := by
      intro t ht; have := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      calc |t| * ‖x‖ < 1 / ‖x‖ * ‖x‖ := mul_lt_mul_of_pos_right this hxn
        _ = 1 := by field_simp
    exact IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun t ht => (hQderiv t (ht_bound t ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => (hQderiv t (ht_bound t ht)).deriv) h1_mem h0_mem

end
