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

**Proof strategy (ODE/derivative approach):**
Define `H(t) = exp(logOnePlus(t•x)) · Ring.inverse(1 + t•x)` for `t : ℝ`.
Then `H(0) = 1`. One shows `H'(t) = 0` by verifying:
- `d/dt logOnePlus(t•x) = Ring.inverse(1+t•x) · x` (term-by-term differentiation)
- The chain rule for exp (valid since logOnePlus(t•x) commutes with its derivative,
  as both are power series in `x`)
- `d/dt Ring.inverse(1+t•x) = -Ring.inverse(1+t•x) · x · Ring.inverse(1+t•x)`

The resulting cancellation gives `H'(t) = 0`, so `H` is constant and `H(1) = 1`,
yielding `exp(logOnePlus x) = 1 + x`.
-/

include 𝕂 in
/-- `exp(log(1+x)) = 1 + x` for `‖x‖ < 1` in a Banach algebra.

This is the fundamental identity connecting the logarithm and exponential series.
The proof for the real scalar case uses `Real.hasSum_pow_div_log_of_abs_lt_one`
(see `exp_logOnePlus_real`). The general Banach algebra case uses the ODE argument:
`d/dt[exp(logOnePlus(t•x)) · (1+t•x)⁻¹] = 0`, see the module docstring above. -/
theorem exp_logOnePlus (x : 𝔸) (hx : ‖x‖ < 1) :
    exp (logOnePlus (𝕂 := 𝕂) x) = 1 + x := by
  sorry

end
