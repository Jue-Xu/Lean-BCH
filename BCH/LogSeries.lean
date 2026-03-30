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

/-! ### The exp ∘ log identity (placeholder) -/

include 𝕂 in
/-- `exp(log(1+x)) = 1 + x` for `‖x‖ < 1` in a Banach algebra.

This is the key identity connecting the logarithm and exponential series.
The proof requires showing that the formal power series composition
`exp ∘ log` equals the identity, which can be done via:
- Power series uniqueness (showing coefficients match termwise)
- ODE argument (both sides satisfy the same ODE with the same initial condition)
- Direct algebraic manipulation of the double series

TODO: Complete this proof. The infrastructure above (summability, bounds)
is sufficient for the BCH project; this identity will be filled in later. -/
theorem exp_logOnePlus (x : 𝔸) (hx : ‖x‖ < 1) :
    exp (logOnePlus (𝕂 := 𝕂) x) = 1 + x := by
  sorry

end
