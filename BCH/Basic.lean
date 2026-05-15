/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH Basic: Structural Baker-Campbell-Hausdorff theorem

The BCH element `bch a b = logOnePlus(exp(a) · exp(b) - 1)` is the unique element Z
satisfying `exp(Z) = exp(a) · exp(b)`, defined for ‖a‖ + ‖b‖ < ln 2.

## Main definitions

* `bch a b`: the BCH element, defined via the log series applied to `exp(a) · exp(b) - 1`

## Main results

* `exp_bch`: `exp(bch a b) = exp a * exp b` for ‖a‖ + ‖b‖ < ln 2
* `logOnePlus_exp_sub_one`: `logOnePlus(exp a - 1) = a` for ‖a‖ < ln 2  (log ∘ exp = id)
* `norm_bch_sub_add_le`: `‖bch a b - (a + b)‖ ≤ C · (‖a‖ + ‖b‖)² · exp(‖a‖ + ‖b‖)`

## References

* [Baker, H.F., *Proc. London Math. Soc.*, 1905]
* [Campbell, J.E., *Proc. London Math. Soc.*, 1897]
* [Hausdorff, F., *Ber. Verhandl. Sächs. Akad. Wiss. Leipzig*, 1906]
-/

import BCH.LogSeries
import Mathlib.Algebra.Lie.OfAssociative

namespace BCH

noncomputable section

open scoped Nat
open NormedSpace Topology Finset

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### Norm bound for exp in Banach algebras

We prove `‖exp x‖ ≤ Real.exp ‖x‖`, which Mathlib has for ℂ but not for general
Banach algebras. The proof goes through the power series representation.
-/

section ExpNormBounds

omit [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Helper: the real exp series evaluated at r gives a HasSum to Real.exp r. -/
private lemma hasSum_real_exp (r : ℝ) :
    HasSum (fun n => (n !⁻¹ : ℝ) * r ^ n) (Real.exp r) := by
  have h := exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) r
  simp only [smul_eq_mul] at h
  rwa [congr_fun Real.exp_eq_exp_ℝ r]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma summable_real_exp_norm_shift (x : 𝔸) :
    Summable (fun n => ((n + 1) !⁻¹ : ℝ) * ‖x‖ ^ (n + 1)) :=
  (summable_nat_add_iff 1).mpr (hasSum_real_exp ‖x‖).summable

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma hasSum_real_exp_norm_shift (x : 𝔸) :
    HasSum (fun n => ((n + 1) !⁻¹ : ℝ) * ‖x‖ ^ (n + 1)) (Real.exp ‖x‖ - 1) := by
  -- Strategy: the full series sums to exp ‖x‖, its 0th term is 1,
  -- so the tail sums to exp ‖x‖ - 1.
  have h := hasSum_real_exp ‖x‖
  -- Use Summable.hasSum_iff to prove the shifted sum has the right value.
  have hsumm : Summable (fun n => ((n + 1) !⁻¹ : ℝ) * ‖x‖ ^ (n + 1)) :=
    summable_real_exp_norm_shift x
  rw [hsumm.hasSum_iff]
  -- Need: ∑' n, ((n+1)!⁻¹ * ‖x‖^(n+1)) = Real.exp ‖x‖ - 1
  -- From h: ∑' n, (n!⁻¹ * ‖x‖^n) = Real.exp ‖x‖
  have h_full := h.tsum_eq
  -- The full tsum = 0th term + shifted tsum
  have h_split : ∑' n, (n !⁻¹ : ℝ) * ‖x‖ ^ n =
      (0 !⁻¹ : ℝ) * ‖x‖ ^ 0 + ∑' n, ((n + 1) !⁻¹ : ℝ) * ‖x‖ ^ (n + 1) :=
    h.summable.tsum_eq_zero_add
  rw [h_full] at h_split
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero] at h_split
  linarith

include 𝕂 in
omit [CompleteSpace 𝔸] in
/-- The exp series term norm bound: `‖(n!)⁻¹ • x^n‖ ≤ (n!)⁻¹ * ‖x‖^n`. -/
private lemma norm_expSeries_term_le' (x : 𝔸) (n : ℕ) :
    ‖(n !⁻¹ : 𝕂) • x ^ n‖ ≤ (n !⁻¹ : ℝ) * ‖x‖ ^ n := by
  calc ‖(n !⁻¹ : 𝕂) • x ^ n‖
      ≤ ‖(n !⁻¹ : 𝕂)‖ * ‖x ^ n‖ := norm_smul_le _ _
    _ ≤ (n !⁻¹ : ℝ) * ‖x‖ ^ n := by
        gcongr
        · rw [norm_inv, RCLike.norm_natCast]
        · exact norm_pow_le x n

include 𝕂 in
omit [CompleteSpace 𝔸] in
/-- `‖exp x‖ ≤ Real.exp ‖x‖` in any complete normed algebra with `‖1‖ = 1`. -/
theorem norm_exp_le (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
  exact tsum_of_norm_bounded (hasSum_real_exp ‖x‖)
    (norm_expSeries_term_le' (𝕂 := 𝕂) x)

include 𝕂 in
/-- `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1` in any complete normed algebra with `‖1‖ = 1`. -/
theorem norm_exp_sub_one_le (x : 𝔸) : ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  -- exp x - 1 = ∑'_{n≥1} (n!)⁻¹ x^n. Bound term-by-term.
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hexp_eq : exp x = ∑' n, f n := congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x
  have h_sub : exp x - 1 = ∑' n, f (n + 1) := by
    rw [hexp_eq, hf_summ.tsum_eq_zero_add, hf0, add_sub_cancel_left]
  rw [h_sub]
  exact tsum_of_norm_bounded (hasSum_real_exp_norm_shift x)
    (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 1))

include 𝕂 in
theorem norm_exp_sub_one_sub_le (x : 𝔸) :
    ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = x := by simp [f]
  have h_sub : exp x - 1 - x = ∑' n, f (n + 2) := by
    rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
    have h1 := hf_summ.tsum_eq_zero_add; rw [hf0] at h1
    have h2 := ((summable_nat_add_iff 1).mpr hf_summ).tsum_eq_zero_add; simp only [hf1] at h2
    rw [h1, add_sub_cancel_left, h2, add_sub_cancel_left]
  rw [h_sub]
  have h_rexp := hasSum_real_exp ‖x‖
  have h_summ2 : Summable (fun n => ((n + 2) !⁻¹ : ℝ) * ‖x‖ ^ (n + 2)) :=
    (summable_nat_add_iff 2).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 2) !⁻¹ : ℝ) * ‖x‖ ^ (n + 2)) (Real.exp ‖x‖ - 1 - ‖x‖) := by
    rw [h_summ2.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2; linarith
  exact tsum_of_norm_bounded h_val (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 2))

include 𝕂 in
/-- Third-order exp remainder: `‖exp(x) - 1 - x - x²/2‖ ≤ exp(‖x‖) - 1 - ‖x‖ - ‖x‖²/2`. -/
theorem norm_exp_sub_one_sub_sub_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2‖ ≤
      Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 := by
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = x := by simp [f]
  have hf2 : f 2 = (2 : 𝕂)⁻¹ • x ^ 2 := by
    simp only [f, Nat.factorial, Nat.mul_one, Nat.cast_ofNat, pow_succ, pow_zero, one_mul]
    ring
  have h_sub : exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 = ∑' n, f (n + 3) := by
    rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
    have h1 := hf_summ.tsum_eq_zero_add; rw [hf0] at h1
    have h2 := ((summable_nat_add_iff 1).mpr hf_summ).tsum_eq_zero_add
    simp only [hf1] at h2
    have h3 := ((summable_nat_add_iff 2).mpr hf_summ).tsum_eq_zero_add
    simp only [hf2] at h3
    rw [h1, add_sub_cancel_left, h2, add_sub_cancel_left, h3, add_sub_cancel_left]
  rw [h_sub]
  have h_rexp := hasSum_real_exp ‖x‖
  have h_summ3 : Summable (fun n => ((n + 3) !⁻¹ : ℝ) * ‖x‖ ^ (n + 3)) :=
    (summable_nat_add_iff 3).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 3) !⁻¹ : ℝ) * ‖x‖ ^ (n + 3))
      (Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2) := by
    rw [h_summ3.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3
    linarith
  exact tsum_of_norm_bounded h_val (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 3))

include 𝕂 in
theorem exp_eq_one_of_norm_lt (z : 𝔸) (hz : exp z = 1) (hn : ‖z‖ < Real.log 2) :
    z = 0 := by
  have hkey : z = -(exp z - 1 - z) := by rw [hz]; simp
  have hbound : ‖z‖ ≤ Real.exp ‖z‖ - 1 - ‖z‖ := by
    calc ‖z‖ = ‖-(exp z - 1 - z)‖ := by conv_lhs => rw [hkey]
      _ = ‖exp z - 1 - z‖ := norm_neg _
      _ ≤ Real.exp ‖z‖ - 1 - ‖z‖ := norm_exp_sub_one_sub_le (𝕂 := 𝕂) z
  by_contra h
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr h
  have hexp_lt : Real.exp ‖z‖ < 2 := by
    calc Real.exp ‖z‖ < Real.exp (Real.log 2) := Real.exp_strictMono hn
      _ = 2 := Real.exp_log (by norm_num)
  have h_half : ‖z‖ < 1 / 2 := by linarith
  have h_exp_bound : Real.exp ‖z‖ * (1 - ‖z‖) ≤ 1 := by
    have h_exp := hasSum_real_exp ‖z‖
    have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) (by linarith)
    have : Real.exp ‖z‖ ≤ (1 - ‖z‖)⁻¹ := by
      calc Real.exp ‖z‖ = ∑' n, (n !⁻¹ : ℝ) * ‖z‖ ^ n := h_exp.tsum_eq.symm
        _ ≤ ∑' n, ‖z‖ ^ n := by
            exact h_exp.summable.tsum_le_tsum
              (fun n => by
                calc (n !⁻¹ : ℝ) * ‖z‖ ^ n ≤ 1 * ‖z‖ ^ n := by
                      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg z) n)
                      exact inv_le_one_of_one_le₀
                        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
                  _ = ‖z‖ ^ n := one_mul _)
              h_geom.summable
        _ = (1 - ‖z‖)⁻¹ := h_geom.tsum_eq
    calc Real.exp ‖z‖ * (1 - ‖z‖) ≤ (1 - ‖z‖)⁻¹ * (1 - ‖z‖) := by gcongr; linarith
      _ = 1 := inv_mul_cancel₀ (by linarith)
  nlinarith

include 𝕂 in
theorem commute_logOnePlus_of_commute (x a : 𝔸) (hxa : Commute x a) :
    Commute (logOnePlus (𝕂 := 𝕂) x) a := by
  unfold logOnePlus logSeriesTerm
  apply Commute.tsum_left
  intro n
  exact (hxa.pow_left (n + 1)).smul_left _

end ExpNormBounds

/-! ### Smallness condition for the BCH element -/

include 𝕂 in
/-- When `‖a‖ + ‖b‖ < ln 2`, we have `‖exp(a) · exp(b) - 1‖ < 1`.
This is the key smallness condition ensuring the log series converges. -/
theorem norm_exp_mul_exp_sub_one_lt_one (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖exp a * exp b - 1‖ < 1 := by
  -- Factor: exp(a) * exp(b) - 1 = (exp(a) - 1) * exp(b) + (exp(b) - 1)
  have hfactor : exp a * exp b - 1 = (exp a - 1) * exp b + (exp b - 1) := by
    rw [sub_mul, one_mul]; abel
  rw [hfactor]
  have hexp_a_ge : 0 ≤ Real.exp ‖a‖ - 1 := by
    linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]
  have hexp_b_pos : 0 ≤ Real.exp ‖b‖ := (Real.exp_pos _).le
  calc ‖(exp a - 1) * exp b + (exp b - 1)‖
      ≤ ‖(exp a - 1) * exp b‖ + ‖exp b - 1‖ := norm_add_le _ _
    _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ (Real.exp ‖a‖ - 1) * Real.exp ‖b‖ + (Real.exp ‖b‖ - 1) := by
        gcongr
        · exact norm_exp_sub_one_le (𝕂 := 𝕂) a
        · exact norm_exp_le (𝕂 := 𝕂) b
        · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
    _ = Real.exp (‖a‖ + ‖b‖) - 1 := by rw [Real.exp_add]; ring
    _ < 1 := by
        have : Real.exp (‖a‖ + ‖b‖) < 2 := by
          calc Real.exp (‖a‖ + ‖b‖)
              < Real.exp (Real.log 2) := Real.exp_strictMono hab
            _ = 2 := Real.exp_log (by norm_num)
        linarith

include 𝕂 in
/-- When `‖a‖ < ln 2`, we have `‖exp(a) - 1‖ < 1`. -/
theorem norm_exp_sub_one_lt_one (a : 𝔸) (ha : ‖a‖ < Real.log 2) :
    ‖exp a - 1‖ < 1 := by
  have h := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a (0 : 𝔸) (by simpa)
  simpa [exp_zero] using h

/-! ### Definition of the BCH element -/

include 𝕂 in
/-- The Baker-Campbell-Hausdorff element: the unique Z such that `exp(Z) = exp(a) · exp(b)`.
Defined as `logOnePlus(exp(a) · exp(b) - 1)` which converges when `‖a‖ + ‖b‖ < ln 2`. -/
noncomputable def bch (a b : 𝔸) : 𝔸 := logOnePlus (𝕂 := 𝕂) (exp a * exp b - 1)

/-! ### The fundamental BCH identity -/

include 𝕂 in
/-- **The structural BCH theorem**: `exp(bch a b) = exp(a) · exp(b)`.

This is the fundamental identity: the BCH element exponentiates back to the product.
The proof combines the log series convergence (from the smallness condition
`‖exp(a)·exp(b) - 1‖ < 1`) with the `exp ∘ log = id` identity from Phase 1. -/
theorem exp_bch (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    exp (bch (𝕂 := 𝕂) a b) = exp a * exp b := by
  unfold bch
  have h : ‖exp a * exp b - 1‖ < 1 :=
    norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have key := exp_logOnePlus (𝕂 := 𝕂) (exp a * exp b - 1) h
  -- key : exp (logOnePlus (exp a * exp b - 1)) = 1 + (exp a * exp b - 1)
  -- 1 + (exp a * exp b - 1) = exp a * exp b
  rw [key]; abel

/-! ### Continuity of logOnePlus on the open unit ball -/

include 𝕂 in
omit [CompleteSpace 𝔸] in
/-- Each log series term `y ↦ logSeriesTerm y n` is continuous. -/
private lemma continuous_logSeriesTerm (n : ℕ) :
    Continuous (fun y : 𝔸 => logSeriesTerm (𝕂 := 𝕂) y n) := by
  unfold logSeriesTerm
  exact continuous_const.smul (continuous_id.pow (n + 1))

/-- The geometric series `∑ (max 0 r)^(n+1)` is summable when `r < 1`. -/
private lemma summable_geometric_succ_max {r : ℝ} (hr : r < 1) :
    Summable (fun n : ℕ => (max 0 r) ^ (n + 1)) :=
  ((summable_geometric_of_lt_one (le_max_left 0 r) (max_lt (by linarith) hr)).mul_left
    (max 0 r)).congr fun n => by ring

include 𝕂 in
/-- `logOnePlus` is continuous on `closedBall 0 r` for any `r < 1`. -/
lemma continuousOn_logOnePlus {r : ℝ} (hr : r < 1) :
    ContinuousOn (logOnePlus (𝕂 := 𝕂)) (Metric.closedBall (0 : 𝔸) r) := by
  unfold logOnePlus
  apply continuousOn_tsum
  · exact fun n => (continuous_logSeriesTerm (𝕂 := 𝕂) n).continuousOn
  · exact summable_geometric_succ_max hr
  · intro n y hy
    calc ‖logSeriesTerm (𝕂 := 𝕂) y n‖
        ≤ ‖y‖ ^ (n + 1) := norm_logSeriesTerm_le (𝕂 := 𝕂) y n
      _ ≤ (max 0 r) ^ (n + 1) := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          rw [Metric.mem_closedBall, dist_zero_right] at hy
          exact hy.trans (le_max_right 0 r)

/-! ### The log ∘ exp identity -/

include 𝕂 in
/-- `logOnePlus(exp(a) - 1) = a` for `‖a‖ < ln 2`: the logarithm inverts the exponential.

The proof proceeds by a chain-of-neighborhoods argument:
1. Define `h(t) = logOnePlus(exp(ta) - 1) - ta` for `t ∈ [0,1]`.
2. Show `h(0) = 0` and `exp(h(t)) = 1` for all `t`.
3. Show `h` is continuous on `[0,1]`.
4. By uniform continuity on `[0,1]` (compact), find `δ > 0` s.t. `‖h(t) - h(s)‖ < ln 2`
   whenever `|t-s| < δ`.
5. By induction with step size `1/N < δ`: `h(k/N) = 0` for all `k ≤ N`.
6. In particular `h(1) = 0`. -/
theorem logOnePlus_exp_sub_one (a : 𝔸) (ha : ‖a‖ < Real.log 2) :
    logOnePlus (𝕂 := 𝕂) (exp a - 1) = a := by
  -- Reduce to ℝ scalars
  rw [logOnePlus_eq_real (𝕂 := 𝕂)]
  set instℝ := NormedAlgebra.restrictScalars ℝ 𝕂 𝔸
  letI : NormedAlgebra ℝ 𝔸 := instℝ
  -- Define h(t) = logOnePlus(exp(ta) - 1) - ta
  set h : ℝ → 𝔸 := fun t =>
    @logOnePlus ℝ _ 𝔸 _ instℝ (exp (t • a) - 1) - t • a with hh_def
  -- It suffices to show h(1) = 0
  suffices h1 : h 1 = 0 by
    simp only [h, one_smul] at h1
    exact sub_eq_zero.mp h1
  -- Step 1: h(0) = 0
  have h0 : h 0 = 0 := by
    simp [h, logOnePlus, logSeriesTerm, tsum_zero]
  -- Step 2: exp(h(t)) = 1 for t ∈ [0,1]
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hexp_ht : ∀ t : ℝ, t * ‖a‖ < Real.log 2 → 0 ≤ t →
      exp (h t) = 1 := by
    intro t ht ht_nn
    -- exp(logOnePlus(exp(ta)-1)) = exp(ta) from exp_logOnePlus
    have hnorm : ‖exp (t • a) - 1‖ < 1 := by
      apply @norm_exp_sub_one_lt_one ℝ _ 𝔸 _ instℝ _ _
      calc ‖t • a‖ ≤ ‖t‖ * ‖a‖ := norm_smul_le t a
        _ = |t| * ‖a‖ := by rw [Real.norm_eq_abs]
        _ = t * ‖a‖ := by rw [abs_of_nonneg ht_nn]
        _ < Real.log 2 := ht
    have hexp_log := @exp_logOnePlus ℝ _ 𝔸 _ instℝ _ _ (exp (t • a) - 1) hnorm
    -- logOnePlus(exp(ta)-1) commutes with a
    have hcomm_exp_a : Commute (exp (t • a) - 1) a := by
      apply Commute.sub_left _ (Commute.one_left a)
      exact (Commute.refl a).smul_left t |>.exp_left
    have hcomm : Commute (@logOnePlus ℝ _ 𝔸 _ instℝ (exp (t • a) - 1)) a :=
      @commute_logOnePlus_of_commute ℝ _ 𝔸 _ instℝ _ _ (exp (t • a) - 1) a hcomm_exp_a
    -- exp(L - ta) = exp(L) * exp(-ta) since L commutes with ta
    have hcomm_ta : Commute (@logOnePlus ℝ _ 𝔸 _ instℝ (exp (t • a) - 1)) (t • a) :=
      hcomm.smul_right t
    set L := @logOnePlus ℝ _ 𝔸 _ instℝ (exp (t • a) - 1)
    show exp (L - t • a) = 1
    rw [show L - t • a = L + (-(t • a)) from sub_eq_add_neg L (t • a),
        exp_add_of_commute (hcomm_ta.neg_right), hexp_log,
        show (1 + (exp (t • a) - 1)) = exp (t • a) from by abel,
        ← exp_add_of_commute ((Commute.refl (t • a)).neg_right),
        add_neg_cancel, exp_zero]
  -- Step 3: h is continuous on [0, 1]
  have hcont : ContinuousOn h (Set.Icc 0 1) := by
    -- h = logOnePlus ∘ (exp(·a) - 1) - (· • a)
    apply ContinuousOn.sub
    · -- logOnePlus(exp(ta)-1) is continuous
      -- The inner function maps [0,1] into closedBall 0 ρ where ρ = exp(‖a‖)-1 < 1
      set ρ := Real.exp ‖a‖ - 1 with hρ_def
      have hρ_lt : ρ < 1 := by
        have : Real.exp ‖a‖ < 2 := by
          calc Real.exp ‖a‖ < Real.exp (Real.log 2) := Real.exp_strictMono ha
            _ = 2 := Real.exp_log (by norm_num)
        linarith
      -- Inner function maps [0,1] into closedBall 0 ρ
      have hmaps : Set.MapsTo (fun t : ℝ => exp (t • a) - 1)
          (Set.Icc 0 1) (Metric.closedBall (0 : 𝔸) ρ) := by
        intro t ht
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖exp (t • a) - 1‖
            ≤ Real.exp ‖t • a‖ - 1 := @norm_exp_sub_one_le ℝ _ 𝔸 _ instℝ _ _ (t • a)
          _ ≤ Real.exp (t * ‖a‖) - 1 := by
              gcongr
              calc ‖t • a‖ ≤ |t| * ‖a‖ := norm_smul_le t a
                _ = t * ‖a‖ := by rw [abs_of_nonneg ht.1]
          _ ≤ Real.exp (1 * ‖a‖) - 1 := by
              gcongr; exact ht.2
          _ = ρ := by rw [one_mul]
      -- Inner function is continuous
      have hinner_cont : ContinuousOn (fun t : ℝ => exp (t • a) - 1) (Set.Icc 0 1) :=
        ContinuousOn.sub
          (NormedSpace.exp_continuous.continuousOn.comp
            ((continuous_id.smul continuous_const).continuousOn) (Set.mapsTo_univ _ _))
          continuousOn_const
      exact ContinuousOn.comp (continuousOn_logOnePlus (𝕂 := ℝ) hρ_lt) hinner_cont hmaps
    · exact (continuous_id.smul continuous_const).continuousOn
  -- Step 4-6: Chain of neighborhoods argument
  -- By uniform continuity on [0,1], find δ
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have huc := hcompact.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (Real.log 2) (Real.log_pos (by norm_num))
  -- Choose N with 1/N < δ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN_pos : 0 < N := by
    rcases N with _ | n
    · simp at hN; linarith [div_pos one_pos hδ_pos]
    · exact Nat.succ_pos n
  -- Induction: h(k/N) = 0 for all k ≤ N
  suffices hind : ∀ k : ℕ, k ≤ N → h (k / N) = 0 by
    have := hind N le_rfl
    rwa [show (N : ℝ) / N = 1 from div_self (Nat.cast_ne_zero.mpr (by omega))] at this
  intro k hk
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have hk_le : k ≤ N := by omega
    have hprev := ih hk_le
    -- Membership in [0,1]
    have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have hkN_mem : (k : ℝ) / N ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg k) hN_pos_real.le,
       div_le_one_of_le₀ (Nat.cast_le.mpr hk_le) hN_pos_real.le⟩
    have hk1N_mem : ((k+1 : ℕ) : ℝ) / N ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hN_pos_real.le,
       div_le_one_of_le₀ (Nat.cast_le.mpr hk) hN_pos_real.le⟩
    -- |(k+1)/N - k/N| = 1/N < δ
    have h1N_lt : (1 : ℝ) / N < δ := by
      rw [one_div]
      exact (inv_lt_comm₀ hδ_pos hN_pos_real).mp (by rwa [one_div] at hN)
    have hdist' : dist ((↑(k + 1) : ℝ) / ↑N) (↑k / ↑N) < δ := by
      rw [dist_comm, Real.dist_eq, show (k : ℝ) / N - ((k + 1 : ℕ) : ℝ) / N = -(1 / N) from by
        push_cast; field_simp; ring, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / N)]
      exact h1N_lt
    -- Apply uniform continuity
    have hnorm_small : ‖h ((k+1 : ℕ) / N) - h (k / N)‖ < Real.log 2 := by
      rw [← dist_eq_norm]
      exact hδ _ hk1N_mem _ hkN_mem hdist'
    -- Since h(k/N) = 0, ‖h((k+1)/N)‖ < ln 2
    rw [hprev, sub_zero] at hnorm_small
    -- exp(h((k+1)/N)) = 1
    have hexp1 : exp (h ((k+1 : ℕ) / N)) = 1 :=
      hexp_ht _ (by calc ((k+1 : ℕ) : ℝ) / N * ‖a‖
            ≤ 1 * ‖a‖ := by gcongr; exact hk1N_mem.2
          _ = ‖a‖ := one_mul _
          _ < Real.log 2 := ha) hk1N_mem.1
    -- By exp_eq_one_of_norm_lt
    exact exp_eq_one_of_norm_lt (𝕂 := 𝕂) _ hexp1 hnorm_small

/-! ### Norm estimate for `bch a b - (a + b)` -/

include 𝕂 in
/-- The BCH remainder bound: `‖bch(a,b) - (a+b)‖` is quadratically small.

More precisely: `‖bch(a,b) - (a+b)‖ ≤ 3s²/(2-eˢ)` where `s = ‖a‖ + ‖b‖`.
The bound diverges at `s = ln 2` (the radius of convergence) and satisfies
`3s²/(2-eˢ) ~ 3s²/2` for small `s`.

The proof decomposes `bch(a,b) - (a+b) = (logOnePlus(y) - y) + (y - (a+b))`
where `y = exp(a)·exp(b) - 1`, bounds each piece, and uses the key inequality
`exp(s)·(1+s) ≤ 1 + 2s + 3s²` for `s ∈ [0, ln 2)`. -/
theorem norm_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b)‖ ≤
      3 * (‖a‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set y := exp a * exp b - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have h_denom_pos : 0 < 2 - Real.exp s := by linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have : y = (exp a - 1) * exp b + (exp b - 1) := by rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [this]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp ‖a‖ - 1) * Real.exp ‖b‖ + (Real.exp ‖b‖ - 1) := by
          have h1 := norm_exp_sub_one_le (𝕂 := 𝕂) a
          have h2 := norm_exp_le (𝕂 := 𝕂) b
          have h3 := norm_exp_sub_one_le (𝕂 := 𝕂) b
          apply add_le_add
          · exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a])
          · exact h3
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  -- Decomposition
  have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) =
      (logOnePlus (𝕂 := 𝕂) y - y) + (y - (a + b)) := by unfold bch; abel
  -- Part 1: log remainder
  have hpart1 : ‖logOnePlus (𝕂 := 𝕂) y - y‖ ≤ (Real.exp s - 1) ^ 2 / (2 - Real.exp s) := by
    calc _ ≤ ‖y‖ ^ 2 / (1 - ‖y‖) := norm_logOnePlus_sub_le (𝕂 := 𝕂) y hy_lt
      _ ≤ (Real.exp s - 1) ^ 2 / (2 - Real.exp s) := by
          exact div_le_div₀ (sq_nonneg _)
            (pow_le_pow_left₀ (norm_nonneg _) hy_le _) h_denom_pos (by linarith)
  -- Part 2: exp factorization
  have hpart2 : ‖y - (a + b)‖ ≤ Real.exp s - 1 - s := by
    have hident : y - (a + b) = (exp a - 1) * (exp b - 1) + (exp a - 1 - a) + (exp b - 1 - b) := by
      rw [hy_def]; noncomm_ring
    rw [hident]
    calc _ ≤ ‖(exp a - 1) * (exp b - 1)‖ + ‖exp a - 1 - a‖ + ‖exp b - 1 - b‖ := by
          calc _ ≤ ‖(exp a - 1) * (exp b - 1) + (exp a - 1 - a)‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) +
          (Real.exp ‖a‖ - 1 - ‖a‖) + (Real.exp ‖b‖ - 1 - ‖b‖) := by
          have ha1 := norm_exp_sub_one_le (𝕂 := 𝕂) a
          have hb1 := norm_exp_sub_one_le (𝕂 := 𝕂) b
          have ha2 := norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
          have hb2 := norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
          have ha_nn : 0 ≤ Real.exp ‖a‖ - 1 := by
            linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]
          have hb_nn : 0 ≤ Real.exp ‖b‖ - 1 := by
            linarith [Real.add_one_le_exp ‖b‖, norm_nonneg b]
          apply add_le_add (add_le_add _ ha2) hb2
          exact (norm_mul_le _ _).trans (mul_le_mul ha1 hb1 (norm_nonneg _) ha_nn)
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  -- Combine and bound: (E-1)²/(2-E) + (E-1-s) ≤ 3s²/(2-E)
  -- Equivalent to: (E-1)² + (E-1-s)(2-E) ≤ 3s², i.e., E(1+s) - (1+2s) ≤ 3s²
  rw [hdecomp]
  calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y‖ + ‖y - (a + b)‖ := norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 2 / (2 - Real.exp s) + (Real.exp s - 1 - s) :=
        add_le_add hpart1 hpart2
    _ ≤ 3 * s ^ 2 / (2 - Real.exp s) := by
        -- Need: (E-1)²/(2-E) + (E-1-s) ≤ 3s²/(2-E)
        -- Combine LHS into single fraction, then compare numerators
        rw [div_add' _ _ _ (ne_of_gt h_denom_pos)]
        apply div_le_div_of_nonneg_right _ h_denom_pos.le
        -- Goal: (E-1)² + (E-1-s)*(2-E) ≤ 3s²
        set E := Real.exp s
        -- s < 1 because 1+s ≤ E < 2
        have hs_lt_one : s < 1 := by linarith [Real.add_one_le_exp s]
        -- E ≤ 1+s+s² from Real.norm_exp_sub_one_sub_id_le (for |s| ≤ 1)
        have hE_taylor : E - 1 - s ≤ s ^ 2 := by
          have h := Real.norm_exp_sub_one_sub_id_le (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.add_one_le_exp s]),
              Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
          exact h
        -- E ≤ 1+s+s²
        have hE_le : E ≤ 1 + s + s ^ 2 := by linarith
        -- E(1+s) ≤ (1+s+s²)(1+s) = 1+2s+2s²+s³ ≤ 1+2s+3s² (since s³ ≤ s²)
        -- (E-1)² + (E-1-s)(2-E) = E(1+s) - (1+2s) by ring
        -- So need E(1+s) - (1+2s) ≤ 3s²
        nlinarith [sq_nonneg s, mul_self_nonneg (s * s),
                   show s ^ 3 ≤ s ^ 2 from by
                     calc s ^ 3 = s ^ 2 * s := by ring
                       _ ≤ s ^ 2 * 1 := by nlinarith [sq_nonneg s]
                       _ = s ^ 2 := by ring]
/-! ### Cubic Taylor remainder bound for exp -/

/-- `exp(s)-1-s-s²/2 ≤ s³/(6(1-s))` for `0 ≤ s < 1`,
from the termwise bound `1/n! ≤ 1/6` for `n ≥ 3`. -/
private lemma real_exp_third_order_le_div {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    Real.exp s - 1 - s - s ^ 2 / 2 ≤ s ^ 3 / (6 * (1 - s)) := by
  -- exp(s) - 1 - s - s²/2 = Σ_{n≥3} sⁿ/n! ≤ Σ_{n≥3} sⁿ/6 = s³/(6(1-s))
  have h_rexp := hasSum_real_exp s
  -- The n≥3 tail: Σ_{n≥0} s^(n+3)/(n+3)! = exp(s)-1-s-s²/2
  have h_summ3 : Summable (fun n => ((n + 3) !⁻¹ : ℝ) * s ^ (n + 3)) :=
    (summable_nat_add_iff 3).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 3) !⁻¹ : ℝ) * s ^ (n + 3))
      (Real.exp s - 1 - s - s ^ 2 / 2) := by
    rw [h_summ3.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3
    linarith
  -- The comparison: Σ_{n≥0} s^(n+3)/6 = s³/(6(1-s))
  have h_geom_summ : Summable (fun n => s ^ (n + 3) / 6) := by
    apply Summable.div_const
    exact (summable_geometric_of_lt_one hs hs1).mul_left (s ^ 3) |>.congr fun n => by ring
  -- Termwise bound: (n+3)!⁻¹ ≤ 6⁻¹ since (n+3)! ≥ 3! = 6
  have hterm : ∀ n, ((n + 3) !⁻¹ : ℝ) * s ^ (n + 3) ≤ s ^ (n + 3) * (6 : ℝ)⁻¹ := by
    intro n
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (n + 3)!) (by positivity : (0 : ℝ) < 6)]
    have : (3 : ℕ)! ≤ (n + 3)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  -- The comparison series sums to s³/(6(1-s))
  have h_geom : HasSum (fun n => s ^ (n + 3) * (6 : ℝ)⁻¹) (s ^ 3 * (1 - s)⁻¹ * (6 : ℝ)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hs hs1).mul_left (s ^ 3)
    have h_eq : (fun n => s ^ 3 * s ^ n) = (fun n => s ^ (n + 3)) := by ext n; ring
    rw [h_eq] at hg
    exact hg.mul_right (6 : ℝ)⁻¹
  calc Real.exp s - 1 - s - s ^ 2 / 2
      = ∑' n, ((n + 3) !⁻¹ : ℝ) * s ^ (n + 3) := h_val.tsum_eq.symm
    _ ≤ ∑' n, (s ^ (n + 3) * (6 : ℝ)⁻¹) :=
        h_summ3.tsum_le_tsum hterm h_geom.summable
    _ = s ^ 3 * (1 - s)⁻¹ * (6 : ℝ)⁻¹ := h_geom.tsum_eq
    _ = s ^ 3 / (6 * (1 - s)) := by rw [div_eq_mul_inv, mul_inv_rev]; ring

/-- For `0 ≤ s` with `s < 5/6`, the third-order Taylor remainder satisfies
`exp(s)-1-s-s²/2 ≤ s³`. -/
lemma real_exp_third_order_le_cube {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 5 / 6) :
    Real.exp s - 1 - s - s ^ 2 / 2 ≤ s ^ 3 := by
  have hs_lt1 : s < 1 := by linarith
  calc Real.exp s - 1 - s - s ^ 2 / 2
      ≤ s ^ 3 / (6 * (1 - s)) := real_exp_third_order_le_div hs hs_lt1
    _ ≤ s ^ 3 := by
        rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 6 * (1 - s))]
        nlinarith [sq_nonneg s, pow_nonneg hs 3]

/-! ### Commutator extraction: BCH to second order -/

set_option maxHeartbeats 16000000 in
include 𝕂 in
/-- **Commutator extraction**: the BCH element equals `a + b + [a,b]/2` up to a cubic remainder.

`‖bch(a,b) - (a+b) - (ab-ba)/2‖ ≤ 10·s³/(2-eˢ)` where `s = ‖a‖+‖b‖`.
This shows the leading non-commutative correction to `bch` is the Lie bracket `[a,b]/2`. -/
theorem norm_bch_sub_add_sub_bracket_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a)‖ ≤
      10 * (‖a‖ + ‖b‖) ^ 3 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set y := exp a * exp b - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖; set β := ‖b‖
  -- Basic setup
  have hs_nn : 0 ≤ s := by positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have : y = (exp a - 1) * exp b + (exp b - 1) := by rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [this]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          apply add_le_add
          · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
              (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hs56 : s < 5 / 6 := by
    calc s < Real.log 2 := hab
      _ ≤ 5 / 6 := by
          rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
          calc (2 : ℝ) ≤ 1 + 5 / 6 + (5 / 6) ^ 2 / 2 := by norm_num
            _ ≤ Real.exp (5 / 6) := Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hs1 : s < 1 := by linarith
  -- Auxiliary definitions
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set P := y - (a + b) with hP_def
  set E₁ := exp a - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := exp b - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  -- Algebraic identities
  have hP_factor : P = (exp a - 1) * (exp b - 1) + D₁ + D₂ := by
    rw [hP_def, hy_def, hD₁_def, hD₂_def]; noncomm_ring
  have hP_expand : P = a * b + a * D₂ + D₁ * b + D₁ * D₂ + D₁ + D₂ := by
    rw [hP_factor, hD₁_def, hD₂_def]; noncomm_ring
  -- Piece B identity: y-(a+b)-½(ab-ba)-½y² = ½•W where W is defined below
  set W := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
    (a + b) * P - P * (a + b) - P ^ 2 with hW_def
  have hpieceB_eq : y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 =
      (2 : 𝕂)⁻¹ • W := by
    have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
    suffices h : (2 : 𝕂) • (y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2) =
        (2 : 𝕂) • ((2 : 𝕂)⁻¹ • W) by
      have hinj : Function.Injective ((2 : 𝕂) • · : 𝔸 → 𝔸) := by
        intro x₀ y₀ hxy
        have := congrArg ((2 : 𝕂)⁻¹ • ·) hxy
        simp only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] at this
        exact this
      exact hinj h
    -- After clearing ½, goal: 2•LHS = W
    rw [smul_smul, mul_inv_cancel₀ h2ne, one_smul]
    -- Unfold all definitions and clear smul via two_smul
    rw [hW_def, hP_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hy_def]
    simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h2ne, one_smul, two_smul]
    noncomm_ring
  -- Norm bounds
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
    rw [hP_factor]
    calc ‖(exp a - 1) * (exp b - 1) + D₁ + D₂‖
        ≤ ‖(exp a - 1) * (exp b - 1)‖ + ‖D₁‖ + ‖D₂‖ := by
          calc _ ≤ ‖(exp a - 1) * (exp b - 1) + D₁‖ + ‖D₂‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ (Real.exp α - 1) * (Real.exp β - 1) +
          (Real.exp α - 1 - α) + (Real.exp β - 1 - β) := by
          gcongr
          calc ‖(exp a - 1) * (exp b - 1)‖
              ≤ ‖exp a - 1‖ * ‖exp b - 1‖ := norm_mul_le _ _
            _ ≤ _ := mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a)
                (norm_exp_sub_one_le (𝕂 := 𝕂) b) (norm_nonneg _)
                (by linarith [Real.add_one_le_exp α])
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  -- Real Taylor bounds
  have hα56 : α < 5 / 6 := lt_of_le_of_lt hα_le hs56
  have hβ56 : β < 5 / 6 := lt_of_le_of_lt hβ_le hs56
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn hα56
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn hβ56
  have hEa_nn : 0 ≤ Real.exp α - 1 - α - α ^ 2 / 2 := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn]
  have hEb_nn : 0 ≤ Real.exp β - 1 - β - β ^ 2 / 2 := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn]
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖α‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hα_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.exp α - 1 - α),
         Real.norm_eq_abs, abs_of_nonneg hα_nn] at h
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖β‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hβ_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.exp β - 1 - β),
         Real.norm_eq_abs, abs_of_nonneg hβ_nn] at h
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.add_one_le_exp s]),
         Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  -- ‖½‖ = 1/2
  have h_half : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Piece A bound
  have hpieceA : ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2‖ ≤
      (Real.exp s - 1) ^ 3 / (2 - Real.exp s) :=
    calc _ ≤ ‖y‖ ^ 3 / (1 - ‖y‖) := norm_logOnePlus_sub_sub_le (𝕂 := 𝕂) y hy_lt
      _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
          (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
  -- Piece B bound: ‖½•W‖ ≤ ½‖W‖ and bound ‖W‖
  have hpieceB : ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2‖ ≤
      (Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
      (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
        (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) +
      s * (Real.exp s - 1 - s) + (Real.exp s - 1 - s) ^ 2 / 2 := by
    rw [hpieceB_eq]
    -- ‖½•W‖ ≤ ½*‖W‖
    have hsmul : ‖(2 : 𝕂)⁻¹ • W‖ ≤ (2 : ℝ)⁻¹ * ‖W‖ := by
      calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖W‖ := norm_smul_le _ _
        _ = _ := by rw [h_half]
    -- ‖W‖ bound via triangle inequality
    set T := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) with hT_def
    have hW_eq : W = T - (a + b) * P - P * (a + b) - P ^ 2 := hW_def
    have hW_bound : ‖W‖ ≤ ‖T‖ + ‖(a + b) * P‖ + ‖P * (a + b)‖ + ‖P ^ 2‖ := by
      rw [hW_eq]
      have hab1 : T - (a + b) * P - P * (a + b) - P ^ 2 =
          (T - (a + b) * P - P * (a + b)) + (-(P ^ 2)) := by abel
      have hab2 : T - (a + b) * P - P * (a + b) =
          (T - (a + b) * P) + (-(P * (a + b))) := by abel
      have hab3 : T - (a + b) * P = T + (-((a + b) * P)) := by abel
      calc ‖T - (a + b) * P - P * (a + b) - P ^ 2‖
          = ‖(T - (a + b) * P - P * (a + b)) + (-(P ^ 2))‖ := by rw [hab1]
        _ ≤ ‖T - (a + b) * P - P * (a + b)‖ + ‖-(P ^ 2)‖ := norm_add_le _ _
        _ = ‖T - (a + b) * P - P * (a + b)‖ + ‖P ^ 2‖ := by rw [norm_neg]
        _ ≤ (‖T - (a + b) * P‖ + ‖P * (a + b)‖) + ‖P ^ 2‖ := by
            gcongr; rw [hab2]; calc _ ≤ _ + ‖-(P * (a + b))‖ := norm_add_le _ _
              _ = _ := by rw [norm_neg]
        _ ≤ (‖T‖ + ‖(a + b) * P‖ + ‖P * (a + b)‖) + ‖P ^ 2‖ := by
            gcongr; rw [hab3]; calc _ ≤ _ + ‖-((a + b) * P)‖ := norm_add_le _ _
              _ = _ := by rw [norm_neg]
        _ = ‖T‖ + ‖(a + b) * P‖ + ‖P * (a + b)‖ + ‖P ^ 2‖ := by ring
    -- Bound each component of ‖W‖
    have hT_le : ‖T‖ ≤ 2 * (‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖) := by
      calc ‖T‖ = ‖(2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂)‖ := rfl
        _ ≤ ‖(2 : 𝕂)‖ * ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖ := norm_smul_le _ _
        _ = 2 * ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖ := by rw [RCLike.norm_ofNat]
        _ ≤ 2 * (‖E₁‖ + ‖E₂‖ + ‖a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖) := by
            gcongr
            calc _ ≤ ‖E₁ + E₂ + a * D₂ + D₁ * b‖ + ‖D₁ * D₂‖ := norm_add_le _ _
              _ ≤ ‖E₁ + E₂ + a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖ := by gcongr; exact norm_add_le _ _
              _ ≤ ‖E₁ + E₂‖ + ‖a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖ := by gcongr; exact norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
        _ ≤ 2 * (‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖) := by
            gcongr <;> exact norm_mul_le _ _
    have habP : ‖(a + b) * P‖ ≤ s * ‖P‖ := by
      calc _ ≤ ‖a + b‖ * ‖P‖ := norm_mul_le _ _
        _ ≤ (α + β) * ‖P‖ := by gcongr; exact norm_add_le a b
    have hPab : ‖P * (a + b)‖ ≤ ‖P‖ * s := by
      calc _ ≤ ‖P‖ * ‖a + b‖ := norm_mul_le _ _
        _ ≤ ‖P‖ * (α + β) := by gcongr; exact norm_add_le a b
    have hP2 : ‖P ^ 2‖ ≤ ‖P‖ ^ 2 := norm_pow_le P 2
    -- Substitute real bounds
    have hQ_le : ‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖ ≤
        (Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
        (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
          (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) := by
      have h1 : α * ‖D₂‖ ≤ α * (Real.exp β - 1 - β) :=
        mul_le_mul_of_nonneg_left hD₂_le hα_nn
      have h2 : ‖D₁‖ * β ≤ (Real.exp α - 1 - α) * β :=
        mul_le_mul_of_nonneg_right hD₁_le hβ_nn
      have h3 : ‖D₁‖ * ‖D₂‖ ≤ (Real.exp α - 1 - α) * (Real.exp β - 1 - β) :=
        mul_le_mul hD₁_le hD₂_le (norm_nonneg _) hDa_nn
      linarith [hE₁_le, hE₂_le]
    -- Combine: ½ * (2*Q + 2s*‖P‖ + ‖P‖²) = Q + s*‖P‖ + ‖P‖²/2
    calc ‖(2 : 𝕂)⁻¹ • W‖ ≤ (2 : ℝ)⁻¹ * ‖W‖ := hsmul
      _ ≤ (2 : ℝ)⁻¹ * (‖T‖ + ‖(a + b) * P‖ + ‖P * (a + b)‖ + ‖P ^ 2‖) := by
          gcongr
      _ ≤ (2 : ℝ)⁻¹ * (2 * (‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖) +
            s * ‖P‖ + ‖P‖ * s + ‖P‖ ^ 2) := by
          gcongr
      _ ≤ (2 : ℝ)⁻¹ * (2 * ((Real.exp α - 1 - α - α ^ 2 / 2) +
            (Real.exp β - 1 - β - β ^ 2 / 2) +
            (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
              (Real.exp α - 1 - α) * (Real.exp β - 1 - β))) +
            s * (Real.exp s - 1 - s) + (Real.exp s - 1 - s) * s +
            (Real.exp s - 1 - s) ^ 2) := by
          nlinarith [hQ_le, hP_le, pow_le_pow_left₀ (norm_nonneg P) hP_le 2]
      _ = _ := by ring
  -- Decomposition: bch-(a+b)-½[a,b] = pieceA + pieceB
  have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) =
      (logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2) +
      (y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2) := by
    unfold bch; abel
  rw [hdecomp]
  calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2‖ +
          ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2‖ :=
        norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 3 / (2 - Real.exp s) +
        ((Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
         (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
           (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) +
         s * (Real.exp s - 1 - s) + (Real.exp s - 1 - s) ^ 2 / 2) :=
        add_le_add hpieceA hpieceB
    _ ≤ 10 * s ^ 3 / (2 - Real.exp s) := by
        rw [div_add' _ _ _ (ne_of_gt hdenom)]
        apply div_le_div_of_nonneg_right _ hdenom.le
        -- Goal: (E-1)³ + RB*(2-E) ≤ 10s³
        set E := Real.exp s
        have hE_le : E ≤ 1 + s + s ^ 2 := by linarith [hEs2]
        have hE1_nn : 0 ≤ E - 1 := by linarith [Real.add_one_le_exp s]
        have hE1_le : E - 1 ≤ s + s ^ 2 := by linarith
        -- Prepare auxiliary bounds for nlinarith
        have hα3s3 : α ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hα_nn hα_le 3
        have hβ3s3 : β ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hβ_nn hβ_le 3
        have hαβ2 : α * β ^ 2 ≤ s ^ 3 := by nlinarith [sq_nonneg β]
        have hα2β : α ^ 2 * β ≤ s ^ 3 := by nlinarith [sq_nonneg α]
        have hEs4 : (E - 1 - s) ^ 2 ≤ s ^ 4 := by nlinarith [hEs2]
        have hs4s3 : s ^ 4 ≤ s ^ 3 := by nlinarith [sq_nonneg s, pow_nonneg hs_nn 3]
        -- Bound (E-1)³ ≤ (s+s²)³ ≤ s³(1+s)³ ≤ s³·8 for s < 1
        -- Actually, (E-1)³ ≤ s³ + 3s⁴ + 3s⁵ + s⁶ ≤ s³ + 3s³ + 3s³ + s³ = 8s³
        have hE13 : (E - 1) ^ 3 ≤ (s + s ^ 2) ^ 3 :=
          pow_le_pow_left₀ hE1_nn hE1_le 3
        -- (s+s²)³ = s³(1+s)³ ≤ s³·8 but need to expand
        -- (s+s²)³ = s³+3s⁴+3s⁵+s⁶ ≤ s³+3s³+3s³+s³ = 8s³ (using s^k ≤ s³ for k≥3, s≤1)
        have hs5 : s ^ 5 ≤ s ^ 3 := by nlinarith [sq_nonneg s, pow_nonneg hs_nn 3]
        have hs6 : s ^ 6 ≤ s ^ 3 := by nlinarith [sq_nonneg s, pow_nonneg hs_nn 3]
        -- Expand (s+s²)³
        have hexp3 : (s + s ^ 2) ^ 3 = s ^ 3 + 3 * s ^ 4 + 3 * s ^ 5 + s ^ 6 := by ring
        -- RB*(2-E) bound: each term of RB times (2-E)≤1 gives cubic bounds
        have h2E_le : 2 - E ≤ 1 := by linarith [Real.add_one_le_exp s]
        have h2E_nn : 0 ≤ 2 - E := hdenom.le
        -- Individual RB terms times (2-E)
        have hRB1 : (Real.exp α - 1 - α - α ^ 2 / 2) * (2 - E) ≤ α ^ 3 :=
          calc _ ≤ (Real.exp α - 1 - α - α ^ 2 / 2) * 1 := by nlinarith
            _ = _ := mul_one _
            _ ≤ α ^ 3 := hEa3
        have hRB2 : (Real.exp β - 1 - β - β ^ 2 / 2) * (2 - E) ≤ β ^ 3 :=
          calc _ ≤ (Real.exp β - 1 - β - β ^ 2 / 2) * 1 := by nlinarith
            _ = _ := mul_one _
            _ ≤ β ^ 3 := hEb3
        -- More RB term bounds times (2-E)
        have hRB3 : α * (Real.exp β - 1 - β) * (2 - E) ≤ α * β ^ 2 := by
          have : α * (Real.exp β - 1 - β) * (2 - E) ≤ α * (Real.exp β - 1 - β) * 1 :=
            mul_le_mul_of_nonneg_left h2E_le (mul_nonneg hα_nn hDb_nn)
          linarith [mul_le_mul_of_nonneg_left hDb2 hα_nn]
        have hRB4 : (Real.exp α - 1 - α) * β * (2 - E) ≤ α ^ 2 * β := by
          have : (Real.exp α - 1 - α) * β * (2 - E) ≤ (Real.exp α - 1 - α) * β * 1 :=
            mul_le_mul_of_nonneg_left h2E_le (mul_nonneg hDa_nn hβ_nn)
          linarith [mul_le_mul_of_nonneg_right hDa2 hβ_nn]
        have hRB5 : (Real.exp α - 1 - α) * (Real.exp β - 1 - β) * (2 - E) ≤
            α ^ 2 * β ^ 2 := by
          have : (Real.exp α - 1 - α) * (Real.exp β - 1 - β) * (2 - E) ≤
            (Real.exp α - 1 - α) * (Real.exp β - 1 - β) * 1 :=
            mul_le_mul_of_nonneg_left h2E_le (mul_nonneg hDa_nn hDb_nn)
          have : (Real.exp α - 1 - α) * (Real.exp β - 1 - β) ≤ α ^ 2 * β ^ 2 :=
            mul_le_mul hDa2 hDb2 hDb_nn (by positivity)
          linarith
        have hαβ_le_s : α * β ≤ s ^ 2 := by nlinarith [sq_nonneg (α - β)]
        have hαβ_nn : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
        have hα2β2 : α ^ 2 * β ^ 2 ≤ s ^ 3 := by
          have h1 : α ^ 2 * β ^ 2 = (α * β) * (α * β) := by ring
          have h2 : (α * β) * (α * β) ≤ s ^ 2 * s := by nlinarith
          linarith [show s ^ 2 * s = s ^ 3 from by ring]
        have hRB6 : s * (E - 1 - s) * (2 - E) ≤ s ^ 3 := by
          calc _ ≤ s * (E - 1 - s) * 1 := by nlinarith [mul_nonneg hs_nn hEs_nn]
            _ = s * (E - 1 - s) := mul_one _
            _ ≤ s * s ^ 2 := by nlinarith
            _ = s ^ 3 := by ring
        have hRB7 : (E - 1 - s) ^ 2 / 2 * (2 - E) ≤ s ^ 3 / 2 := by
          calc _ ≤ (E - 1 - s) ^ 2 / 2 * 1 := by nlinarith [sq_nonneg (E - 1 - s)]
            _ = (E - 1 - s) ^ 2 / 2 := mul_one _
            _ ≤ s ^ 4 / 2 := by nlinarith [hEs4]
            _ ≤ s ^ 3 / 2 := by nlinarith [hs4s3]
        -- Total bound: (E-1)³ + RB*(2-E) ≤ 8s³ + (s³+s³+s³+s³+s³+s³) = ... ≤ 10s³
        -- We bound (E-1)³ ≤ (s+s²)³ = s³+3s⁴+3s⁵+s⁶ ≤ s³+3s³+3s³+s³ = 8s³
        -- (E-1)³ ≤ s³(1+s)³ and (1+s)³ ≤ 7 for s ≤ 5/6
        -- since (1+5/6)³ = (11/6)³ = 1331/216 ≈ 6.16 < 7
        have h1s3 : (1 + s) ^ 3 ≤ 13 / 2 := by nlinarith [sq_nonneg s, sq_nonneg (s - 5/6)]
        have hE13_bound : (E - 1) ^ 3 ≤ 13 / 2 * s ^ 3 := by
          calc (E - 1) ^ 3 ≤ (s + s ^ 2) ^ 3 := hE13
            _ = s ^ 3 * (1 + s) ^ 3 := by ring
            _ ≤ s ^ 3 * (13 / 2) := mul_le_mul_of_nonneg_left h1s3 (pow_nonneg hs_nn 3)
            _ = 13 / 2 * s ^ 3 := by ring
        -- Distribute and bound RB*(2-E)
        -- RB = Ea + Eb + (αDb+Daβ+DaDb) + s(E-1-s) + (E-1-s)²/2
        -- RB*(2-E) ≤ Ea*(2-E) + Eb*(2-E) + ... (since all terms and (2-E) are non-negative)
        -- But this needs distributing the product first. Use:
        -- (a+b+c+d+e)*(2-E) = a(2-E)+b(2-E)+c(2-E)+d(2-E)+e(2-E)
        -- For this we need linearity, which nlinarith should handle.
        -- Total: ≤ 8s³ + α³ + β³ + αβ² + α²β + α²β² + s³ + s³ = 8s³ + 2s³ = 10s³
        -- (using α³+β³ ≤ 2s³, αβ² ≤ s³, α²β ≤ s³, α²β² ≤ s³, etc.)
        -- Bound the full RB*(2-E) by distributing
        -- RB*(2-E) = [Ea+Eb+(αDb+Daβ+DaDb)+s(E-1-s)+(E-1-s)²/2]*(2-E)
        -- ≤ Ea(2-E) + Eb(2-E) + αDb(2-E) + Daβ(2-E) + DaDb(2-E) + s(E-1-s)(2-E) + (E-1-s)²/2(2-E)
        -- ≤ α³ + β³ + αβ² + α²β + α²β² + s³ + s³   (from above bounds)
        -- ≤ s³ + s³ + s³ + s³ + s³ + s³ + s³ = 7s³
        -- But we need to account for the product expansion.
        -- The key is: (Ea + Eb + X + Y + Z)*(2-E) ≤ Ea(2-E) + Eb(2-E) + ...
        -- since all terms and (2-E) are non-negative.
        -- Pre-expand the product as: sum of (term_i * (2-E))
        -- Total: (E-1)³ + RB*(2-E) ≤ 8s³ + 2s³ = 10s³
        -- We prove: RB*(2-E) ≤ 2s³
        -- by: each RB_i*(2-E) ≤ cubic in s, and sum of all ≤ 2s³
        -- Manual bound: RB_total = sum of 5 non-negative terms times (2-E)
        -- Use: (a+b+c)*d ≤ a*d+b*d+c*d when d ≥ 0, and similar for sums
        -- Crude upper bound: each of the 7 terms times (2-E) ≤ s³
        -- So RB*(2-E) ≤ 7s³, giving total ≤ 8s³+7s³ = 15s³. But we need ≤ 10s³.
        -- Actually: hRB1 ≤ α³ ≤ s³, hRB2 ≤ β³ ≤ s³,
        -- hRB3 ≤ αβ² ≤ s³, hRB4 ≤ α²β ≤ s³, hRB5 ≤ α²β² ≤ s³,
        -- hRB6 ≤ s³, hRB7 ≤ s³. Total ≤ 7s³.
        -- But α³+β³ ≤ s³ (NOT 2s³)! Since α+β=s and t³ is convex with t≥0:
        -- α³+β³ ≤ (α+β)³ = s³ is WRONG. But α³+β³ ≤ s³ IS true:
        -- α³+β³ = (α+β)(α²-αβ+β²) = s(α²-αβ+β²) ≤ s·s² = s³ since α²-αβ+β² ≤ (α+β)² = s².
        -- Wait: α²-αβ+β² ≤ α²+β² ≤ s². Yes.
        -- So RB*(2-E) ≤ s³ + s³ + s³ + s³ + s³ = 5s³ (combining α³+β³≤s³).
        -- But hRB5 ≤ α²β² ≤ s³ still, and hRB6,hRB7 ≤ s³ each.
        -- WAIT: I double-counted. Let me redo:
        -- hRB1+hRB2 ≤ α³+β³ ≤ s³ (saving one factor!)
        -- hRB3 ≤ αβ² ≤ s³, hRB4 ≤ α²β ≤ s³, hRB5 ≤ α²β² ≤ s³
        -- hRB6 ≤ s³, hRB7 ≤ s³
        -- Total: s³ + s³ + s³ + s³ + s³ + s³ = 6s³. Still > 2s³.
        -- Hmm, 8s³ + 6s³ = 14s³ > 10s³. The bound is too loose!
        -- PROBLEM: The (E-1)³ ≤ 8s³ bound is too loose. For small s, (E-1) ≈ s, so (E-1)³ ≈ s³.
        -- Better bound: (E-1)³ ≤ (E-1)²·(E-1) ≤ (s+s²)²·(s+s²)
        -- For s < 0.7: E-1 < s+s² < 0.7+0.49 = 1.19, so (E-1)³ < 1.19³ ≈ 1.69
        -- But s³ for s=0.7 is 0.343, and 10·0.343 = 3.43, so we need (E-1)³ + RB*(2-E) ≤ 3.43.
        -- At s=0.7: (E-1)³ = (e^0.7-1)³ ≈ (1.0138)³ ≈ 1.042
        -- RB*(2-E) with 2-E ≈ 2-2.0138 ≈ -0.0138. Wait, E=exp(0.7)≈2.0138>2!
        -- s=0.7 > ln2≈0.693, so s < ln2 is violated. For s = 0.69: E=exp(0.69)≈1.994, 2-E≈0.006.
        -- (E-1)³ ≈ (0.994)³ ≈ 0.982. RB≈... very small times 0.006. Total ≈ 0.982.
        -- 10s³ = 10·0.329 = 3.29. So 0.982 ≤ 3.29. OK.
        -- The bound IS correct; I just need nlinarith to see it.
        -- Let me try: bound RB*(2-E) directly via RB ≤ something and then multiply by (2-E).
        -- We need: (E-1)³ + RB*(2-E) ≤ 10s³
        -- where RB = sum of non-negative terms, all bounded above by cubic terms in s
        -- After distributing: (E-1)³ + sum_i(term_i*(2-E)) ≤ 10s³
        -- Use mul_comm and add_mul to distribute, then bound each piece
        set Ea := Real.exp α - 1 - α - α ^ 2 / 2
        set Eb := Real.exp β - 1 - β - β ^ 2 / 2
        set cross := α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
          (Real.exp α - 1 - α) * (Real.exp β - 1 - β)
        set δ := E - 1 - s
        set d := (2 : ℝ) - E
        -- The RB sum is Ea + Eb + cross + s*δ + δ²/2
        -- Need: (E-1)³ + (Ea + Eb + cross + s*δ + δ²/2) * d ≤ 10s³
        -- = (E-1)³ + Ea*d + Eb*d + cross*d + s*δ*d + δ²/2*d
        -- ≤ 8s³ + α³ + β³ + (αβ² + α²β + α²β²) + s³ + s³  [using previous bounds]
        -- α³+β³ ≤ s³ [since α³+β³ = (α+β)(α²-αβ+β²) ≤ s·s² = s³]
        -- αβ² + α²β = αβ(α+β) = αβs ≤ s²/4·s = s³/4 [by AM-GM: αβ ≤ s²/4]
        -- α²β² ≤ s⁴/16 ≤ s³/16
        -- So total ≤ 8s³ + s³ + s³/4 + s³/16 + s³ + s³ = 8s³ + 2.3125s³ < 10.32s³.
        -- Hmm, that's > 10. But actually (E-1)³ ≤ 8s³ is very loose.
        -- Better: (E-1) = s+δ where δ ≤ s². And (E-1)³ = s³ + 3s²δ + 3sδ² + δ³.
        -- 3s²δ ≤ 3s²·s² = 3s⁴ ≤ 3s³. 3sδ² ≤ 3s·s⁴ = 3s⁵ ≤ 3s³. δ³ ≤ s⁶ ≤ s³.
        -- So (E-1)³ ≤ s³ + 3s³ + 3s³ + s³ = 8s³. Same bound.
        -- The issue is the constant. We need ≤ 10s³. With 8+2.3 > 10.
        -- BUT: the cross term bound was too loose. αDb*(2-E) ≤ αβ², not ≤ αβ²·1.
        -- And actually αβ(α+β) = αβs ≤ (s/2)²·s = s³/4 (by AM-GM). So αβ² + α²β ≤ s³/4+s³/4 = s³/2? NO, αβ²+α²β = αβ(α+β) = αβs.
        -- For the TOTAL, with the exact RB_i*(2-E) ≤ ... bounds:
        -- hRB1+hRB2+hRB3+hRB4+hRB5+hRB6+hRB7 ≤ α³+β³+αβ²+α²β+α²β²+s³+s³
        -- = α³+β³+αβs+α²β²+2s³
        -- ≤ s³ + s³/4·something...
        -- OK this is getting tight. Let me just try with (E-1)³ ≤ s³+3s⁴+3s⁵+s⁶
        -- and be more careful.
        -- Actually: (E-1)³ ≤ (s+s²)³ and (s+s²)³*(2-E) / ... no.
        -- Let me just try `nlinarith` with ALL the pre-computed bounds as hypotheses:
        have hcross_le : (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
            (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) * (2 - E) ≤
            α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 := by linarith [hRB3, hRB4, hRB5]
        -- αβ² + α²β = αβ(α+β) = αβs and α²β² = (αβ)². Using αβ ≤ s²/4:
        -- αβs ≤ s³/4 and (αβ)² ≤ s⁴/16 ≤ s³/16
        -- Total: ≤ s³/4 + s³/16 < s³
        have hcross_s3 : α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 ≤ s ^ 3 := by
          have hαβs : α * β ≤ s ^ 2 / 4 := by nlinarith [sq_nonneg (α - β)]
          have h1 : α * β ^ 2 + α ^ 2 * β = α * β * s := by
            rw [show α * β ^ 2 + α ^ 2 * β = α * β * (α + β) from by ring, hs_def]
          nlinarith [mul_nonneg hα_nn hβ_nn, hα2β2]
        -- Need: (E-1)³ + RB*(2-E) ≤ 10s³
        -- Distribute RB*(2-E) = Ea*(2-E) + Eb*(2-E) + cross*(2-E) + sδ*(2-E) + δ²/2*(2-E)
        -- We already have bounds on each piece.
        have hα3β3 : α ^ 3 + β ^ 3 ≤ s ^ 3 := by nlinarith [sq_nonneg (α - β)]
        -- Expand the product manually:
        have hprod_expand :
            (Real.exp α - 1 - α - α ^ 2 / 2 + (Real.exp β - 1 - β - β ^ 2 / 2) +
              (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
                (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) +
              s * (E - 1 - s) + (E - 1 - s) ^ 2 / 2) * (2 - E) =
            (Real.exp α - 1 - α - α ^ 2 / 2) * (2 - E) +
            (Real.exp β - 1 - β - β ^ 2 / 2) * (2 - E) +
            (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
              (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) * (2 - E) +
            s * (E - 1 - s) * (2 - E) +
            (E - 1 - s) ^ 2 / 2 * (2 - E) := by ring
        -- Total: 7s³ + s³ + s³ + s³ + s³/2 = 10.5s³. Still > 10!
        -- Need to tighten (E-1)³ bound further.
        -- (1+s)³ = 1+3s+3s²+s³. For s ≤ 5/6:
        -- (1+s)³ ≤ 1+3(5/6)+3(5/6)²+(5/6)³ = 1+2.5+2.0833+0.5787 = 6.16 < 7
        -- We need total ≤ 10. With exact bounds:
        -- (E-1)³ ≤ s³(1+s)³ and RB*(2-E) with exact ½.
        -- Actually: let me bound (E-1)³ more tightly. Since E-1 ≤ s+s²:
        -- (E-1)³ ≤ s³ + 3s²(E-1-s) + 3s(E-1-s)² + (E-1-s)³
        -- ≤ s³ + 3s²·s² + 3s·s⁴ + s⁶ = s³ + 3s⁴ + 3s⁵ + s⁶
        -- ≤ s³ + 3s³ + 3s³ + s³ = 8s³ (too loose with ≤ s³)
        -- BETTER: use s⁴ ≤ s³·s ≤ s³·(5/6):
        -- ≤ s³ + 3·(5/6)·s³ + 3·(5/6)²·s³ + (5/6)³·s³ = s³(1+2.5+2.08+0.58) = 6.16s³
        -- But I'd need to prove s ≤ 5/6 explicitly here.
        -- Actually, I have hs56 : s < 5/6 in scope!
        -- Let me use: (1+s)³ ≤ 1 + 3s + 3s² + s³ and bound 3s+3s²+s³ ≤ 3(5/6)+3(5/6)²+(5/6)³ = 5.16
        -- Hmm, this numeric argument is messy. Let me just use nlinarith with the hint (1+s)³ ≤ 7:
        rw [hprod_expand]
        -- Sum up: 13/2·s³ + s³ + s³ + s³ + s³/2 = (13/2+1+1+1+1/2)s³ = 10s³
        have h_sum1 : (Real.exp α - 1 - α - α ^ 2 / 2) * (2 - E) +
            (Real.exp β - 1 - β - β ^ 2 / 2) * (2 - E) ≤ s ^ 3 :=
          calc _ ≤ α ^ 3 + β ^ 3 := add_le_add hRB1 hRB2
            _ ≤ s ^ 3 := hα3β3
        have h_sum2 : (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
            (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) * (2 - E) ≤ s ^ 3 := by
          linarith [hcross_le, hcross_s3]
        -- Total: 13/2·s³ + s³ + s³ + s³ + s³/2 = 10s³
        nlinarith [pow_nonneg hs_nn 3, hRB6, hRB7, hE13_bound, h_sum1, h_sum2]

/-! ### Symmetric BCH: cubic remainder for Strang splitting -/

set_option maxHeartbeats 6400000 in
include 𝕂 in
/-- **Symmetric BCH (Strang splitting)**: The symmetric product `exp(a/2)·exp(b)·exp(a/2)`
equals `exp(a + b + R)` where `‖R‖ = O(s³)`. Equivalently,
`bch(bch(a/2, b), a/2) = a + b + O(s³)`.

The second-order commutator `[a/2, b]` from the two BCH applications cancels,
leaving only a cubic remainder. This is the key property making the Strang splitting
a second-order integrator.

The proof uses the ring identity `[z, a'] + [a', b] = [z - a' - b, a']` to show
the cancellation, where `z = bch(a', b)` and the RHS is cubic since
`z - a' - b = bch(a',b) - (a'+b) = O(s²)`. -/
theorem norm_symmetric_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) - (a + b)‖ ≤
      300 * (‖a‖ + ‖b‖) ^ 3 := by
  set a' := (2 : 𝕂)⁻¹ • a with ha'_def
  set s := ‖a‖ + ‖b‖ with hs_def
  -- ‖a'‖ ≤ ‖a‖/2
  have h_half_norm : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have ha'_le : ‖a'‖ ≤ ‖a‖ / 2 := by
    calc ‖a'‖ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [h_half_norm]; ring
  have ha'_le_a : ‖a'‖ ≤ ‖a‖ := by linarith [norm_nonneg a]
  have hs_nn : 0 ≤ s := by positivity
  have hs14 : s < 1 / 4 := hab
  have hs1 : s < 1 := by linarith
  -- s₁ = ‖a'‖ + ‖b‖ ≤ s
  set s₁ := ‖a'‖ + ‖b‖ with hs₁_def
  have hs₁_le : s₁ ≤ s := by show ‖a'‖ + ‖b‖ ≤ ‖a‖ + ‖b‖; linarith [ha'_le_a]
  have hs₁_nn : 0 ≤ s₁ := by positivity
  have ha_le_s : ‖a‖ ≤ s := le_add_of_nonneg_right (norm_nonneg b)
  have hb_le_s : ‖b‖ ≤ s := le_add_of_nonneg_left (norm_nonneg a)
  -- s₁ < ln 2 (for first BCH)
  have hln2 : (1 : ℝ) / 4 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
    have h14 := real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1:ℝ)/4 < 5/6)
    linarith
  have hs₁_ln2 : s₁ < Real.log 2 := by linarith
  -- First BCH application: z = bch(a', b)
  set z := bch (𝕂 := 𝕂) a' b with hz_def
  -- ‖z - (a' + b)‖ ≤ 3s₁²/(2-exp(s₁))  [quadratic bound]
  have hexp_s₁_lt : Real.exp s₁ < 2 := by
    calc _ < Real.exp (Real.log 2) := Real.exp_strictMono hs₁_ln2
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith
  have hδ_le : ‖z - (a' + b)‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) :=
    norm_bch_sub_add_le (𝕂 := 𝕂) a' b hs₁_ln2
  -- Tighter bound on ‖z-(a'+b)‖ using cubic remainder + commutator bound
  have hR₃'_early := norm_bch_sub_add_sub_bracket_le (𝕂 := 𝕂) a' b hs₁_ln2
  -- ‖z-(a'+b)‖ ≤ ‖½[a',b]‖ + ‖z-(a'+b)-½[a',b]‖ ≤ ‖a'‖·‖b‖ + 10s₁³/(2-exp s₁)
  -- ‖½(a'b-ba')‖ ≤ ‖a'‖·‖b‖
  have hbracket_le : ‖(2 : 𝕂)⁻¹ • (a' * b - b * a')‖ ≤ ‖a'‖ * ‖b‖ := by
    calc ‖(2 : 𝕂)⁻¹ • (a' * b - b * a')‖
        ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a' * b - b * a'‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (‖a' * b‖ + ‖b * a'‖) := by
          rw [h_half_norm]; gcongr
          calc ‖a' * b - b * a'‖ ≤ ‖a' * b‖ + ‖-(b * a')‖ := by
                rw [show a' * b - b * a' = a' * b + -(b * a') from sub_eq_add_neg _ _]
                exact norm_add_le _ _
            _ = ‖a' * b‖ + ‖b * a'‖ := by rw [norm_neg]
      _ ≤ (2 : ℝ)⁻¹ * (‖a'‖ * ‖b‖ + ‖b‖ * ‖a'‖) := by
          gcongr <;> exact norm_mul_le _ _
      _ = ‖a'‖ * ‖b‖ := by ring
  have hδ_tight : ‖z - (a' + b)‖ ≤ ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    set w := (2 : 𝕂)⁻¹ • (a' * b - b * a')
    calc ‖z - (a' + b)‖
        = ‖(z - (a' + b) - w) + w‖ := by abel_nf
      _ ≤ ‖z - (a' + b) - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 10 * s₁ ^ 3 / (2 - Real.exp s₁) + ‖a'‖ * ‖b‖ :=
          add_le_add hR₃'_early hbracket_le
      _ = ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by ring
  -- ‖z‖ bound: ‖z‖ ≤ ‖z - (a'+b)‖ + ‖a'+b‖
  have hz_le : ‖z‖ ≤ s₁ + ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    have hab_le : ‖a' + b‖ ≤ s₁ := norm_add_le a' b
    calc ‖z‖ = ‖(z - (a' + b)) + (a' + b)‖ := by congr 1; abel
      _ ≤ ‖z - (a' + b)‖ + ‖a' + b‖ := norm_add_le _ _
      _ ≤ (‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁)) + s₁ := by linarith
      _ = s₁ + ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by ring
  -- Denominator lower bounds
  have hexp_cubic := real_exp_third_order_le_cube hs_nn (by linarith : s < 5/6)
  have hexp_le : Real.exp s ≤ 1 + s + s ^ 2 := by nlinarith [sq_nonneg s]
  have hdenom_lb : (11 : ℝ) / 16 ≤ 2 - Real.exp s := by nlinarith
  have hdenom₁_lb : (11 : ℝ) / 16 ≤ 2 - Real.exp s₁ := by
    linarith [Real.exp_le_exp_of_le hs₁_le]
  -- ‖a'‖·‖b‖ ≤ s²/8 (AM-GM type bound)
  have hab_prod : ‖a'‖ * ‖b‖ ≤ s ^ 2 / 8 := by
    have h1 : ‖a'‖ ≤ s / 2 := by linarith [ha_le_s]
    have h2 : ‖b‖ ≤ s := hb_le_s
    -- ‖a'‖·‖b‖ ≤ (s/2)·s/4? No. Better: ‖a'‖ ≤ ‖a‖/2 and ‖b‖ = s-‖a‖
    -- (x/2)(s-x) ≤ s²/8 by AM-GM: max at x=s/2 giving (s/4)(s/2)=s²/8
    nlinarith [sq_nonneg (2 * ‖a'‖ - ‖b‖), norm_nonneg a', norm_nonneg b]
  -- s₂ ≤ s + ‖a'‖·‖b‖ + 10s₁³/(2-exp s₁) < 2s
  -- Key: s₂ = ‖z‖ + ‖a'‖ ≤ (s₁ + ‖a'‖) + ‖a'‖·‖b‖ + 10s₁³/(2-exp s₁)
  --       = s + ‖a'‖·‖b‖ + 10s₁³/(2-exp s₁)  [since 2‖a'‖+‖b‖ ≤ ‖a‖+‖b‖ = s]
  have hs1a'_le : s₁ + ‖a'‖ ≤ s := by
    show ‖a'‖ + ‖b‖ + ‖a'‖ ≤ ‖a‖ + ‖b‖; linarith [ha'_le]
  -- 10s₁³/(2-exp s₁) ≤ 160/11·s³
  have hcubic_div_bound : 10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 := by
    rw [div_le_iff₀ hdenom₁]
    have hs₁3 : s₁ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs₁_nn hs₁_le 3
    -- Need: 10*s₁³ ≤ 160/11*s³*(2-exp s₁)
    -- Since 160/11*(11/16) = 10 and 2-exp s₁ ≥ 11/16:
    -- 160/11*s³*(2-exp s₁) ≥ 160/11*s³*(11/16) = 10*s³ ≥ 10*s₁³
    have h1 : 160 / 11 * s ^ 3 * (2 - Real.exp s₁) ≥ 160 / 11 * s ^ 3 * (11 / 16) := by
      nlinarith [pow_nonneg hs_nn 3, hdenom₁_lb]
    have h2 : 160 / 11 * s ^ 3 * (11 / 16) = 10 * s ^ 3 := by ring
    linarith
  have hs₂_le_2s : ‖z‖ + ‖a'‖ ≤ 2 * s := by
    -- ‖z‖ + ‖a'‖ ≤ (s₁ + ‖a'‖) + ‖a'‖·‖b‖ + 10s₁³/(2-exp s₁)
    --            ≤ s + s²/8 + 160/11·s³
    -- s²/8 + 160/11·s³ ≤ s  (for s < 1/4)
    have h1 : ‖z‖ + ‖a'‖ ≤ s + ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
      have := hz_le
      have := hs1a'_le
      linarith
    -- ‖a'‖·‖b‖ + 10s₁³/(2-exp s₁) ≤ s²/8 + 160/11·s³ ≤ s
    have h2 : ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ s := by
      calc ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁)
          ≤ s ^ 2 / 8 + 160 / 11 * s ^ 3 := by linarith [hab_prod, hcubic_div_bound]
        _ ≤ s := by nlinarith [sq_nonneg s, pow_nonneg hs_nn 3,
                     sq_nonneg (1 / 4 - s)]
    linarith
  -- ‖z‖ + ‖a'‖ < ln 2  (for second BCH)
  have hz_a'_ln2 : ‖z‖ + ‖a'‖ < Real.log 2 := by
    have hln2_half : (1 : ℝ) / 2 < Real.log 2 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 2)]
      have := real_exp_third_order_le_cube (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1:ℝ)/2 < 5/6)
      linarith
    linarith
  -- Second BCH application norms
  set s₂ := ‖z‖ + ‖a'‖ with hs₂_def
  have hs₂_le_2s' : s₂ ≤ 2 * s := hs₂_le_2s
  have hs₂_nn : 0 ≤ s₂ := by positivity
  have hs₂_lt_half : s₂ < 1 / 2 := by linarith
  have hexp_s₂_lt : Real.exp s₂ < 2 := by
    calc _ < Real.exp (Real.log 2) := Real.exp_strictMono hz_a'_ln2
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom₂ : 0 < 2 - Real.exp s₂ := by linarith
  -- Denominator lower bound for s₂: exp(s₂) ≤ 1+s₂+s₂²/2+s₂³/(6(1-s₂))
  -- For s₂ < 1/2: 6(1-s₂) > 3, so s₂³/(6(1-s₂)) < s₂³/3
  -- Then 2-exp(s₂) ≥ 1-s₂-s₂²/2-s₂³/3 ≥ 1-2s-(2s)²/2-(2s)³/3 = 1-2s-2s²-8s³/3
  -- For s < 1/4: 1-2s-2s²-8s³/3 > 1/3
  have hdenom₂_lb : (1 : ℝ) / 3 ≤ 2 - Real.exp s₂ := by
    have hexp_div := real_exp_third_order_le_div hs₂_nn (by linarith : s₂ < 1)
    -- exp(s₂) ≤ 1 + s₂ + s₂²/2 + s₂³/(6(1-s₂))
    have h1ms₂ : (0 : ℝ) < 1 - s₂ := by linarith
    have h6_1ms₂ : (0 : ℝ) < 6 * (1 - s₂) := by linarith
    -- s₂³/(6(1-s₂)) ≤ s₂³/3 since 6(1-s₂) ≥ 3 (because s₂ < 1/2)
    have hcubic_div : s₂ ^ 3 / (6 * (1 - s₂)) ≤ s₂ ^ 3 / 3 :=
      div_le_div_of_nonneg_left (pow_nonneg hs₂_nn 3) (by norm_num : (0:ℝ) < 3) (by linarith)
    -- 2-exp(s₂) ≥ 1-s₂-s₂²/2-s₂³/3
    have hexp_ub : Real.exp s₂ ≤ 1 + s₂ + s₂ ^ 2 / 2 + s₂ ^ 3 / 3 := by linarith
    -- Now bound 1-s₂-s₂²/2-s₂³/3 ≥ 1/3 using s₂ < 2s < 1/2, s < 1/4
    -- i.e., 2/3 ≥ s₂ + s₂²/2 + s₂³/3 given s₂ < 1/2
    -- Since s₂ < 2s and s < 1/4:
    -- s₂ + s₂²/2 + s₂³/3 < 2s + (2s)²/2 + (2s)³/3 = 2s + 2s² + 8s³/3
    -- Need: 2s + 2s² + 8s³/3 ≤ 2/3, i.e., 6s + 6s² + 8s³ ≤ 2
    -- At s = 1/4: 3/2 + 3/8 + 1/8 = 2. So for s < 1/4 (strict): 6s+6s²+8s³ < 2.
    -- s₂ ≤ 2s, s₂² ≤ 4s², s₂³ ≤ 8s³
    have hs₂_le : s₂ ≤ 2 * s := hs₂_le_2s'
    -- s₂+s₂²/2+s₂³/3 ≤ 2s+2s²+8s³/3 ≤ 2/3
    -- 1 - s₂ - s₂²/2 - s₂³/3 ≥ 1 - 2s - 2s² - 8s³/3 ≥ 1/3
    -- Equivalently: 6s + 6s² + 8s³ ≤ 2
    -- Use s₂ ≤ 2s to bound: s₂ + s₂²/2 + s₂³/3 ≤ 2s + 2s² + 8s³/3 ≤ 2/3
    -- Then 1-s₂-s₂²/2-s₂³/3 ≥ 1-2/3 = 1/3
    -- First: 6s+6s²+8s³ ≤ 2. Write as (1-4s)(2+2s+8s²) ≥ 0... no.
    -- 2-6s-6s²-8s³ ≥ 0: Subst s = 1/4-t with t > 0:
    --   2-6(1/4-t)-6(1/4-t)²-8(1/4-t)³ = ... = 6t²(something) ≥ 0
    -- Simpler: provide the factored form directly
    -- 2-6s-6s²-8s³ = (1-4s)(2+2s+8s²)/4... let me compute:
    -- (1-4s)(2+2s) = 2+2s-8s-8s² = 2-6s-8s². Not quite.
    -- Try: 2-6s-6s²-8s³ = 2(1-4s)+2s-6s²-8s³ = 2(1-4s)+2s(1-3s-4s²)
    -- For s < 1/4: 1-3s-4s² > 1-3/4-1/4 = 0. And s ≥ 0, so 2s(1-3s-4s²) ≥ 0.
    suffices h : s₂ + s₂ ^ 2 / 2 + s₂ ^ 3 / 3 ≤ 2 / 3 by linarith
    have h_s₂_sq : s₂ ^ 2 ≤ 4 * s ^ 2 :=
      -- s₂² = s₂·s₂ ≤ (2s)·(2s) = 4s²
      calc s₂ ^ 2 = s₂ * s₂ := by ring
        _ ≤ (2 * s) * (2 * s) := mul_le_mul hs₂_le hs₂_le hs₂_nn (by linarith)
        _ = 4 * s ^ 2 := by ring
    have h_s₂_cu : s₂ ^ 3 ≤ 8 * s ^ 3 :=
      -- s₂³ = s₂·s₂² ≤ 2s·4s² = 8s³
      calc s₂ ^ 3 = s₂ * s₂ ^ 2 := by ring
        _ ≤ (2 * s) * (4 * s ^ 2) := mul_le_mul hs₂_le h_s₂_sq (sq_nonneg _) (by linarith)
        _ = 8 * s ^ 3 := by ring
    -- s₂ + s₂²/2 + s₂³/3 ≤ 2s + 2s² + 8s³/3
    have h_sum : s₂ + s₂ ^ 2 / 2 + s₂ ^ 3 / 3 ≤ 2 * s + 2 * s ^ 2 + 8 / 3 * s ^ 3 := by
      linarith
    -- 2s + 2s² + 8s³/3 ≤ 2/3 ⟺ 6s + 6s² + 8s³ ≤ 2
    -- 2(1-4s) + 2s(1-3s-4s²) ≥ 0
    have h14 : 0 ≤ 1 - 4 * s := by linarith
    -- 1-3s-4s² ≥ 0 for s < 1/4: 1-3/4-4/16 = 1-3/4-1/4 = 0
    have h_inner : 0 ≤ 1 - 3 * s - 4 * s ^ 2 := by
      -- (1-4s)(1+s) = 1+s-4s-4s² = 1-3s-4s² ≥ 0 since both factors nonneg
      have : 1 - 3 * s - 4 * s ^ 2 = (1 - 4 * s) * (1 + s) := by ring
      rw [this]; exact mul_nonneg h14 (by linarith)
    linarith [mul_nonneg hs_nn h_inner, pow_nonneg hs_nn 3]
  -- Decomposition using H1:
  set δ := z - (a' + b) with hδ_def
  -- The ring identity for commutator cancellation
  have hcomm_cancel : (z * a' - a' * z) + (a' * b - b * a') = δ * a' - a' * δ := by
    rw [hδ_def]; noncomm_ring
  -- From H1 on bch(a', b):
  have hR₃' := norm_bch_sub_add_sub_bracket_le (𝕂 := 𝕂) a' b hs₁_ln2
  -- From H1 on bch(z, a'):
  have hR₃'' := norm_bch_sub_add_sub_bracket_le (𝕂 := 𝕂) z a' hz_a'_ln2
  -- a'+a' = a
  have ha'_add : a' + a' = a := by
    rw [ha'_def, ← add_smul, show (2 : 𝕂)⁻¹ + (2 : 𝕂)⁻¹ = 1 from by
      rw [← two_mul, mul_inv_cancel₀ (two_ne_zero : (2 : 𝕂) ≠ 0)]]; exact one_smul _ _
  -- Full algebraic decomposition:
  -- bch(z, a') - (a+b) = R₃'' + ½(δa'-a'δ) + R₃'
  have hfull_decomp : bch (𝕂 := 𝕂) z a' - (a + b) =
      (bch (𝕂 := 𝕂) z a' - (z + a') - (2 : 𝕂)⁻¹ • (z * a' - a' * z)) +
      ((2 : 𝕂)⁻¹ • (δ * a' - a' * δ)) +
      (z - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a')) := by
    have hsmul_expand : (2 : 𝕂)⁻¹ • (δ * a' - a' * δ) =
        (2 : 𝕂)⁻¹ • (z * a' - a' * z) + (2 : 𝕂)⁻¹ • (a' * b - b * a') := by
      rw [← smul_add, ← hcomm_cancel]
    rw [hsmul_expand, ← ha'_add]
    abel
  -- Bound each piece
  rw [hfull_decomp]
  -- Bound ‖½(δa' - a'δ)‖ ≤ ‖δ‖ · ‖a'‖
  have hcomm_bound : ‖(2 : 𝕂)⁻¹ • (δ * a' - a' * δ)‖ ≤ ‖δ‖ * ‖a'‖ := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖δ * a' - a' * δ‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (‖δ * a'‖ + ‖a' * δ‖) := by
          rw [h_half_norm]; gcongr
          calc _ ≤ ‖δ * a'‖ + ‖-(a' * δ)‖ := by
                rw [show δ * a' - a' * δ = δ * a' + -(a' * δ) from sub_eq_add_neg _ _]
                exact norm_add_le _ _
            _ = _ := by rw [norm_neg]
      _ ≤ (2 : ℝ)⁻¹ * (‖δ‖ * ‖a'‖ + ‖a'‖ * ‖δ‖) := by
          gcongr <;> exact norm_mul_le _ _
      _ = ‖δ‖ * ‖a'‖ := by ring
  -- ‖δ‖ ≤ 3s₁²/(2-exp s₁) ≤ 3s²/(11/16), and ‖a'‖ ≤ s/2
  have ha'_le_s2 : ‖a'‖ ≤ s / 2 := by linarith [ha_le_s]
  have hδ_cubic : ‖δ‖ * ‖a'‖ ≤ 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) := by
    calc ‖δ‖ * ‖a'‖
        ≤ (3 * s₁ ^ 2 / (2 - Real.exp s₁)) * (s / 2) := by
          apply mul_le_mul hδ_le ha'_le_s2 (norm_nonneg _)
          exact div_nonneg (by positivity) (le_of_lt hdenom₁)
      _ ≤ (3 * s ^ 2 / (2 - Real.exp s₁)) * (s / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          apply div_le_div_of_nonneg_right _ (le_of_lt hdenom₁)
          nlinarith
  -- Final bound: ‖piece1‖ + ‖piece2‖ + ‖piece3‖
  calc _ ≤ ‖bch (𝕂 := 𝕂) z a' - (z + a') - (2 : 𝕂)⁻¹ • (z * a' - a' * z)‖ +
          ‖(2 : 𝕂)⁻¹ • (δ * a' - a' * δ)‖ +
          ‖z - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a')‖ := by
        calc _ ≤ ‖(bch (𝕂 := 𝕂) z a' - (z + a') - (2 : 𝕂)⁻¹ • (z * a' - a' * z)) +
                  ((2 : 𝕂)⁻¹ • (δ * a' - a' * δ))‖ +
                ‖z - (a' + b) - (2 : 𝕂)⁻¹ • (a' * b - b * a')‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ 10 * s₂ ^ 3 / (2 - Real.exp s₂) +
        (3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2)) +
        10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
        have h1 := hR₃''
        have h2 : ‖(2 : 𝕂)⁻¹ • (δ * a' - a' * δ)‖ ≤
            3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) :=
          le_trans hcomm_bound hδ_cubic
        have h3 := hR₃'
        linarith
    _ ≤ 300 * s ^ 3 := by
        -- s₂ < 2s, denom₂ ≥ 1/3, denom₁ ≥ 11/16
        -- Term 1: 10s₂³/(2-exp s₂) ≤ 10·8s³/(1/3) = 240s³
        have hs₂3 : s₂ ^ 3 ≤ 8 * s ^ 3 := by
          have : s₂ ≤ 2 * s := hs₂_le_2s'
          nlinarith [pow_le_pow_left₀ hs₂_nn this 3]
        have hterm1 : 10 * s₂ ^ 3 / (2 - Real.exp s₂) ≤ 240 * s ^ 3 := by
          rw [div_le_iff₀ hdenom₂]
          nlinarith [hdenom₂_lb, pow_nonneg hs_nn 3]
        -- Term 2: 3s²/(2-exp s₁)·(s/2) ≤ 3·(16/11)·s²·(s/2) = 24/11·s³
        have hterm2 : 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) ≤ 24 / 11 * s ^ 3 := by
          have h_div : 3 * s ^ 2 / (2 - Real.exp s₁) ≤ 3 * s ^ 2 / (11 / 16) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hdenom₁_lb
          have hs_half : 0 ≤ s / 2 := by linarith
          calc 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2)
              ≤ 3 * s ^ 2 / (11 / 16) * (s / 2) := by nlinarith
            _ = 24 / 11 * s ^ 3 := by ring
        -- Term 3: 10s₁³/(2-exp s₁) ≤ 160/11·s³
        have hterm3 : 10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 := by
          have hs₁3 : s₁ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs₁_nn hs₁_le 3
          calc 10 * s₁ ^ 3 / (2 - Real.exp s₁)
              ≤ 10 * s ^ 3 / (11 / 16) := by
                apply div_le_div₀ (by positivity) (by linarith) (by positivity) hdenom₁_lb
            _ = 160 / 11 * s ^ 3 := by ring
        -- Total: 240 + 24/11 + 160/11 = 240 + 184/11 ≈ 256.7 ≤ 300
        linarith [pow_nonneg hs_nn 3]

/-! ### Lie bracket formulation of BCH results -/

/-- The Lie bracket `⁅a, b⁆` in an associative ring equals the ring commutator `a*b - b*a`.
This is `LieRing.of_associative_ring_bracket` from Mathlib, restated here for convenience. -/
theorem lie_eq_commutator (a b : 𝔸) : ⁅a, b⁆ = a * b - b * a :=
  LieRing.of_associative_ring_bracket a b

include 𝕂 in
/-- **BCH commutator extraction (Lie bracket form)**:
`bch(a,b) = a + b + ½⁅a,b⁆ + O(s³)`. -/
theorem norm_bch_sub_add_sub_lie_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • ⁅a, b⁆‖ ≤
      10 * (‖a‖ + ‖b‖) ^ 3 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  rw [lie_eq_commutator]
  exact norm_bch_sub_add_sub_bracket_le (𝕂 := 𝕂) a b hab

include 𝕂 in
/-- **Symmetric BCH (Lie bracket form)**: The Strang splitting has cubic error,
with the `⁅a/2, b⁆` term cancelling. -/
theorem norm_symmetric_bch_sub_add_lie_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖bch (𝕂 := 𝕂) (bch (𝕂 := 𝕂) ((2 : 𝕂)⁻¹ • a) b) ((2 : 𝕂)⁻¹ • a) - (a + b)‖ ≤
      300 * (‖a‖ + ‖b‖) ^ 3 :=
  norm_symmetric_bch_sub_add_le (𝕂 := 𝕂) a b hab

include 𝕂 in
/-- The BCH quadratic bound in Lie bracket notation:
`‖bch(a,b) - (a+b)‖ ≤ 3s²/(2-eˢ)`, i.e., the leading error is `½⁅a,b⁆`. -/
theorem norm_bch_sub_add_le' (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b)‖ ≤
      3 * (‖a‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a‖ + ‖b‖)) :=
  norm_bch_sub_add_le (𝕂 := 𝕂) a b hab

/-! ### Suzuki infrastructure: Cubic coefficient and quintic remainder

For the fourth-order Suzuki formula, we need the cubic coefficient E₃ of the
symmetric BCH expansion, with the property that E₃(c·a, c·b) = c³·E₃(a,b).
The Suzuki condition 4p³+(1-4p)³=0 then kills this term. -/

/-- The degree-3 BCH term: `(1/12)([a,[a,b]] + [b,[b,a]])`.

This is the leading cubic correction in the BCH expansion:
`bch(a,b) = a + b + ½[a,b] + bch_cubic_term a b + O(s⁴)`. -/
noncomputable def bch_cubic_term (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
  (12 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a) +
  (12 : 𝕂)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Homogeneity of bch_cubic_term**: E₃(c·a, c·b) = c³·E₃(a,b).
This is the key property enabling Suzuki's cubic cancellation. -/
theorem bch_cubic_term_smul (a b : 𝔸) (c : 𝕂) :
    bch_cubic_term 𝕂 (c • a) (c • b) = c ^ 3 • bch_cubic_term 𝕂 a b := by
  -- Helper: triple product homogeneity
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
  unfold bch_cubic_term
  simp only [mul_sub, sub_mul, triple, triple', ← smul_sub, smul_comm (c ^ 3) ((12 : 𝕂)⁻¹),
    ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Norm bound for bch_cubic_term. -/
theorem norm_bch_cubic_term_le (a b : 𝔸) :
    ‖bch_cubic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 3 := by
  unfold bch_cubic_term
  set s := ‖a‖ + ‖b‖
  -- Bound ‖(12:𝕂)⁻¹‖ ≤ 1
  have h12 : ‖(12 : 𝕂)⁻¹‖ ≤ 1 := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  -- Bound each double commutator
  have hab_comm : ‖a * b - b * a‖ ≤ 2 * ‖a‖ * ‖b‖ := by
    calc ‖a * b - b * a‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖a‖ * ‖b‖ := by ring
  have hba_comm : ‖b * a - a * b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
    calc ‖b * a - a * b‖ ≤ ‖b * a‖ + ‖a * b‖ := norm_sub_le _ _
      _ ≤ ‖b‖ * ‖a‖ + ‖a‖ * ‖b‖ := by gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖a‖ * ‖b‖ := by ring
  -- First double commutator: a*[a,b] - [a,b]*a, norm ≤ 4‖a‖²‖b‖
  have h1 : ‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ := by
    calc ‖a * (a * b - b * a) - (a * b - b * a) * a‖
        ≤ ‖a * (a * b - b * a)‖ + ‖(a * b - b * a) * a‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * ‖a * b - b * a‖ + ‖a * b - b * a‖ * ‖a‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ ≤ ‖a‖ * (2 * ‖a‖ * ‖b‖) + (2 * ‖a‖ * ‖b‖) * ‖a‖ := by
          gcongr
      _ = 4 * ‖a‖ ^ 2 * ‖b‖ := by ring
  -- Second double commutator: b*[b,a] - [b,a]*b, norm ≤ 4‖a‖‖b‖²
  have h2 : ‖b * (b * a - a * b) - (b * a - a * b) * b‖ ≤ 4 * ‖a‖ * ‖b‖ ^ 2 := by
    calc ‖b * (b * a - a * b) - (b * a - a * b) * b‖
        ≤ ‖b * (b * a - a * b)‖ + ‖(b * a - a * b) * b‖ := norm_sub_le _ _
      _ ≤ ‖b‖ * ‖b * a - a * b‖ + ‖b * a - a * b‖ * ‖b‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ ≤ ‖b‖ * (2 * ‖a‖ * ‖b‖) + (2 * ‖a‖ * ‖b‖) * ‖b‖ := by
          gcongr
      _ = 4 * ‖a‖ * ‖b‖ ^ 2 := by ring
  -- Bound the smul'd terms
  have hs1 : ‖(12 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)‖
      ≤ 4 * ‖a‖ ^ 2 * ‖b‖ := by
    calc _ ≤ ‖(12 : 𝕂)⁻¹‖ * ‖a * (a * b - b * a) - (a * b - b * a) * a‖ :=
            norm_smul_le _ _
      _ ≤ 1 * (4 * ‖a‖ ^ 2 * ‖b‖) := by gcongr
      _ = 4 * ‖a‖ ^ 2 * ‖b‖ := by ring
  have hs2 : ‖(12 : 𝕂)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)‖
      ≤ 4 * ‖a‖ * ‖b‖ ^ 2 := by
    calc _ ≤ ‖(12 : 𝕂)⁻¹‖ * ‖b * (b * a - a * b) - (b * a - a * b) * b‖ :=
            norm_smul_le _ _
      _ ≤ 1 * (4 * ‖a‖ * ‖b‖ ^ 2) := by gcongr
      _ = 4 * ‖a‖ * ‖b‖ ^ 2 := by ring
  -- Combine
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  calc ‖(12 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a) +
        (12 : 𝕂)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)‖
      ≤ ‖(12 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)‖ +
        ‖(12 : 𝕂)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)‖ :=
        norm_add_le _ _
    _ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ + 4 * ‖a‖ * ‖b‖ ^ 2 := by gcongr
    _ ≤ s ^ 3 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Lipschitz-style bound for `bch_cubic_term` in its first argument**:
`‖C₃(z, y) - C₃(x, y)‖ ≤ (‖z‖+‖x‖+‖y‖)² · ‖z - x‖`.

The diff telescopes into 12 summands (counting multiplicities; 9 distinct
patterns), each of the form `[product] · (z-x) · [product]` with the products
totaling 2 letters from `{z, x, y}`. Each summand has norm ≤ M²·‖z-x‖
(M = ‖z‖+‖x‖+‖y‖), giving 12·M²·‖z-x‖ in total; the (1/12)·smul scaling
trims this to exactly M²·‖z-x‖.

Use case (T2-F7e parent discharge model): when `z = (a'+b) + W` with
`‖W‖ = O(s²)` and `‖a'+b‖, ‖y‖ = O(s)`, gives `‖C₃(z, y) - C₃(a'+b, y)‖
≤ K · s² · s² = K · s⁴`. The analog for `bch_quintic_term` and
`bch_sextic_term` (gives O(s⁶) and O(s⁷) bounds respectively) provides the
key residual estimates for the parent T2-F7e discharge. -/
theorem norm_bch_cubic_term_diff_le (z x y : 𝔸) :
    ‖bch_cubic_term 𝕂 z y - bch_cubic_term 𝕂 x y‖ ≤
      (‖z‖ + ‖x‖ + ‖y‖) ^ 2 * ‖z - x‖ := by
  -- Step 1: Telescoping algebraic identity. Each (z-x) factor is exposed.
  have htel : bch_cubic_term 𝕂 z y - bch_cubic_term 𝕂 x y =
      (12 : 𝕂)⁻¹ • (
          z * (z - x) * y + (z - x) * x * y
        - z * y * (z - x) - z * y * (z - x)
        - (z - x) * y * x - (z - x) * y * x
        + y * z * (z - x) + y * (z - x) * x
        + y * y * (z - x)
        - y * (z - x) * y - y * (z - x) * y
        + (z - x) * y * y) := by
    unfold bch_cubic_term
    simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
      smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
    match_scalars <;> ring
  rw [htel]
  -- Step 2: Setup
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  set d := ‖z - x‖ with hd_def
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  -- Helper: triple product norm bound
  have htriple : ∀ A B C : 𝔸, ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := fun A B C => by
    calc ‖A * B * C‖ ≤ ‖A * B‖ * ‖C‖ := norm_mul_le _ _
      _ ≤ ‖A‖ * ‖B‖ * ‖C‖ := by gcongr; exact norm_mul_le _ _
  -- Step 3: Each summand ≤ M²·d
  have h1 : ‖z * (z - x) * y‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖z‖ * ‖z - x‖ * ‖y‖ := htriple _ _ _
      _ ≤ M * d * M := by gcongr
      _ = M ^ 2 * d := by ring
  have h2 : ‖(z - x) * x * y‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖z - x‖ * ‖x‖ * ‖y‖ := htriple _ _ _
      _ ≤ d * M * M := by gcongr
      _ = M ^ 2 * d := by ring
  have h3 : ‖z * y * (z - x)‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖z‖ * ‖y‖ * ‖z - x‖ := htriple _ _ _
      _ ≤ M * M * d := by gcongr
      _ = M ^ 2 * d := by ring
  have h4 : ‖(z - x) * y * x‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖z - x‖ * ‖y‖ * ‖x‖ := htriple _ _ _
      _ ≤ d * M * M := by gcongr
      _ = M ^ 2 * d := by ring
  have h5 : ‖y * z * (z - x)‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖y‖ * ‖z‖ * ‖z - x‖ := htriple _ _ _
      _ ≤ M * M * d := by gcongr
      _ = M ^ 2 * d := by ring
  have h6 : ‖y * (z - x) * x‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖y‖ * ‖z - x‖ * ‖x‖ := htriple _ _ _
      _ ≤ M * d * M := by gcongr
      _ = M ^ 2 * d := by ring
  have h7 : ‖y * y * (z - x)‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖z - x‖ := htriple _ _ _
      _ ≤ M * M * d := by gcongr
      _ = M ^ 2 * d := by ring
  have h8 : ‖y * (z - x) * y‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖y‖ * ‖z - x‖ * ‖y‖ := htriple _ _ _
      _ ≤ M * d * M := by gcongr
      _ = M ^ 2 * d := by ring
  have h9 : ‖(z - x) * y * y‖ ≤ M ^ 2 * d := by
    calc _ ≤ ‖z - x‖ * ‖y‖ * ‖y‖ := htriple _ _ _
      _ ≤ d * M * M := by gcongr
      _ = M ^ 2 * d := by ring
  -- Step 4: Triangle inequality on the 12-term sum
  set S : 𝔸 :=
        z * (z - x) * y + (z - x) * x * y
      - z * y * (z - x) - z * y * (z - x)
      - (z - x) * y * x - (z - x) * y * x
      + y * z * (z - x) + y * (z - x) * x
      + y * y * (z - x)
      - y * (z - x) * y - y * (z - x) * y
      + (z - x) * y * y with hS_def
  -- Rewrite S as a sum of 12 explicit terms (each with sign), bound by 12·M²·d
  have hS_eq : S = z * (z - x) * y + (z - x) * x * y +
        -(z * y * (z - x)) + -(z * y * (z - x)) +
        -((z - x) * y * x) + -((z - x) * y * x) +
        y * z * (z - x) + y * (z - x) * x +
        y * y * (z - x) +
        -(y * (z - x) * y) + -(y * (z - x) * y) +
        (z - x) * y * y := by rw [hS_def]; abel
  have hS_le : ‖S‖ ≤ 12 * (M ^ 2 * d) := by
    rw [hS_eq]
    -- Set abbreviations for the 12 summands to keep linarith hypotheses small.
    set s1 : 𝔸 := z * (z - x) * y with hs1
    set s2 : 𝔸 := (z - x) * x * y with hs2
    set s3 : 𝔸 := -(z * y * (z - x)) with hs3
    set s4 : 𝔸 := -(z * y * (z - x)) with hs4
    set s5 : 𝔸 := -((z - x) * y * x) with hs5
    set s6 : 𝔸 := -((z - x) * y * x) with hs6
    set s7 : 𝔸 := y * z * (z - x) with hs7
    set s8 : 𝔸 := y * (z - x) * x with hs8
    set s9 : 𝔸 := y * y * (z - x) with hs9
    set s10 : 𝔸 := -(y * (z - x) * y) with hs10
    set s11 : 𝔸 := -(y * (z - x) * y) with hs11
    set s12 : 𝔸 := (z - x) * y * y with hs12
    have a11 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10 + s11) s12
    have a10 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10) s11
    have a9 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9) s10
    have a8 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8) s9
    have a7 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7) s8
    have a6 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6) s7
    have a5 := norm_add_le (s1 + s2 + s3 + s4 + s5) s6
    have a4 := norm_add_le (s1 + s2 + s3 + s4) s5
    have a3 := norm_add_le (s1 + s2 + s3) s4
    have a2 := norm_add_le (s1 + s2) s3
    have a1 := norm_add_le s1 s2
    -- Norms of the negated summands equal norms of unnegated; bound each by M²·d.
    have hs1_le : ‖s1‖ ≤ M ^ 2 * d := h1
    have hs2_le : ‖s2‖ ≤ M ^ 2 * d := h2
    have hs3_le : ‖s3‖ ≤ M ^ 2 * d := by rw [hs3, norm_neg]; exact h3
    have hs4_le : ‖s4‖ ≤ M ^ 2 * d := by rw [hs4, norm_neg]; exact h3
    have hs5_le : ‖s5‖ ≤ M ^ 2 * d := by rw [hs5, norm_neg]; exact h4
    have hs6_le : ‖s6‖ ≤ M ^ 2 * d := by rw [hs6, norm_neg]; exact h4
    have hs7_le : ‖s7‖ ≤ M ^ 2 * d := h5
    have hs8_le : ‖s8‖ ≤ M ^ 2 * d := h6
    have hs9_le : ‖s9‖ ≤ M ^ 2 * d := h7
    have hs10_le : ‖s10‖ ≤ M ^ 2 * d := by rw [hs10, norm_neg]; exact h8
    have hs11_le : ‖s11‖ ≤ M ^ 2 * d := by rw [hs11, norm_neg]; exact h8
    have hs12_le : ‖s12‖ ≤ M ^ 2 * d := h9
    linarith
  -- Step 5: Combine smul bound + sum bound
  have h12_inv : ‖(12 : 𝕂)⁻¹‖ = (12 : ℝ)⁻¹ := by
    rw [norm_inv, RCLike.norm_ofNat]
  calc ‖(12 : 𝕂)⁻¹ • S‖ ≤ ‖(12 : 𝕂)⁻¹‖ * ‖S‖ := norm_smul_le _ _
    _ = (12 : ℝ)⁻¹ * ‖S‖ := by rw [h12_inv]
    _ ≤ (12 : ℝ)⁻¹ * (12 * (M ^ 2 * d)) := by
        apply mul_le_mul_of_nonneg_left hS_le (by norm_num)
    _ = M ^ 2 * d := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **C₃ LQ decomposition** (T2-F7e Phase E.2 helper):
    `C₃(x+W, y) − C₃(x, y) = (1/12) · L_C3(x, W, y) + (1/12) · Q_C3(W, y)`
where `L_C3` is linear in W and `Q_C3` is quadratic in W.

This is a more granular form of the telescoping identity in
`norm_bch_cubic_term_diff_le`: separating linear-in-W from quadratic-in-W
contributions of the difference. Used to extract the deg-5 (linear-in-W
when W=O(s²)) and deg-6+ (quadratic) parts of the cubic term difference
for the parent T2-F7e discharge.

The L_C3 shape matches the cubic template's `L_W` (in Basic.lean's
`norm_symmetric_bch_cubic_sub_poly_le`) with `x ≡ a'+b`, `y ≡ a'`,
giving `L_W = L_C3(a'+b, W, a')`. -/
theorem bch_cubic_term_LQ_decomp (x W y : 𝔸) :
    bch_cubic_term 𝕂 (x + W) y - bch_cubic_term 𝕂 x y =
      (12 : 𝕂)⁻¹ • (
        -- Linear in W (9 distinct terms; "- X - X" written as -2·X equivalent).
        x * W * y + W * x * y - x * y * W - x * y * W - W * y * x - W * y * x +
        y * x * W + y * W * x + y * y * W - y * W * y - y * W * y + W * y * y) +
      (12 : 𝕂)⁻¹ • (
        -- Quadratic in W (3 distinct terms).
        W * W * y - W * y * W - W * y * W + y * W * W) := by
  unfold bch_cubic_term
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-- The degree-4 BCH term: `-(1/24)⁅b,⁅a,⁅a,b⁆⁆⁆`.

This is the quartic correction in the BCH expansion:
`bch(a,b) = a + b + ½[a,b] + bch_cubic_term a b + bch_quartic_term a b + O(s⁵)`.

The 4th BCH coefficient Z₄ = -(1/24)[b,[a,[a,b]]], verified by direct computation:
the degree-4 part of y-y²/2+y³/3-y⁴/4 (where y=exp(a)exp(b)-1) equals this expression.

Note: in the free Lie algebra, [b,[a,[a,b]]]+[a,[b,[b,a]]] = 0 (identity in any associative
algebra), so Z₄ = -(1/24)[b,[a,[a,b]]] = (1/24)[a,[b,[b,a]]]. -/
noncomputable def bch_quartic_term (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
  -((24 : 𝕂)⁻¹ • (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
    (a * (a * b - b * a) - (a * b - b * a) * a) * b))

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Homogeneity of bch_quartic_term**: C₄(c·a, c·b) = c⁴·C₄(a,b).
This is the key property for extracting the quartic term from the BCH expansion. -/
theorem bch_quartic_term_smul (a b : 𝔸) (c : 𝕂) :
    bch_quartic_term 𝕂 (c • a) (c • b) = c ^ 4 • bch_quartic_term 𝕂 a b := by
  unfold bch_quartic_term
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, mul_sub, sub_mul, smul_smul,
    smul_neg, neg_inj]
  congr 1; congr 1
  all_goals (try (congr 1; ring)); try ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Norm bound for bch_quartic_term: `‖C₄(a,b)‖ ≤ s⁴`.
The new definition C₄ = -(1/24)[b,[a,[a,b]]] is a single triple commutator,
so the bound is ‖(1/24)·2β·4α²β‖ = (1/3)α²β² ≤ s⁴. -/
theorem norm_bch_quartic_term_le (a b : 𝔸) :
    ‖bch_quartic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 4 := by
  set s := ‖a‖ + ‖b‖
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have h24 : ‖(24 : 𝕂)⁻¹‖ ≤ 1 := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  -- Double commutator bound: ‖[a,[a,b]]‖ ≤ 4α²β
  have hab_comm : ‖a * b - b * a‖ ≤ 2 * ‖a‖ * ‖b‖ := by
    calc _ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := by gcongr <;> exact norm_mul_le _ _
      _ = _ := by ring
  have hA_dc : ‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ := by
    calc _ ≤ ‖a * (a * b - b * a)‖ + ‖(a * b - b * a) * a‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * (2 * ‖a‖ * ‖b‖) + (2 * ‖a‖ * ‖b‖) * ‖a‖ := by
          gcongr
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hab_comm ha)
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hab_comm ha)
      _ = _ := by ring
  -- Triple commutator: ‖[b,[a,[a,b]]]‖ = ‖b·DC_a-DC_a·b‖ ≤ 8α²β²
  show ‖bch_quartic_term 𝕂 a b‖ ≤ s ^ 4
  unfold bch_quartic_term
  set DC_a := a * (a * b - b * a) - (a * b - b * a) * a
  have hB_tc : ‖b * DC_a - DC_a * b‖ ≤ 8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    calc _ ≤ ‖b * DC_a‖ + ‖DC_a * b‖ := norm_sub_le _ _
      _ ≤ ‖b‖ * ‖DC_a‖ + ‖DC_a‖ * ‖b‖ := by gcongr <;> exact norm_mul_le _ _
      _ ≤ ‖b‖ * (4 * ‖a‖ ^ 2 * ‖b‖) + (4 * ‖a‖ ^ 2 * ‖b‖) * ‖b‖ := by gcongr
      _ = _ := by ring
  calc ‖-((24 : 𝕂)⁻¹ • (b * DC_a - DC_a * b))‖
      = ‖(24 : 𝕂)⁻¹ • (b * DC_a - DC_a * b)‖ := norm_neg _
    _ ≤ ‖(24 : 𝕂)⁻¹‖ * ‖b * DC_a - DC_a * b‖ := norm_smul_le _ _
    _ ≤ 1 * (8 * ‖a‖ ^ 2 * ‖b‖ ^ 2) := by gcongr
    _ = 8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := one_mul _
    _ ≤ s ^ 4 := by
        -- 8α²β² ≤ (α+β)⁴ since αβ ≤ (α+β)²/4 → α²β² ≤ s⁴/16 → 8α²β² ≤ s⁴/2
        have hab : ‖a‖ * ‖b‖ ≤ s ^ 2 / 4 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
        have hab2 : ‖a‖ ^ 2 * ‖b‖ ^ 2 ≤ s ^ 4 / 16 := by
          have h1 : (‖a‖ * ‖b‖) ^ 2 ≤ (s ^ 2 / 4) ^ 2 :=
            sq_le_sq' (by nlinarith) hab
          nlinarith [h1]
        nlinarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **C₄ LQ decomposition** (T2-F7e Phase E.2 step 3 helper):
    `C₄(x+W, y) − C₄(x, y) = (1/24) · L_C4(x, W, y) + (1/24) · Q_C4(W, y)`
where L_C4 is linear in W and Q_C4 is quadratic in W.

Analog of `bch_cubic_term_LQ_decomp` for the deg-4 BCH term. Used to
extract the deg-4 (linear-in-W with W=V₂) and deg-6 (linear-in-W with
W=V₃ + quadratic-in-W with W=V₂) leading parts of T₆ for the Phase E.2
discharge of R_T6_sept.

Recall `C₄(z, y) = (1/24)·(zzyy - 2·zyzy + 2·yzyz - yyzz)`. After the
substitution `z := x + W` and subtracting `C₄(x, y)`, the result has
linear-in-W (8 sub-terms) and quadratic-in-W (4 sub-terms) pieces. -/
theorem bch_quartic_term_LQ_decomp (x W y : 𝔸) :
    bch_quartic_term 𝕂 (x + W) y - bch_quartic_term 𝕂 x y =
      (24 : 𝕂)⁻¹ • (
        -- Linear in W (12 sub-terms with multiplicities; coefficients ±1, ±2).
        x * W * y * y + W * x * y * y - x * y * W * y - x * y * W * y -
        W * y * x * y - W * y * x * y +
        y * W * y * x + y * W * y * x + y * x * y * W + y * x * y * W -
        y * y * x * W - y * y * W * x) +
      (24 : 𝕂)⁻¹ • (
        -- Quadratic in W (6 sub-terms with multiplicities).
        W * W * y * y - W * y * W * y - W * y * W * y +
        y * W * y * W + y * W * y * W - y * y * W * W) := by
  unfold bch_quartic_term
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, neg_neg, neg_mul, mul_neg,
    sub_neg_eq_add, ← mul_assoc]
  match_scalars <;> ring

/-! ### Fifth-order BCH term (Z₅) -/

/-- **Sign-1 group** of `bch_quintic_term`: the four 5-letter words with
  absolute coefficient 1 (the "almost-pure" pattern AAAAB / ABBBB / BAAAA /
  BBBBA). Each appears with coefficient -1/720 in Z₅.

  Factored separately to keep the proofs of `bch_quintic_term_smul` and
  `norm_bch_quintic_term_le` tractable. -/
noncomputable def bch_quintic_group_1 {𝔸 : Type*} [NormedRing 𝔸]
    (a b : 𝔸) : 𝔸 :=
  a * a * a * a * b + a * b * b * b * b + b * a * a * a * a + b * b * b * b * a

/-- **Sign-4 group** of `bch_quintic_term`: the ten 5-letter words with
  absolute coefficient 4. Each appears with coefficient +4/720 = 1/180. -/
noncomputable def bch_quintic_group_4 {𝔸 : Type*} [NormedRing 𝔸]
    (a b : 𝔸) : 𝔸 :=
  a * a * a * b * a + a * a * a * b * b + a * a * b * b * b +
  a * b * a * a * a + a * b * b * b * a + b * a * a * a * b +
  b * a * b * b * b + b * b * a * a * a + b * b * b * a * a +
  b * b * b * a * b

/-- **Sign-6 group** of `bch_quintic_term`: the fourteen 5-letter words
  with absolute coefficient 6. Each appears with coefficient -6/720 = -1/120. -/
noncomputable def bch_quintic_group_6 {𝔸 : Type*} [NormedRing 𝔸]
    (a b : 𝔸) : 𝔸 :=
  a * a * b * a * a + a * a * b * a * b + a * a * b * b * a +
  a * b * a * a * b + a * b * a * b * b + a * b * b * a * a +
  a * b * b * a * b + b * a * a * b * a + b * a * a * b * b +
  b * a * b * a * a + b * a * b * b * a + b * b * a * a * b +
  b * b * a * b * a + b * b * a * b * b

/-- **Sign-24 group** of `bch_quintic_term`: the two 5-letter palindromic
  words with absolute coefficient 24. Each appears with coefficient
  +24/720 = 1/30. -/
noncomputable def bch_quintic_group_24 {𝔸 : Type*} [NormedRing 𝔸]
    (a b : 𝔸) : 𝔸 :=
  a * b * a * b * a + b * a * b * a * b

/-- The degree-5 BCH term: τ⁵ coefficient of `bch(a,b) = log(exp(a)·exp(b))`.

Extracted symbolically by `Lean-Trotter/scripts/extract_bch_z5.py` from the
truncated NC-polynomial expansion of `log(1 + (exp(a)·exp(b) - 1))` to
degree 5. Has 30 non-zero 5-letter words on `{a, b}`; the only words that
do NOT appear are the pure `aaaaa` and `bbbbb` (since `bch(a, 0) = a` and
`bch(0, b) = b` have no quintic correction). LCM of denominators is 720.

Decomposed into four `bch_quintic_group_n` pieces grouped by absolute
coefficient (n ∈ {1, 4, 6, 24}) for clean smul and norm bookkeeping.

This is the next term in the expansion:
`bch(a,b) = a + b + ½[a,b] + bch_cubic_term + bch_quartic_term +
  bch_quintic_term + O(s⁶)`. -/
noncomputable def bch_quintic_term (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
  (720 : 𝕂)⁻¹ • (
    -bch_quintic_group_1 a b
    + (4 : 𝕂) • bch_quintic_group_4 a b
    - (6 : 𝕂) • bch_quintic_group_6 a b
    + (24 : 𝕂) • bch_quintic_group_24 a b
  )

/-! #### Homogeneity of bch_quintic_term -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem bch_quintic_group_1_smul (a b : 𝔸) (c : 𝕂) :
    bch_quintic_group_1 (c • a) (c • b) = c ^ 5 • bch_quintic_group_1 a b := by
  unfold bch_quintic_group_1
  have quint : ∀ x₁ x₂ x₃ x₄ x₅ : 𝔸,
      (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) =
        c ^ 5 • (x₁ * x₂ * x₃ * x₄ * x₅) := by
    intros; simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; congr 1; ring
  simp only [quint, ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem bch_quintic_group_4_smul (a b : 𝔸) (c : 𝕂) :
    bch_quintic_group_4 (c • a) (c • b) = c ^ 5 • bch_quintic_group_4 a b := by
  unfold bch_quintic_group_4
  have quint : ∀ x₁ x₂ x₃ x₄ x₅ : 𝔸,
      (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) =
        c ^ 5 • (x₁ * x₂ * x₃ * x₄ * x₅) := by
    intros; simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; congr 1; ring
  simp only [quint, ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem bch_quintic_group_6_smul (a b : 𝔸) (c : 𝕂) :
    bch_quintic_group_6 (c • a) (c • b) = c ^ 5 • bch_quintic_group_6 a b := by
  unfold bch_quintic_group_6
  have quint : ∀ x₁ x₂ x₃ x₄ x₅ : 𝔸,
      (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) =
        c ^ 5 • (x₁ * x₂ * x₃ * x₄ * x₅) := by
    intros; simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; congr 1; ring
  simp only [quint, ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem bch_quintic_group_24_smul (a b : 𝔸) (c : 𝕂) :
    bch_quintic_group_24 (c • a) (c • b) = c ^ 5 • bch_quintic_group_24 a b := by
  unfold bch_quintic_group_24
  have quint : ∀ x₁ x₂ x₃ x₄ x₅ : 𝔸,
      (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) =
        c ^ 5 • (x₁ * x₂ * x₃ * x₄ * x₅) := by
    intros; simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; congr 1; ring
  simp only [quint, ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Homogeneity of bch_quintic_term**: Z₅(c·a, c·b) = c⁵·Z₅(a,b). -/
theorem bch_quintic_term_smul (a b : 𝔸) (c : 𝕂) :
    bch_quintic_term 𝕂 (c • a) (c • b) = c ^ 5 • bch_quintic_term 𝕂 a b := by
  unfold bch_quintic_term
  rw [bch_quintic_group_1_smul, bch_quintic_group_4_smul,
      bch_quintic_group_6_smul, bch_quintic_group_24_smul]
  -- Pull c^5 out of each smul'd group; then out of the (720)⁻¹ smul
  rw [smul_comm ((4 : 𝕂)) (c ^ 5), smul_comm ((6 : 𝕂)) (c ^ 5),
      smul_comm ((24 : 𝕂)) (c ^ 5),
      ← smul_neg, ← smul_add, ← smul_sub, ← smul_add,
      smul_comm ((720 : 𝕂)⁻¹) (c ^ 5)]

/-! #### Norm bounds for the four groups + the headline bound -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Helper: any 5-letter word on `{a, b}` has norm ≤ s⁵ where s = ‖a‖+‖b‖. -/
private lemma norm_word5_le {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸)
    (x₁ x₂ x₃ x₄ x₅ : 𝔸)
    (h₁ : x₁ = a ∨ x₁ = b) (h₂ : x₂ = a ∨ x₂ = b) (h₃ : x₃ = a ∨ x₃ = b)
    (h₄ : x₄ = a ∨ x₄ = b) (h₅ : x₅ = a ∨ x₅ = b) :
    ‖x₁ * x₂ * x₃ * x₄ * x₅‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  set s := ‖a‖ + ‖b‖
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hxs : ∀ x : 𝔸, x = a ∨ x = b → ‖x‖ ≤ s := by
    intro x hx
    cases hx with
    | inl h => rw [h]; linarith
    | inr h => rw [h]; linarith
  calc ‖x₁ * x₂ * x₃ * x₄ * x₅‖
      ≤ ‖x₁ * x₂ * x₃ * x₄‖ * ‖x₅‖ := norm_mul_le _ _
    _ ≤ ‖x₁ * x₂ * x₃‖ * ‖x₄‖ * ‖x₅‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖x₁ * x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖x₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ s * s * s * s * s := by
        gcongr <;> [exact hxs _ h₁; exact hxs _ h₂; exact hxs _ h₃;
                    exact hxs _ h₄; exact hxs _ h₅]
    _ = s ^ 5 := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem norm_bch_quintic_group_1_le (a b : 𝔸) :
    ‖bch_quintic_group_1 a b‖ ≤ 4 * (‖a‖ + ‖b‖) ^ 5 := by
  unfold bch_quintic_group_1
  set s := ‖a‖ + ‖b‖
  have m1 := norm_word5_le a b a a a a b
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have m2 := norm_word5_le a b a b b b b
    (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have m3 := norm_word5_le a b b a a a a
    (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have m4 := norm_word5_le a b b b b b a
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have step1 := norm_add_le (a*a*a*a*b + a*b*b*b*b + b*a*a*a*a) (b*b*b*b*a)
  have step2 := norm_add_le (a*a*a*a*b + a*b*b*b*b) (b*a*a*a*a)
  have step3 := norm_add_le (a*a*a*a*b) (a*b*b*b*b)
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem norm_bch_quintic_group_4_le (a b : 𝔸) :
    ‖bch_quintic_group_4 a b‖ ≤ 10 * (‖a‖ + ‖b‖) ^ 5 := by
  unfold bch_quintic_group_4
  set s := ‖a‖ + ‖b‖
  have m1 := norm_word5_le a b a a a b a
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have m2 := norm_word5_le a b a a a b b
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have m3 := norm_word5_le a b a a b b b
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have m4 := norm_word5_le a b a b a a a
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have m5 := norm_word5_le a b a b b b a
    (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have m6 := norm_word5_le a b b a a a b
    (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have m7 := norm_word5_le a b b a b b b
    (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have m8 := norm_word5_le a b b b a a a
    (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have m9 := norm_word5_le a b b b b a a
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have m10 := norm_word5_le a b b b b a b
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have step1 := norm_add_le (a*a*a*b*a + a*a*a*b*b + a*a*b*b*b + a*b*a*a*a +
      a*b*b*b*a + b*a*a*a*b + b*a*b*b*b + b*b*a*a*a + b*b*b*a*a) (b*b*b*a*b)
  have step2 := norm_add_le (a*a*a*b*a + a*a*a*b*b + a*a*b*b*b + a*b*a*a*a +
      a*b*b*b*a + b*a*a*a*b + b*a*b*b*b + b*b*a*a*a) (b*b*b*a*a)
  have step3 := norm_add_le (a*a*a*b*a + a*a*a*b*b + a*a*b*b*b + a*b*a*a*a +
      a*b*b*b*a + b*a*a*a*b + b*a*b*b*b) (b*b*a*a*a)
  have step4 := norm_add_le (a*a*a*b*a + a*a*a*b*b + a*a*b*b*b + a*b*a*a*a +
      a*b*b*b*a + b*a*a*a*b) (b*a*b*b*b)
  have step5 := norm_add_le (a*a*a*b*a + a*a*a*b*b + a*a*b*b*b + a*b*a*a*a +
      a*b*b*b*a) (b*a*a*a*b)
  have step6 := norm_add_le (a*a*a*b*a + a*a*a*b*b + a*a*b*b*b + a*b*a*a*a) (a*b*b*b*a)
  have step7 := norm_add_le (a*a*a*b*a + a*a*a*b*b + a*a*b*b*b) (a*b*a*a*a)
  have step8 := norm_add_le (a*a*a*b*a + a*a*a*b*b) (a*a*b*b*b)
  have step9 := norm_add_le (a*a*a*b*a) (a*a*a*b*b)
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem norm_bch_quintic_group_6_le (a b : 𝔸) :
    ‖bch_quintic_group_6 a b‖ ≤ 14 * (‖a‖ + ‖b‖) ^ 5 := by
  unfold bch_quintic_group_6
  set s := ‖a‖ + ‖b‖
  have m1 := norm_word5_le a b a a b a a
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have m2 := norm_word5_le a b a a b a b
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have m3 := norm_word5_le a b a a b b a
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have m4 := norm_word5_le a b a b a a b
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have m5 := norm_word5_le a b a b a b b
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have m6 := norm_word5_le a b a b b a a
    (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have m7 := norm_word5_le a b a b b a b
    (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have m8 := norm_word5_le a b b a a b a
    (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have m9 := norm_word5_le a b b a a b b
    (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have m10 := norm_word5_le a b b a b a a
    (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have m11 := norm_word5_le a b b a b b a
    (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have m12 := norm_word5_le a b b b a a b
    (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have m13 := norm_word5_le a b b b a b a
    (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have m14 := norm_word5_le a b b b a b b
    (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have step1 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a + a*b*b*a*b + b*a*a*b*a + b*a*a*b*b + b*a*b*a*a +
      b*a*b*b*a + b*b*a*a*b + b*b*a*b*a) (b*b*a*b*b)
  have step2 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a + a*b*b*a*b + b*a*a*b*a + b*a*a*b*b + b*a*b*a*a +
      b*a*b*b*a + b*b*a*a*b) (b*b*a*b*a)
  have step3 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a + a*b*b*a*b + b*a*a*b*a + b*a*a*b*b + b*a*b*a*a +
      b*a*b*b*a) (b*b*a*a*b)
  have step4 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a + a*b*b*a*b + b*a*a*b*a + b*a*a*b*b + b*a*b*a*a)
      (b*a*b*b*a)
  have step5 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a + a*b*b*a*b + b*a*a*b*a + b*a*a*b*b) (b*a*b*a*a)
  have step6 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a + a*b*b*a*b + b*a*a*b*a) (b*a*a*b*b)
  have step7 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a + a*b*b*a*b) (b*a*a*b*a)
  have step8 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b + a*b*b*a*a) (a*b*b*a*b)
  have step9 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b +
      a*b*a*b*b) (a*b*b*a*a)
  have step10 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a + a*b*a*a*b)
      (a*b*a*b*b)
  have step11 := norm_add_le (a*a*b*a*a + a*a*b*a*b + a*a*b*b*a) (a*b*a*a*b)
  have step12 := norm_add_le (a*a*b*a*a + a*a*b*a*b) (a*a*b*b*a)
  have step13 := norm_add_le (a*a*b*a*a) (a*a*b*a*b)
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem norm_bch_quintic_group_24_le (a b : 𝔸) :
    ‖bch_quintic_group_24 a b‖ ≤ 2 * (‖a‖ + ‖b‖) ^ 5 := by
  unfold bch_quintic_group_24
  set s := ‖a‖ + ‖b‖
  have m1 := norm_word5_le a b a b a b a
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have m2 := norm_word5_le a b b a b a b
    (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have step1 := norm_add_le (a*b*a*b*a) (b*a*b*a*b)
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Norm bound for `bch_quintic_term`: `‖Z₅(a,b)‖ ≤ s⁵` where `s = ‖a‖+‖b‖`.

  Sum of |coefficients|: 4·1 + 10·4 + 14·6 + 2·24 = 176. Multiplied by
  `‖(720)⁻¹‖ = 1/720` gives `176/720 ≈ 0.244`, well below 1. -/
theorem norm_bch_quintic_term_le (a b : 𝔸) :
    ‖bch_quintic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  unfold bch_quintic_term
  set s := ‖a‖ + ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  have hs5_nn : 0 ≤ s ^ 5 := pow_nonneg hs_nn 5
  -- Per-group bounds
  have hg1 := norm_bch_quintic_group_1_le a b
  have hg4 := norm_bch_quintic_group_4_le a b
  have hg6 := norm_bch_quintic_group_6_le a b
  have hg24 := norm_bch_quintic_group_24_le a b
  -- Negation preserves norm
  have hng1 : ‖-bch_quintic_group_1 a b‖ ≤ 4 * s ^ 5 := by rw [norm_neg]; exact hg1
  -- Bounds on (n : 𝕂) • group, using ‖(n : 𝕂)‖ = n in RCLike
  have h4n : ‖((4 : 𝕂)) • bch_quintic_group_4 a b‖ ≤ 40 * s ^ 5 := by
    calc ‖((4 : 𝕂)) • bch_quintic_group_4 a b‖
        ≤ ‖((4 : 𝕂))‖ * ‖bch_quintic_group_4 a b‖ := norm_smul_le _ _
      _ = 4 * ‖bch_quintic_group_4 a b‖ := by rw [RCLike.norm_ofNat]
      _ ≤ 4 * (10 * s ^ 5) := by gcongr
      _ = 40 * s ^ 5 := by ring
  have h6n : ‖((6 : 𝕂)) • bch_quintic_group_6 a b‖ ≤ 84 * s ^ 5 := by
    calc ‖((6 : 𝕂)) • bch_quintic_group_6 a b‖
        ≤ ‖((6 : 𝕂))‖ * ‖bch_quintic_group_6 a b‖ := norm_smul_le _ _
      _ = 6 * ‖bch_quintic_group_6 a b‖ := by rw [RCLike.norm_ofNat]
      _ ≤ 6 * (14 * s ^ 5) := by gcongr
      _ = 84 * s ^ 5 := by ring
  have h24n : ‖((24 : 𝕂)) • bch_quintic_group_24 a b‖ ≤ 48 * s ^ 5 := by
    calc ‖((24 : 𝕂)) • bch_quintic_group_24 a b‖
        ≤ ‖((24 : 𝕂))‖ * ‖bch_quintic_group_24 a b‖ := norm_smul_le _ _
      _ = 24 * ‖bch_quintic_group_24 a b‖ := by rw [RCLike.norm_ofNat]
      _ ≤ 24 * (2 * s ^ 5) := by gcongr
      _ = 48 * s ^ 5 := by ring
  -- Inner sum: 4 + 40 + 84 + 48 = 176
  have h_inner : ‖-bch_quintic_group_1 a b + (4 : 𝕂) • bch_quintic_group_4 a b -
      (6 : 𝕂) • bch_quintic_group_6 a b + (24 : 𝕂) • bch_quintic_group_24 a b‖ ≤
      176 * s ^ 5 := by
    have step1 := norm_add_le (-bch_quintic_group_1 a b + (4 : 𝕂) • bch_quintic_group_4 a b -
      (6 : 𝕂) • bch_quintic_group_6 a b) ((24 : 𝕂) • bch_quintic_group_24 a b)
    have step2 := norm_sub_le (-bch_quintic_group_1 a b + (4 : 𝕂) • bch_quintic_group_4 a b)
      ((6 : 𝕂) • bch_quintic_group_6 a b)
    have step3 := norm_add_le (-bch_quintic_group_1 a b)
      ((4 : 𝕂) • bch_quintic_group_4 a b)
    linarith
  -- Outer (720)⁻¹ smul: ‖(720)⁻¹‖ = 1/720 in RCLike
  have h720 : ‖((720 : 𝕂)⁻¹)‖ = 1 / 720 := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  calc ‖((720 : 𝕂)⁻¹) • (-bch_quintic_group_1 a b + (4 : 𝕂) • bch_quintic_group_4 a b -
      (6 : 𝕂) • bch_quintic_group_6 a b + (24 : 𝕂) • bch_quintic_group_24 a b)‖
      ≤ ‖((720 : 𝕂)⁻¹)‖ * ‖-bch_quintic_group_1 a b + (4 : 𝕂) • bch_quintic_group_4 a b -
        (6 : 𝕂) • bch_quintic_group_6 a b + (24 : 𝕂) • bch_quintic_group_24 a b‖ :=
        norm_smul_le _ _
    _ ≤ (1 / 720) * (176 * s ^ 5) := by rw [h720]; gcongr
    _ ≤ s ^ 5 := by nlinarith [hs5_nn]

/-! #### Lipschitz-style bounds for `bch_quintic_group_1` (Phase A.1 of T2-F7e)

The Lipschitz-style bound `‖C₅(z, y) − C₅(x, y)‖ ≤ M⁴ · ‖z − x‖` (where
`M = ‖z‖+‖x‖+‖y‖`) is needed for the parent T2-F7e discharge. This file
contains the per-group precursors; the full `bch_quintic_term` bound combines
all 4 groups via triangle inequality with the appropriate `(720)⁻¹`-scalar
factors.

Each group's diff telescopes per-word: a word `w(z, y)` with k z-positions has
diff `w(z, y) − w(x, y) = Σⱼ [product]·(z−x)·[product]`, with k summands.
Each summand has 4 letters from `{x, z, y}` (each ≤ M) and one (z−x) factor
(of norm `‖z − x‖`), giving a per-summand bound of `M⁴ · ‖z − x‖`. -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Lipschitz bound for `bch_quintic_group_1` in its first argument**:
`‖group_1(z, y) − group_1(x, y)‖ ≤ 10 · (‖z‖+‖x‖+‖y‖)⁴ · ‖z − x‖`.

`bch_quintic_group_1 = a·a·a·a·b + a·b·b·b·b + b·a·a·a·a + b·b·b·b·a` has 4
words with a-position counts `{4, 1, 4, 1}`, summing to 10 telescoping
summands. Each summand has the form `[product]·(z−x)·[product]` with the
products totaling 4 letters from `{x, z, y}`; bounded by M⁴·‖z−x‖. -/
theorem norm_bch_quintic_group_1_diff_le (z x y : 𝔸) :
    ‖bch_quintic_group_1 z y - bch_quintic_group_1 x y‖ ≤
      10 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  -- Step 1: Telescoping algebraic identity
  have htel : bch_quintic_group_1 z y - bch_quintic_group_1 x y =
      (z - x) * z * z * z * y + x * (z - x) * z * z * y +
      x * x * (z - x) * z * y + x * x * x * (z - x) * y +
      (z - x) * y * y * y * y +
      y * (z - x) * z * z * z + y * x * (z - x) * z * z +
      y * x * x * (z - x) * z + y * x * x * x * (z - x) +
      y * y * y * y * (z - x) := by
    unfold bch_quintic_group_1
    noncomm_ring
  rw [htel]
  -- Step 2: Setup
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  set d := ‖z - x‖ with hd_def
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  -- Step 3: 5-product norm helper
  have h5prod : ∀ A B C D E : 𝔸,
      ‖A * B * C * D * E‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ :=
    fun A B C D E => by
      calc ‖A * B * C * D * E‖
          ≤ ‖A * B * C * D‖ * ‖E‖ := norm_mul_le _ _
        _ ≤ ‖A * B * C‖ * ‖D‖ * ‖E‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖A * B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by gcongr; exact norm_mul_le _ _
  -- Step 4: Each summand ≤ M⁴·d
  have h1 : ‖(z - x) * z * z * z * y‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖z - x‖ * ‖z‖ * ‖z‖ * ‖z‖ * ‖y‖ := h5prod _ _ _ _ _
      _ ≤ d * M * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h2 : ‖x * (z - x) * z * z * y‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖x‖ * ‖z - x‖ * ‖z‖ * ‖z‖ * ‖y‖ := h5prod _ _ _ _ _
      _ ≤ M * d * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h3 : ‖x * x * (z - x) * z * y‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖x‖ * ‖x‖ * ‖z - x‖ * ‖z‖ * ‖y‖ := h5prod _ _ _ _ _
      _ ≤ M * M * d * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h4 : ‖x * x * x * (z - x) * y‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖x‖ * ‖x‖ * ‖x‖ * ‖z - x‖ * ‖y‖ := h5prod _ _ _ _ _
      _ ≤ M * M * M * d * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h5 : ‖(z - x) * y * y * y * y‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖z - x‖ * ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ := h5prod _ _ _ _ _
      _ ≤ d * M * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h6 : ‖y * (z - x) * z * z * z‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖y‖ * ‖z - x‖ * ‖z‖ * ‖z‖ * ‖z‖ := h5prod _ _ _ _ _
      _ ≤ M * d * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h7 : ‖y * x * (z - x) * z * z‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖y‖ * ‖x‖ * ‖z - x‖ * ‖z‖ * ‖z‖ := h5prod _ _ _ _ _
      _ ≤ M * M * d * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h8 : ‖y * x * x * (z - x) * z‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖y‖ * ‖x‖ * ‖x‖ * ‖z - x‖ * ‖z‖ := h5prod _ _ _ _ _
      _ ≤ M * M * M * d * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h9 : ‖y * x * x * x * (z - x)‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖y‖ * ‖x‖ * ‖x‖ * ‖x‖ * ‖z - x‖ := h5prod _ _ _ _ _
      _ ≤ M * M * M * M * d := by gcongr
      _ = M ^ 4 * d := by ring
  have h10 : ‖y * y * y * y * (z - x)‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ * ‖z - x‖ := h5prod _ _ _ _ _
      _ ≤ M * M * M * M * d := by gcongr
      _ = M ^ 4 * d := by ring
  -- Step 5: 9-step triangle inequality on the 10-term sum (use `set` for clarity)
  set s1 : 𝔸 := (z - x) * z * z * z * y with hs1
  set s2 : 𝔸 := x * (z - x) * z * z * y with hs2
  set s3 : 𝔸 := x * x * (z - x) * z * y with hs3
  set s4 : 𝔸 := x * x * x * (z - x) * y with hs4
  set s5 : 𝔸 := (z - x) * y * y * y * y with hs5
  set s6 : 𝔸 := y * (z - x) * z * z * z with hs6
  set s7 : 𝔸 := y * x * (z - x) * z * z with hs7
  set s8 : 𝔸 := y * x * x * (z - x) * z with hs8
  set s9 : 𝔸 := y * x * x * x * (z - x) with hs9
  set s10 : 𝔸 := y * y * y * y * (z - x) with hs10
  have a9 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9) s10
  have a8 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8) s9
  have a7 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6 + s7) s8
  have a6 := norm_add_le (s1 + s2 + s3 + s4 + s5 + s6) s7
  have a5 := norm_add_le (s1 + s2 + s3 + s4 + s5) s6
  have a4 := norm_add_le (s1 + s2 + s3 + s4) s5
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **5-product norm helper**: `‖A·B·C·D·E‖ ≤ ‖A‖·‖B‖·‖C‖·‖D‖·‖E‖`.
Factored out for use in the `bch_quintic_group_*_diff_le` lemmas. -/
lemma norm_5prod_le (A B C D E : 𝔸) :
    ‖A * B * C * D * E‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by
  calc ‖A * B * C * D * E‖
      ≤ ‖A * B * C * D‖ * ‖E‖ := norm_mul_le _ _
    _ ≤ ‖A * B * C‖ * ‖D‖ * ‖E‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖A * B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by gcongr; exact norm_mul_le _ _

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **6-product norm helper**: `‖A·B·C·D·E·F‖ ≤ ‖A‖·‖B‖·‖C‖·‖D‖·‖E‖·‖F‖`.
Factored out for use in the future `bch_sextic_term`-related diff bounds
(per-word Lipschitz lemmas needed for the parent T2-F7e discharge). -/
lemma norm_6prod_le (A B C D E F : 𝔸) :
    ‖A * B * C * D * E * F‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ := by
  calc ‖A * B * C * D * E * F‖
      ≤ ‖A * B * C * D * E‖ * ‖F‖ := norm_mul_le _ _
    _ ≤ ‖A * B * C * D‖ * ‖E‖ * ‖F‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖A * B * C‖ * ‖D‖ * ‖E‖ * ‖F‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖A * B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ := by gcongr; exact norm_mul_le _ _

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **7-product norm helper**: `‖A·B·C·D·E·F·G‖ ≤ ‖A‖·‖B‖·‖C‖·‖D‖·‖E‖·‖F‖·‖G‖`.
For T2-F7e Phase E.2 step 4 (C5_diff_residual norm bound, deg-7 monomials). -/
lemma norm_7prod_le (A B C D E F G : 𝔸) :
    ‖A * B * C * D * E * F * G‖ ≤
      ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ * ‖G‖ := by
  calc ‖A * B * C * D * E * F * G‖
      ≤ ‖A * B * C * D * E * F‖ * ‖G‖ := norm_mul_le _ _
    _ ≤ (‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖) * ‖G‖ :=
        mul_le_mul_of_nonneg_right (norm_6prod_le A B C D E F) (norm_nonneg _)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **8-product norm helper**: deg-8 generalization. -/
lemma norm_8prod_le (A B C D E F G H : 𝔸) :
    ‖A * B * C * D * E * F * G * H‖ ≤
      ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ * ‖G‖ * ‖H‖ := by
  calc ‖A * B * C * D * E * F * G * H‖
      ≤ ‖A * B * C * D * E * F * G‖ * ‖H‖ := norm_mul_le _ _
    _ ≤ (‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ * ‖G‖) * ‖H‖ :=
        mul_le_mul_of_nonneg_right (norm_7prod_le A B C D E F G) (norm_nonneg _)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **9-product norm helper**: deg-9 generalization. -/
lemma norm_9prod_le (A B C D E F G H I : 𝔸) :
    ‖A * B * C * D * E * F * G * H * I‖ ≤
      ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ * ‖G‖ * ‖H‖ * ‖I‖ := by
  calc ‖A * B * C * D * E * F * G * H * I‖
      ≤ ‖A * B * C * D * E * F * G * H‖ * ‖I‖ := norm_mul_le _ _
    _ ≤ (‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖F‖ * ‖G‖ * ‖H‖) * ‖I‖ :=
        mul_le_mul_of_nonneg_right (norm_8prod_le A B C D E F G H) (norm_nonneg _)

set_option maxHeartbeats 800000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Lipschitz bound for `bch_quintic_group_4` in its first argument**:
`‖group_4(z, y) − group_4(x, y)‖ ≤ 25 · (‖z‖+‖x‖+‖y‖)⁴ · ‖z − x‖`.

`bch_quintic_group_4` has 10 words; the a-position counts are
`{4, 3, 2, 4, 2, 3, 1, 3, 2, 1}`, summing to 25 telescoping summands.
Proof structure mirrors `norm_bch_quintic_group_1_diff_le`: telescoping
identity (`noncomm_ring`) + per-summand 5-product norm bound + 24-step
triangle inequality. -/
theorem norm_bch_quintic_group_4_diff_le (z x y : 𝔸) :
    ‖bch_quintic_group_4 z y - bch_quintic_group_4 x y‖ ≤
      25 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have htel : bch_quintic_group_4 z y - bch_quintic_group_4 x y =
      -- word 1: z·z·z·y·z (4 summands)
      (z - x) * z * z * y * z + x * (z - x) * z * y * z +
      x * x * (z - x) * y * z + x * x * x * y * (z - x) +
      -- word 2: z·z·z·y·y (3 summands)
      (z - x) * z * z * y * y + x * (z - x) * z * y * y +
      x * x * (z - x) * y * y +
      -- word 3: z·z·y·y·y (2 summands)
      (z - x) * z * y * y * y + x * (z - x) * y * y * y +
      -- word 4: z·y·z·z·z (4 summands)
      (z - x) * y * z * z * z + x * y * (z - x) * z * z +
      x * y * x * (z - x) * z + x * y * x * x * (z - x) +
      -- word 5: z·y·y·y·z (2 summands)
      (z - x) * y * y * y * z + x * y * y * y * (z - x) +
      -- word 6: y·z·z·z·y (3 summands)
      y * (z - x) * z * z * y + y * x * (z - x) * z * y +
      y * x * x * (z - x) * y +
      -- word 7: y·z·y·y·y (1 summand)
      y * (z - x) * y * y * y +
      -- word 8: y·y·z·z·z (3 summands)
      y * y * (z - x) * z * z + y * y * x * (z - x) * z +
      y * y * x * x * (z - x) +
      -- word 9: y·y·y·z·z (2 summands)
      y * y * y * (z - x) * z + y * y * y * x * (z - x) +
      -- word 10: y·y·y·z·y (1 summand)
      y * y * y * (z - x) * y := by
    unfold bch_quintic_group_4
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  set d := ‖z - x‖ with hd_def
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  -- Per-summand bounds. Each is M⁴·d via norm_5prod_le.
  -- We inline a single helper macro-ish pattern.
  have hM4d : ∀ (a₁ a₂ a₃ a₄ a₅ : 𝔸),
      ‖a₁‖ ≤ M → ‖a₂‖ ≤ M → ‖a₃‖ ≤ M → ‖a₄‖ ≤ M → ‖a₅‖ ≤ M →
      ‖a₁ * a₂ * a₃ * a₄ * a₅‖ ≤ M ^ 5 := fun a₁ a₂ a₃ a₄ a₅ h₁ h₂ h₃ h₄ h₅ => by
    calc _ ≤ ‖a₁‖ * ‖a₂‖ * ‖a₃‖ * ‖a₄‖ * ‖a₅‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * M * M * M := by gcongr
      _ = M ^ 5 := by ring
  -- Key lemma: any 5-product with one (z-x) and four ≤M factors is ≤ M⁴·d.
  -- Cases: (z-x) at position 1, 2, 3, 4, or 5.
  have hL1 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖(z - x) * a * b * c * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖z - x‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ d * M * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL2 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * (z - x) * b * c * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖z - x‖ * ‖b‖ * ‖c‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * d * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL3 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * b * (z - x) * c * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖b‖ * ‖z - x‖ * ‖c‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * d * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL4 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * b * c * (z - x) * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖z - x‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * M * d * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL5 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * b * c * d' * (z - x)‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d'‖ * ‖z - x‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * M * M * d := by gcongr
      _ = M ^ 4 * d := by ring
  -- Apply per-summand bounds. 25 summands.
  have h1  := hL1 z z y z hz_le hz_le hy_le hz_le
  have h2  := hL2 x z y z hx_le hz_le hy_le hz_le
  have h3  := hL3 x x y z hx_le hx_le hy_le hz_le
  have h4  := hL5 x x x y hx_le hx_le hx_le hy_le
  have h5  := hL1 z z y y hz_le hz_le hy_le hy_le
  have h6  := hL2 x z y y hx_le hz_le hy_le hy_le
  have h7  := hL3 x x y y hx_le hx_le hy_le hy_le
  have h8  := hL1 z y y y hz_le hy_le hy_le hy_le
  have h9  := hL2 x y y y hx_le hy_le hy_le hy_le
  have h10 := hL1 y z z z hy_le hz_le hz_le hz_le
  have h11 := hL3 x y z z hx_le hy_le hz_le hz_le
  have h12 := hL4 x y x z hx_le hy_le hx_le hz_le
  have h13 := hL5 x y x x hx_le hy_le hx_le hx_le
  have h14 := hL1 y y y z hy_le hy_le hy_le hz_le
  have h15 := hL5 x y y y hx_le hy_le hy_le hy_le
  have h16 := hL2 y z z y hy_le hz_le hz_le hy_le
  have h17 := hL3 y x z y hy_le hx_le hz_le hy_le
  have h18 := hL4 y x x y hy_le hx_le hx_le hy_le
  have h19 := hL2 y y y y hy_le hy_le hy_le hy_le
  have h20 := hL3 y y z z hy_le hy_le hz_le hz_le
  have h21 := hL4 y y x z hy_le hy_le hx_le hz_le
  have h22 := hL5 y y x x hy_le hy_le hx_le hx_le
  have h23 := hL4 y y y z hy_le hy_le hy_le hz_le
  have h24 := hL5 y y y x hy_le hy_le hy_le hx_le
  have h25 := hL4 y y y y hy_le hy_le hy_le hy_le
  -- Triangle inequality on the 25-term sum
  set t1  : 𝔸 := (z - x) * z * z * y * z
  set t2  : 𝔸 := x * (z - x) * z * y * z
  set t3  : 𝔸 := x * x * (z - x) * y * z
  set t4  : 𝔸 := x * x * x * y * (z - x)
  set t5  : 𝔸 := (z - x) * z * z * y * y
  set t6  : 𝔸 := x * (z - x) * z * y * y
  set t7  : 𝔸 := x * x * (z - x) * y * y
  set t8  : 𝔸 := (z - x) * z * y * y * y
  set t9  : 𝔸 := x * (z - x) * y * y * y
  set t10 : 𝔸 := (z - x) * y * z * z * z
  set t11 : 𝔸 := x * y * (z - x) * z * z
  set t12 : 𝔸 := x * y * x * (z - x) * z
  set t13 : 𝔸 := x * y * x * x * (z - x)
  set t14 : 𝔸 := (z - x) * y * y * y * z
  set t15 : 𝔸 := x * y * y * y * (z - x)
  set t16 : 𝔸 := y * (z - x) * z * z * y
  set t17 : 𝔸 := y * x * (z - x) * z * y
  set t18 : 𝔸 := y * x * x * (z - x) * y
  set t19 : 𝔸 := y * (z - x) * y * y * y
  set t20 : 𝔸 := y * y * (z - x) * z * z
  set t21 : 𝔸 := y * y * x * (z - x) * z
  set t22 : 𝔸 := y * y * x * x * (z - x)
  set t23 : 𝔸 := y * y * y * (z - x) * z
  set t24 : 𝔸 := y * y * y * x * (z - x)
  set t25 : 𝔸 := y * y * y * (z - x) * y
  -- 24 norm_add_le applications
  have a24 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24) t25
  have a23 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23) t24
  have a22 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22) t23
  have a21 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21) t22
  have a20 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20) t21
  have a19 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17 + t18 + t19) t20
  have a18 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17 + t18) t19
  have a17 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16 + t17) t18
  have a16 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15 + t16) t17
  have a15 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14 + t15) t16
  have a14 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13 + t14) t15
  have a13 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 +
    t13) t14
  have a12 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12) t13
  have a11 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11) t12
  have a10 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11
  have a9  := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10
  have a8  := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9
  have a7  := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have a6  := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7
  have a5  := norm_add_le (t1 + t2 + t3 + t4 + t5) t6
  have a4  := norm_add_le (t1 + t2 + t3 + t4) t5
  have a3  := norm_add_le (t1 + t2 + t3) t4
  have a2  := norm_add_le (t1 + t2) t3
  have a1  := norm_add_le t1 t2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Lipschitz bound for `bch_quintic_group_24` in its first argument**:
`‖group_24(z, y) − group_24(x, y)‖ ≤ 5 · (‖z‖+‖x‖+‖y‖)⁴ · ‖z − x‖`.

`bch_quintic_group_24 = a·b·a·b·a + b·a·b·a·b` has 2 words with a-position
counts `{3, 2}`, summing to 5 telescoping summands. -/
theorem norm_bch_quintic_group_24_diff_le (z x y : 𝔸) :
    ‖bch_quintic_group_24 z y - bch_quintic_group_24 x y‖ ≤
      5 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have htel : bch_quintic_group_24 z y - bch_quintic_group_24 x y =
      -- word 1: z·y·z·y·z (3 summands)
      (z - x) * y * z * y * z + x * y * (z - x) * y * z + x * y * x * y * (z - x) +
      -- word 2: y·z·y·z·y (2 summands)
      y * (z - x) * y * z * y + y * x * y * (z - x) * y := by
    unfold bch_quintic_group_24
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  set d := ‖z - x‖ with hd_def
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 : ‖(z - x) * y * z * y * z‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖z - x‖ * ‖y‖ * ‖z‖ * ‖y‖ * ‖z‖ := norm_5prod_le _ _ _ _ _
      _ ≤ d * M * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h2 : ‖x * y * (z - x) * y * z‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖x‖ * ‖y‖ * ‖z - x‖ * ‖y‖ * ‖z‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * d * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h3 : ‖x * y * x * y * (z - x)‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖x‖ * ‖y‖ * ‖x‖ * ‖y‖ * ‖z - x‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * M * M * d := by gcongr
      _ = M ^ 4 * d := by ring
  have h4 : ‖y * (z - x) * y * z * y‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖y‖ * ‖z - x‖ * ‖y‖ * ‖z‖ * ‖y‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * d * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have h5 : ‖y * x * y * (z - x) * y‖ ≤ M ^ 4 * d := by
    calc _ ≤ ‖y‖ * ‖x‖ * ‖y‖ * ‖z - x‖ * ‖y‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * M * d * M := by gcongr
      _ = M ^ 4 * d := by ring
  set s1 : 𝔸 := (z - x) * y * z * y * z
  set s2 : 𝔸 := x * y * (z - x) * y * z
  set s3 : 𝔸 := x * y * x * y * (z - x)
  set s4 : 𝔸 := y * (z - x) * y * z * y
  set s5 : 𝔸 := y * x * y * (z - x) * y
  have a4 := norm_add_le (s1 + s2 + s3 + s4) s5
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

set_option maxHeartbeats 1600000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Lipschitz bound for `bch_quintic_group_6` in its first argument**:
`‖group_6(z, y) − group_6(x, y)‖ ≤ 35 · (‖z‖+‖x‖+‖y‖)⁴ · ‖z − x‖`.

`bch_quintic_group_6` has 14 words; the a-position counts are
`{4, 3, 3, 3, 2, 3, 2, 3, 2, 3, 2, 2, 2, 1}`, summing to 35 telescoping
summands. -/
theorem norm_bch_quintic_group_6_diff_le (z x y : 𝔸) :
    ‖bch_quintic_group_6 z y - bch_quintic_group_6 x y‖ ≤
      35 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have htel : bch_quintic_group_6 z y - bch_quintic_group_6 x y =
      -- word 1: a·a·b·a·a → z·z·y·z·z (a-pos {1,2,4,5}, 4 summands)
      (z - x) * z * y * z * z + x * (z - x) * y * z * z +
      x * x * y * (z - x) * z + x * x * y * x * (z - x) +
      -- word 2: a·a·b·a·b → z·z·y·z·y (a-pos {1,2,4}, 3 summands)
      (z - x) * z * y * z * y + x * (z - x) * y * z * y +
      x * x * y * (z - x) * y +
      -- word 3: a·a·b·b·a → z·z·y·y·z (a-pos {1,2,5}, 3 summands)
      (z - x) * z * y * y * z + x * (z - x) * y * y * z +
      x * x * y * y * (z - x) +
      -- word 4: a·b·a·a·b → z·y·z·z·y (a-pos {1,3,4}, 3 summands)
      (z - x) * y * z * z * y + x * y * (z - x) * z * y +
      x * y * x * (z - x) * y +
      -- word 5: a·b·a·b·b → z·y·z·y·y (a-pos {1,3}, 2 summands)
      (z - x) * y * z * y * y + x * y * (z - x) * y * y +
      -- word 6: a·b·b·a·a → z·y·y·z·z (a-pos {1,4,5}, 3 summands)
      (z - x) * y * y * z * z + x * y * y * (z - x) * z +
      x * y * y * x * (z - x) +
      -- word 7: a·b·b·a·b → z·y·y·z·y (a-pos {1,4}, 2 summands)
      (z - x) * y * y * z * y + x * y * y * (z - x) * y +
      -- word 8: b·a·a·b·a → y·z·z·y·z (a-pos {2,3,5}, 3 summands)
      y * (z - x) * z * y * z + y * x * (z - x) * y * z +
      y * x * x * y * (z - x) +
      -- word 9: b·a·a·b·b → y·z·z·y·y (a-pos {2,3}, 2 summands)
      y * (z - x) * z * y * y + y * x * (z - x) * y * y +
      -- word 10: b·a·b·a·a → y·z·y·z·z (a-pos {2,4,5}, 3 summands)
      y * (z - x) * y * z * z + y * x * y * (z - x) * z +
      y * x * y * x * (z - x) +
      -- word 11: b·a·b·b·a → y·z·y·y·z (a-pos {2,5}, 2 summands)
      y * (z - x) * y * y * z + y * x * y * y * (z - x) +
      -- word 12: b·b·a·a·b → y·y·z·z·y (a-pos {3,4}, 2 summands)
      y * y * (z - x) * z * y + y * y * x * (z - x) * y +
      -- word 13: b·b·a·b·a → y·y·z·y·z (a-pos {3,5}, 2 summands)
      y * y * (z - x) * y * z + y * y * x * y * (z - x) +
      -- word 14: b·b·a·b·b → y·y·z·y·y (a-pos {3}, 1 summand)
      y * y * (z - x) * y * y := by
    unfold bch_quintic_group_6
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  set d := ‖z - x‖ with hd_def
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  -- Position-specific helpers (same as in group_4)
  have hL1 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖(z - x) * a * b * c * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖z - x‖ * ‖a‖ * ‖b‖ * ‖c‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ d * M * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL2 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * (z - x) * b * c * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖z - x‖ * ‖b‖ * ‖c‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * d * M * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL3 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * b * (z - x) * c * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖b‖ * ‖z - x‖ * ‖c‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * d * M * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL4 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * b * c * (z - x) * d'‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖z - x‖ * ‖d'‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * M * d * M := by gcongr
      _ = M ^ 4 * d := by ring
  have hL5 : ∀ a b c d' : 𝔸, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖c‖ ≤ M → ‖d'‖ ≤ M →
      ‖a * b * c * d' * (z - x)‖ ≤ M ^ 4 * d := fun a b c d' ha hb hc hd' => by
    calc _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d'‖ * ‖z - x‖ := norm_5prod_le _ _ _ _ _
      _ ≤ M * M * M * M * d := by gcongr
      _ = M ^ 4 * d := by ring
  -- Apply per-summand bounds. 35 summands.
  have h01 := hL1 z y z z hz_le hy_le hz_le hz_le
  have h02 := hL2 x y z z hx_le hy_le hz_le hz_le
  have h03 := hL4 x x y z hx_le hx_le hy_le hz_le
  have h04 := hL5 x x y x hx_le hx_le hy_le hx_le
  have h05 := hL1 z y z y hz_le hy_le hz_le hy_le
  have h06 := hL2 x y z y hx_le hy_le hz_le hy_le
  have h07 := hL4 x x y y hx_le hx_le hy_le hy_le
  have h08 := hL1 z y y z hz_le hy_le hy_le hz_le
  have h09 := hL2 x y y z hx_le hy_le hy_le hz_le
  have h10 := hL5 x x y y hx_le hx_le hy_le hy_le
  have h11 := hL1 y z z y hy_le hz_le hz_le hy_le
  have h12 := hL3 x y z y hx_le hy_le hz_le hy_le
  have h13 := hL4 x y x y hx_le hy_le hx_le hy_le
  have h14 := hL1 y z y y hy_le hz_le hy_le hy_le
  have h15 := hL3 x y y y hx_le hy_le hy_le hy_le
  have h16 := hL1 y y z z hy_le hy_le hz_le hz_le
  have h17 := hL4 x y y z hx_le hy_le hy_le hz_le
  have h18 := hL5 x y y x hx_le hy_le hy_le hx_le
  have h19 := hL1 y y z y hy_le hy_le hz_le hy_le
  have h20 := hL4 x y y y hx_le hy_le hy_le hy_le
  have h21 := hL2 y z y z hy_le hz_le hy_le hz_le
  have h22 := hL3 y x y z hy_le hx_le hy_le hz_le
  have h23 := hL5 y x x y hy_le hx_le hx_le hy_le
  have h24 := hL2 y z y y hy_le hz_le hy_le hy_le
  have h25 := hL3 y x y y hy_le hx_le hy_le hy_le
  have h26 := hL2 y y z z hy_le hy_le hz_le hz_le
  have h27 := hL4 y x y z hy_le hx_le hy_le hz_le
  have h28 := hL5 y x y x hy_le hx_le hy_le hx_le
  have h29 := hL2 y y y z hy_le hy_le hy_le hz_le
  have h30 := hL5 y x y y hy_le hx_le hy_le hy_le
  have h31 := hL3 y y z y hy_le hy_le hz_le hy_le
  have h32 := hL4 y y x y hy_le hy_le hx_le hy_le
  have h33 := hL3 y y y z hy_le hy_le hy_le hz_le
  have h34 := hL5 y y x y hy_le hy_le hx_le hy_le
  have h35 := hL3 y y y y hy_le hy_le hy_le hy_le
  -- Triangle inequality on the 35-term sum
  set t01 : 𝔸 := (z - x) * z * y * z * z
  set t02 : 𝔸 := x * (z - x) * y * z * z
  set t03 : 𝔸 := x * x * y * (z - x) * z
  set t04 : 𝔸 := x * x * y * x * (z - x)
  set t05 : 𝔸 := (z - x) * z * y * z * y
  set t06 : 𝔸 := x * (z - x) * y * z * y
  set t07 : 𝔸 := x * x * y * (z - x) * y
  set t08 : 𝔸 := (z - x) * z * y * y * z
  set t09 : 𝔸 := x * (z - x) * y * y * z
  set t10 : 𝔸 := x * x * y * y * (z - x)
  set t11 : 𝔸 := (z - x) * y * z * z * y
  set t12 : 𝔸 := x * y * (z - x) * z * y
  set t13 : 𝔸 := x * y * x * (z - x) * y
  set t14 : 𝔸 := (z - x) * y * z * y * y
  set t15 : 𝔸 := x * y * (z - x) * y * y
  set t16 : 𝔸 := (z - x) * y * y * z * z
  set t17 : 𝔸 := x * y * y * (z - x) * z
  set t18 : 𝔸 := x * y * y * x * (z - x)
  set t19 : 𝔸 := (z - x) * y * y * z * y
  set t20 : 𝔸 := x * y * y * (z - x) * y
  set t21 : 𝔸 := y * (z - x) * z * y * z
  set t22 : 𝔸 := y * x * (z - x) * y * z
  set t23 : 𝔸 := y * x * x * y * (z - x)
  set t24 : 𝔸 := y * (z - x) * z * y * y
  set t25 : 𝔸 := y * x * (z - x) * y * y
  set t26 : 𝔸 := y * (z - x) * y * z * z
  set t27 : 𝔸 := y * x * y * (z - x) * z
  set t28 : 𝔸 := y * x * y * x * (z - x)
  set t29 : 𝔸 := y * (z - x) * y * y * z
  set t30 : 𝔸 := y * x * y * y * (z - x)
  set t31 : 𝔸 := y * y * (z - x) * z * y
  set t32 : 𝔸 := y * y * x * (z - x) * y
  set t33 : 𝔸 := y * y * (z - x) * y * z
  set t34 : 𝔸 := y * y * x * y * (z - x)
  set t35 : 𝔸 := y * y * (z - x) * y * y
  -- 34 norm_add_le applications
  have a34 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27 + t28 + t29 + t30 + t31 + t32 + t33 + t34) t35
  have a33 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27 + t28 + t29 + t30 + t31 + t32 + t33) t34
  have a32 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27 + t28 + t29 + t30 + t31 + t32) t33
  have a31 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27 + t28 + t29 + t30 + t31) t32
  have a30 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27 + t28 + t29 + t30) t31
  have a29 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27 + t28 + t29) t30
  have a28 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27 + t28) t29
  have a27 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27) t28
  have a26 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26) t27
  have a25 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25) t26
  have a24 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24) t25
  have a23 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23) t24
  have a22 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22) t23
  have a21 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21) t22
  have a20 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20) t21
  have a19 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19) t20
  have a18 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18) t19
  have a17 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17) t18
  have a16 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16) t17
  have a15 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15) t16
  have a14 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14) t15
  have a13 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13) t14
  have a12 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12) t13
  have a11 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 + t11) t12
  have a10 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10) t11
  have a09 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09) t10
  have a08 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08) t09
  have a07 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07) t08
  have a06 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06) t07
  have a05 := norm_add_le (t01 + t02 + t03 + t04 + t05) t06
  have a04 := norm_add_le (t01 + t02 + t03 + t04) t05
  have a03 := norm_add_le (t01 + t02 + t03) t04
  have a02 := norm_add_le (t01 + t02) t03
  have a01 := norm_add_le t01 t02
  linarith

include 𝕂 in
/-- **Lipschitz bound for `bch_quintic_term` in its first argument**:
`‖C₅(z, y) − C₅(x, y)‖ ≤ (‖z‖+‖x‖+‖y‖)⁴ · ‖z − x‖`.

Combines the 4 per-group Lipschitz bounds with the (720)⁻¹ scalar factor:
`(10 + 4·25 + 6·35 + 24·5)/720 = 440/720 = 11/18 < 1`.

This is the analog of `norm_bch_cubic_term_diff_le` at degree 5; both are
key infrastructure for the parent T2-F7e discharge. With `z = (a'+b) + W`
(where ‖W‖ = O(s²)), this gives `‖C₅(z, y) − C₅(a'+b, y)‖ ≤ K · s² · M⁴ ≤
K · s⁶`, the deg-6+ residual estimate needed in the extended hdecomp. -/
theorem norm_bch_quintic_term_diff_le (z x y : 𝔸) :
    ‖bch_quintic_term 𝕂 z y - bch_quintic_term 𝕂 x y‖ ≤
      (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  set d := ‖z - x‖ with hd_def
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hM_nn : 0 ≤ M := by positivity
  have hM4_nn : (0 : ℝ) ≤ M ^ 4 := pow_nonneg hM_nn 4
  -- Per-group bounds.
  have hg1 := norm_bch_quintic_group_1_diff_le z x y
  have hg4 := norm_bch_quintic_group_4_diff_le z x y
  have hg6 := norm_bch_quintic_group_6_diff_le z x y
  have hg24 := norm_bch_quintic_group_24_diff_le z x y
  -- Identity: bch_quintic_term diff = (720)⁻¹ • (per-group diffs combo).
  have htel : bch_quintic_term 𝕂 z y - bch_quintic_term 𝕂 x y =
      (720 : 𝕂)⁻¹ • (
        -(bch_quintic_group_1 z y - bch_quintic_group_1 x y)
        + (4 : 𝕂) • (bch_quintic_group_4 z y - bch_quintic_group_4 x y)
        - (6 : 𝕂) • (bch_quintic_group_6 z y - bch_quintic_group_6 x y)
        + (24 : 𝕂) • (bch_quintic_group_24 z y - bch_quintic_group_24 x y)) := by
    unfold bch_quintic_term
    simp only [smul_sub, smul_add, smul_neg]
    abel
  rw [htel]
  -- Norm bound on the smul'd expression.
  set d1 : 𝔸 := bch_quintic_group_1 z y - bch_quintic_group_1 x y
  set d4 : 𝔸 := bch_quintic_group_4 z y - bch_quintic_group_4 x y
  set d6 : 𝔸 := bch_quintic_group_6 z y - bch_quintic_group_6 x y
  set d24 : 𝔸 := bch_quintic_group_24 z y - bch_quintic_group_24 x y
  -- Bounds on the smul'd diffs
  have h_neg_d1 : ‖-d1‖ ≤ 10 * M ^ 4 * d := by
    rw [norm_neg]; exact hg1
  have h_4_d4 : ‖((4 : 𝕂)) • d4‖ ≤ 100 * M ^ 4 * d := by
    calc ‖((4 : 𝕂)) • d4‖ ≤ ‖((4 : 𝕂))‖ * ‖d4‖ := norm_smul_le _ _
      _ = 4 * ‖d4‖ := by rw [RCLike.norm_ofNat]
      _ ≤ 4 * (25 * M ^ 4 * d) := by gcongr
      _ = 100 * M ^ 4 * d := by ring
  have h_6_d6 : ‖((6 : 𝕂)) • d6‖ ≤ 210 * M ^ 4 * d := by
    calc ‖((6 : 𝕂)) • d6‖ ≤ ‖((6 : 𝕂))‖ * ‖d6‖ := norm_smul_le _ _
      _ = 6 * ‖d6‖ := by rw [RCLike.norm_ofNat]
      _ ≤ 6 * (35 * M ^ 4 * d) := by gcongr
      _ = 210 * M ^ 4 * d := by ring
  have h_24_d24 : ‖((24 : 𝕂)) • d24‖ ≤ 120 * M ^ 4 * d := by
    calc ‖((24 : 𝕂)) • d24‖ ≤ ‖((24 : 𝕂))‖ * ‖d24‖ := norm_smul_le _ _
      _ = 24 * ‖d24‖ := by rw [RCLike.norm_ofNat]
      _ ≤ 24 * (5 * M ^ 4 * d) := by gcongr
      _ = 120 * M ^ 4 * d := by ring
  -- Triangle inequality for the 4-term sum
  set S : 𝔸 := -d1 + (4 : 𝕂) • d4 - (6 : 𝕂) • d6 + (24 : 𝕂) • d24 with hS_def
  have hS_eq : S = -d1 + (4 : 𝕂) • d4 + (-((6 : 𝕂) • d6)) + (24 : 𝕂) • d24 := by
    rw [hS_def]; abel
  have hS_le : ‖S‖ ≤ 440 * M ^ 4 * d := by
    rw [hS_eq]
    have a3 := norm_add_le (-d1 + (4 : 𝕂) • d4 + (-((6 : 𝕂) • d6))) ((24 : 𝕂) • d24)
    have a2 := norm_add_le (-d1 + (4 : 𝕂) • d4) (-((6 : 𝕂) • d6))
    have a1 := norm_add_le (-d1) ((4 : 𝕂) • d4)
    have h_neg : ‖-((6 : 𝕂) • d6)‖ = ‖((6 : 𝕂) • d6)‖ := norm_neg _
    rw [h_neg] at a2
    linarith
  -- Final smul bound
  have h720 : ‖((720 : 𝕂)⁻¹)‖ = 1 / 720 := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  calc ‖((720 : 𝕂)⁻¹) • S‖
      ≤ ‖((720 : 𝕂)⁻¹)‖ * ‖S‖ := norm_smul_le _ _
    _ = (1 / 720) * ‖S‖ := by rw [h720]
    _ ≤ (1 / 720) * (440 * M ^ 4 * d) := by
        apply mul_le_mul_of_nonneg_left hS_le (by norm_num)
    _ ≤ M ^ 4 * d := by nlinarith [hM4_nn, hd_nn]

/-! ### Per-group LQ decompositions for `bch_quintic_group_*`

These are the building blocks for `bch_quintic_term_LQ_decomp` (T2-F7e Phase E.2
step 4 foundation). Each decomposes `group_k(x+W, y) - group_k(x, y)` into
linear-in-W + quadratic-in-W + (cubic-in-W) + (quartic-in-W) parts.

For W = V₂ = ½·[a',b] (degree 2 in (a, b)) and y = a' (degree 1), each piece
is naturally bounded:
- linear-in-W: M⁴·‖W‖ scaling.
- quadratic-in-W: M³·‖W‖² scaling.
- cubic-in-W: M²·‖W‖³ scaling.
- quartic-in-W: M·‖W‖⁴ scaling.

When ‖W‖ ≤ s²/2 (V₂ bound), each piece is O(s⁷). -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Per-group LQ decomposition (group 1)**: 4 monomials → 10 linear + 12 quadratic + 8 cubic + 2 quartic = 32 sub-terms.
The 4 monomials are `aaaab`, `abbbb`, `baaaa`, `bbbba`. After substituting first-arg `a → x+W`,
each contributes 2^k - 1 sub-terms by W-count (where k = #a's of monomial). -/
theorem bch_quintic_group_1_LQ_decomp (x W y : 𝔸) :
    bch_quintic_group_1 (x + W) y - bch_quintic_group_1 x y =
    -- Linear-in-W (10 sub-terms): 4 from aaaab + 1 from abbbb + 4 from baaaa + 1 from bbbba
    (W * x * x * x * y + x * W * x * x * y + x * x * W * x * y + x * x * x * W * y +
     W * y * y * y * y +
     y * W * x * x * x + y * x * W * x * x + y * x * x * W * x + y * x * x * x * W +
     y * y * y * y * W) +
    -- Quadratic-in-W (12 sub-terms): 6 from aaaab + 6 from baaaa
    (W * W * x * x * y + W * x * W * x * y + W * x * x * W * y +
     x * W * W * x * y + x * W * x * W * y + x * x * W * W * y +
     y * W * W * x * x + y * W * x * W * x + y * W * x * x * W +
     y * x * W * W * x + y * x * W * x * W + y * x * x * W * W) +
    -- Cubic-in-W (8 sub-terms): 4 from aaaab + 4 from baaaa
    (W * W * W * x * y + W * W * x * W * y + W * x * W * W * y + x * W * W * W * y +
     y * W * W * W * x + y * W * W * x * W + y * W * x * W * W + y * x * W * W * W) +
    -- Quartic-in-W (2 sub-terms): from aaaab + baaaa
    (W * W * W * W * y + y * W * W * W * W) := by
  unfold bch_quintic_group_1
  noncomm_ring

set_option maxHeartbeats 3200000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Per-group LQ decomposition (group 6)**: 14 monomials → 35 linear + 30 quadratic + 10 cubic + 1 quartic = 76 sub-terms.
The 14 monomials are `aabaa, aabab, aabba, abaab, ababb, abbaa, abbab, baaba, baabb, babaa, babba, bbaab, bbaba, bbabb`. -/
theorem bch_quintic_group_6_LQ_decomp (x W y : 𝔸) :
    bch_quintic_group_6 (x + W) y - bch_quintic_group_6 x y =
    -- Linear-in-W (35 sub-terms)
    (-- aabaa (4, a-pos 1,2,4,5)
     W * x * y * x * x + x * W * y * x * x + x * x * y * W * x + x * x * y * x * W +
     -- aabab (3, a-pos 1,2,4)
     W * x * y * x * y + x * W * y * x * y + x * x * y * W * y +
     -- aabba (3, a-pos 1,2,5)
     W * x * y * y * x + x * W * y * y * x + x * x * y * y * W +
     -- abaab (3, a-pos 1,3,4)
     W * y * x * x * y + x * y * W * x * y + x * y * x * W * y +
     -- ababb (2, a-pos 1,3)
     W * y * x * y * y + x * y * W * y * y +
     -- abbaa (3, a-pos 1,4,5)
     W * y * y * x * x + x * y * y * W * x + x * y * y * x * W +
     -- abbab (2, a-pos 1,4)
     W * y * y * x * y + x * y * y * W * y +
     -- baaba (3, a-pos 2,3,5)
     y * W * x * y * x + y * x * W * y * x + y * x * x * y * W +
     -- baabb (2, a-pos 2,3)
     y * W * x * y * y + y * x * W * y * y +
     -- babaa (3, a-pos 2,4,5)
     y * W * y * x * x + y * x * y * W * x + y * x * y * x * W +
     -- babba (2, a-pos 2,5)
     y * W * y * y * x + y * x * y * y * W +
     -- bbaab (2, a-pos 3,4)
     y * y * W * x * y + y * y * x * W * y +
     -- bbaba (2, a-pos 3,5)
     y * y * W * y * x + y * y * x * y * W +
     -- bbabb (1, a-pos 3)
     y * y * W * y * y) +
    -- Quadratic-in-W (30 sub-terms)
    (-- aabaa (6, pairs {1,2,4,5}: (1,2),(1,4),(1,5),(2,4),(2,5),(4,5))
     W * W * y * x * x + W * x * y * W * x + W * x * y * x * W +
     x * W * y * W * x + x * W * y * x * W + x * x * y * W * W +
     -- aabab (3, pairs (1,2),(1,4),(2,4))
     W * W * y * x * y + W * x * y * W * y + x * W * y * W * y +
     -- aabba (3, pairs (1,2),(1,5),(2,5))
     W * W * y * y * x + W * x * y * y * W + x * W * y * y * W +
     -- abaab (3, pairs (1,3),(1,4),(3,4))
     W * y * W * x * y + W * y * x * W * y + x * y * W * W * y +
     -- ababb (1, pair (1,3))
     W * y * W * y * y +
     -- abbaa (3, pairs (1,4),(1,5),(4,5))
     W * y * y * W * x + W * y * y * x * W + x * y * y * W * W +
     -- abbab (1, pair (1,4))
     W * y * y * W * y +
     -- baaba (3, pairs (2,3),(2,5),(3,5))
     y * W * W * y * x + y * W * x * y * W + y * x * W * y * W +
     -- baabb (1, pair (2,3))
     y * W * W * y * y +
     -- babaa (3, pairs (2,4),(2,5),(4,5))
     y * W * y * W * x + y * W * y * x * W + y * x * y * W * W +
     -- babba (1, pair (2,5))
     y * W * y * y * W +
     -- bbaab (1, pair (3,4))
     y * y * W * W * y +
     -- bbaba (1, pair (3,5))
     y * y * W * y * W) +
    -- Cubic-in-W (10 sub-terms)
    (-- aabaa (4, triples (1,2,4),(1,2,5),(1,4,5),(2,4,5))
     W * W * y * W * x + W * W * y * x * W + W * x * y * W * W + x * W * y * W * W +
     -- aabab (1, triple (1,2,4))
     W * W * y * W * y +
     -- aabba (1, triple (1,2,5))
     W * W * y * y * W +
     -- abaab (1, triple (1,3,4))
     W * y * W * W * y +
     -- abbaa (1, triple (1,4,5))
     W * y * y * W * W +
     -- baaba (1, triple (2,3,5))
     y * W * W * y * W +
     -- babaa (1, triple (2,4,5))
     y * W * y * W * W) +
    -- Quartic-in-W (1 sub-term)
    -- aabaa (quadruple (1,2,4,5))
    W * W * y * W * W := by
  unfold bch_quintic_group_6
  noncomm_ring

set_option maxHeartbeats 1600000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Per-group LQ decomposition (group 4)**: 10 monomials → 25 linear + 24 quadratic + 11 cubic + 2 quartic = 62 sub-terms.
The 10 monomials are `aaaba, aaabb, aabbb, abaaa, abbba, baaab, babbb, bbaaa, bbbaa, bbbab`. -/
theorem bch_quintic_group_4_LQ_decomp (x W y : 𝔸) :
    bch_quintic_group_4 (x + W) y - bch_quintic_group_4 x y =
    -- Linear-in-W (25 sub-terms)
    (-- aaaba (4 sub-terms): W at pos 1, 2, 3, 5
     W * x * x * y * x + x * W * x * y * x + x * x * W * y * x + x * x * x * y * W +
     -- aaabb (3 sub-terms): W at pos 1, 2, 3
     W * x * x * y * y + x * W * x * y * y + x * x * W * y * y +
     -- aabbb (2 sub-terms): W at pos 1, 2
     W * x * y * y * y + x * W * y * y * y +
     -- abaaa (4 sub-terms): W at pos 1, 3, 4, 5
     W * y * x * x * x + x * y * W * x * x + x * y * x * W * x + x * y * x * x * W +
     -- abbba (2 sub-terms): W at pos 1, 5
     W * y * y * y * x + x * y * y * y * W +
     -- baaab (3 sub-terms): W at pos 2, 3, 4
     y * W * x * x * y + y * x * W * x * y + y * x * x * W * y +
     -- babbb (1 sub-term): W at pos 2
     y * W * y * y * y +
     -- bbaaa (3 sub-terms): W at pos 3, 4, 5
     y * y * W * x * x + y * y * x * W * x + y * y * x * x * W +
     -- bbbaa (2 sub-terms): W at pos 4, 5
     y * y * y * W * x + y * y * y * x * W +
     -- bbbab (1 sub-term): W at pos 4
     y * y * y * W * y) +
    -- Quadratic-in-W (24 sub-terms)
    (-- aaaba (6 sub-terms): pairs (1,2), (1,3), (1,5), (2,3), (2,5), (3,5)
     W * W * x * y * x + W * x * W * y * x + W * x * x * y * W +
     x * W * W * y * x + x * W * x * y * W + x * x * W * y * W +
     -- aaabb (3 sub-terms): pairs (1,2), (1,3), (2,3)
     W * W * x * y * y + W * x * W * y * y + x * W * W * y * y +
     -- aabbb (1 sub-term): pair (1,2)
     W * W * y * y * y +
     -- abaaa (6 sub-terms): pairs (1,3), (1,4), (1,5), (3,4), (3,5), (4,5)
     W * y * W * x * x + W * y * x * W * x + W * y * x * x * W +
     x * y * W * W * x + x * y * W * x * W + x * y * x * W * W +
     -- abbba (1 sub-term): pair (1,5)
     W * y * y * y * W +
     -- baaab (3 sub-terms): pairs (2,3), (2,4), (3,4)
     y * W * W * x * y + y * W * x * W * y + y * x * W * W * y +
     -- bbaaa (3 sub-terms): pairs (3,4), (3,5), (4,5)
     y * y * W * W * x + y * y * W * x * W + y * y * x * W * W +
     -- bbbaa (1 sub-term): pair (4,5)
     y * y * y * W * W) +
    -- Cubic-in-W (11 sub-terms)
    (-- aaaba (4 sub-terms): triples (1,2,3), (1,2,5), (1,3,5), (2,3,5)
     W * W * W * y * x + W * W * x * y * W + W * x * W * y * W + x * W * W * y * W +
     -- aaabb (1 sub-term): triple (1,2,3)
     W * W * W * y * y +
     -- abaaa (4 sub-terms): triples (1,3,4), (1,3,5), (1,4,5), (3,4,5)
     W * y * W * W * x + W * y * W * x * W + W * y * x * W * W + x * y * W * W * W +
     -- baaab (1 sub-term): triple (2,3,4)
     y * W * W * W * y +
     -- bbaaa (1 sub-term): triple (3,4,5)
     y * y * W * W * W) +
    -- Quartic-in-W (2 sub-terms)
    (-- aaaba: quadruple (1,2,3,5)
     W * W * W * y * W +
     -- abaaa: quadruple (1,3,4,5)
     W * y * W * W * W) := by
  unfold bch_quintic_group_4
  noncomm_ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Per-group LQ decomposition (group 24)**: 2 monomials → 5 linear + 4 quadratic + 1 cubic = 10 sub-terms.
The 2 monomials are `ababa`, `babab`. -/
theorem bch_quintic_group_24_LQ_decomp (x W y : 𝔸) :
    bch_quintic_group_24 (x + W) y - bch_quintic_group_24 x y =
    -- Linear-in-W (5 sub-terms): from ababa (3) + babab (2)
    (x * y * x * y * W + x * y * W * y * x + W * y * x * y * x +
     y * x * y * W * y + y * W * y * x * y) +
    -- Quadratic-in-W (4 sub-terms): from ababa (3) + babab (1)
    (x * y * W * y * W + W * y * x * y * W + W * y * W * y * x +
     y * W * y * W * y) +
    -- Cubic-in-W (1 sub-term): from ababa
    W * y * W * y * W := by
  unfold bch_quintic_group_24
  noncomm_ring

/-! ### `bch_sextic_term` — the τ⁶ coefficient of `bch(a, b)`

Explicit 28-term polynomial in {a, b}, derived via the CAS pipeline at
`Lean-Trotter/scripts/extract_bch_z6.py` (extends `extract_bch_z5.py` to
degree 6). Common denominator 1440; integer numerators in {±1, ±4, ±6, ±24}.
Sum of |numerators|/1440 = 164/1440 ≈ 0.1139 < 1, so `‖Z₆(a,b)‖ ≤ s⁶`.

This is the next term in the BCH expansion after `bch_quintic_term`:
`bch(a,b) = a + b + ½[a,b] + Z₃ + Z₄ + Z₅ + Z₆ + O(·^7)`.

Used in the sextic identity (T2-F7e) for canceling deg-6 contributions to
`sym_bch_cubic - sym_E₃ - sym_E₅`. -/

/-- **τ⁶ coefficient of `bch(a, b)`** — explicit 28-term polynomial in {a, b}.

The 28 non-zero 6-letter words (out of 64 = 2⁶ possible) come from the
free Lie algebra basis at degree 6. Coefficients are rational with LCM 1440. -/
noncomputable def bch_sextic_term (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
    (-1 / 1440 : 𝕂) • (a * a * a * a * b * b)
  + (4 / 1440 : 𝕂) • (a * a * a * b * a * b)
  + (4 / 1440 : 𝕂) • (a * a * a * b * b * b)
  + (-6 / 1440 : 𝕂) • (a * a * b * a * a * b)
  + (-6 / 1440 : 𝕂) • (a * a * b * a * b * b)
  + (-6 / 1440 : 𝕂) • (a * a * b * b * a * b)
  + (-1 / 1440 : 𝕂) • (a * a * b * b * b * b)
  + (4 / 1440 : 𝕂) • (a * b * a * a * a * b)
  + (-6 / 1440 : 𝕂) • (a * b * a * a * b * b)
  + (24 / 1440 : 𝕂) • (a * b * a * b * a * b)
  + (4 / 1440 : 𝕂) • (a * b * a * b * b * b)
  + (-6 / 1440 : 𝕂) • (a * b * b * a * a * b)
  + (-6 / 1440 : 𝕂) • (a * b * b * a * b * b)
  + (4 / 1440 : 𝕂) • (a * b * b * b * a * b)
  + (-4 / 1440 : 𝕂) • (b * a * a * a * b * a)
  + (6 / 1440 : 𝕂) • (b * a * a * b * a * a)
  + (6 / 1440 : 𝕂) • (b * a * a * b * b * a)
  + (-4 / 1440 : 𝕂) • (b * a * b * a * a * a)
  + (-24 / 1440 : 𝕂) • (b * a * b * a * b * a)
  + (6 / 1440 : 𝕂) • (b * a * b * b * a * a)
  + (-4 / 1440 : 𝕂) • (b * a * b * b * b * a)
  + (1 / 1440 : 𝕂) • (b * b * a * a * a * a)
  + (6 / 1440 : 𝕂) • (b * b * a * a * b * a)
  + (6 / 1440 : 𝕂) • (b * b * a * b * a * a)
  + (6 / 1440 : 𝕂) • (b * b * a * b * b * a)
  + (-4 / 1440 : 𝕂) • (b * b * b * a * a * a)
  + (-4 / 1440 : 𝕂) • (b * b * b * a * b * a)
  + (1 / 1440 : 𝕂) • (b * b * b * b * a * a)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **6-fold smul-product identity**: `(c•x₁)·...·(c•x₆) = c⁶ • (x₁·...·x₆)`. -/
private lemma six_fold_smul_mul (c : 𝕂) (x₁ x₂ x₃ x₄ x₅ x₆ : 𝔸) :
    (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) * (c • x₆) =
      c ^ 6 • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1; ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Homogeneity of `bch_sextic_term`**: `Z₆(c•a, c•b) = c⁶ • Z₆(a,b)`. -/
theorem bch_sextic_term_smul (a b : 𝔸) (c : 𝕂) :
    bch_sextic_term 𝕂 (c • a) (c • b) = c ^ 6 • bch_sextic_term 𝕂 a b := by
  unfold bch_sextic_term
  simp only [six_fold_smul_mul c, smul_comm _ (c ^ 6 : 𝕂), ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Helper: a 6-letter product `x₁·x₂·x₃·x₄·x₅·x₆` with each `xᵢ ∈ {a, b}`
has norm ≤ `(‖a‖+‖b‖)⁶`. -/
private lemma norm_six_word_le {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸)
    (x₁ x₂ x₃ x₄ x₅ x₆ : 𝔸)
    (h₁ : ‖x₁‖ ≤ ‖a‖ + ‖b‖) (h₂ : ‖x₂‖ ≤ ‖a‖ + ‖b‖)
    (h₃ : ‖x₃‖ ≤ ‖a‖ + ‖b‖) (h₄ : ‖x₄‖ ≤ ‖a‖ + ‖b‖)
    (h₅ : ‖x₅‖ ≤ ‖a‖ + ‖b‖) (h₆ : ‖x₆‖ ≤ ‖a‖ + ‖b‖) :
    ‖x₁ * x₂ * x₃ * x₄ * x₅ * x₆‖ ≤ (‖a‖ + ‖b‖) ^ 6 := by
  set s := ‖a‖ + ‖b‖
  have hs_nn : 0 ≤ s := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖x₁ * x₂ * x₃ * x₄ * x₅ * x₆‖
      ≤ ‖x₁ * x₂ * x₃ * x₄ * x₅‖ * ‖x₆‖ := norm_mul_le _ _
    _ ≤ ‖x₁ * x₂ * x₃ * x₄‖ * ‖x₅‖ * ‖x₆‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ ‖x₁ * x₂ * x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ ‖x₁ * x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ ‖x₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ s * s * s * s * s * s := by gcongr
    _ = s ^ 6 := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Helper: `‖((k:𝕂)/1440) • w‖ ≤ |k|/1440·s⁶` for a 6-letter word `w`. -/
private lemma norm_sextic_word_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    (k : ℤ) (w : 𝔸) (s : ℝ) (hw : ‖w‖ ≤ s ^ 6) (hs_nn : 0 ≤ s) :
    ‖((k : 𝕂) / 1440) • w‖ ≤ |(k : ℝ)| / 1440 * s ^ 6 := by
  have h1440_norm : ‖(1440 : 𝕂)‖ = 1440 := by
    rw [show (1440 : 𝕂) = ((1440 : ℕ) : 𝕂) from by norm_cast, RCLike.norm_natCast]
    norm_num
  have hc_nn : (0 : ℝ) ≤ |(k : ℝ)| / 1440 := by positivity
  have hk_norm : ‖((k : ℤ) : 𝕂)‖ = |(k : ℝ)| := by
    rw [show ((k : ℤ) : 𝕂) = ((k : ℝ) : 𝕂) from by push_cast; rfl, RCLike.norm_ofReal]
  calc ‖((k : 𝕂) / 1440) • w‖
      ≤ ‖((k : 𝕂) / 1440)‖ * ‖w‖ := norm_smul_le _ _
    _ = |(k : ℝ)| / 1440 * ‖w‖ := by rw [norm_div, h1440_norm, hk_norm]
    _ ≤ |(k : ℝ)| / 1440 * s ^ 6 := mul_le_mul_of_nonneg_left hw hc_nn

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Norm bound for `bch_sextic_term`**: `‖Z₆(a,b)‖ ≤ (‖a‖+‖b‖)⁶`.

Sum of |numerators| over the 28 terms = 164. So `‖Z₆‖ ≤ 164/1440·s⁶ ≈ 0.114·s⁶`. -/
theorem norm_bch_sextic_term_le (a b : 𝔸) :
    ‖bch_sextic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 6 := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs6_nn : (0 : ℝ) ≤ s ^ 6 := pow_nonneg hs_nn 6
  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]
  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]
  have hw : ∀ (x₁ x₂ x₃ x₄ x₅ x₆ : 𝔸), ‖x₁‖ ≤ s → ‖x₂‖ ≤ s → ‖x₃‖ ≤ s →
      ‖x₄‖ ≤ s → ‖x₅‖ ≤ s → ‖x₆‖ ≤ s → ‖x₁ * x₂ * x₃ * x₄ * x₅ * x₆‖ ≤ s ^ 6 :=
    fun x₁ x₂ x₃ x₄ x₅ x₆ h₁ h₂ h₃ h₄ h₅ h₆ => by
      have := norm_six_word_le (𝔸 := 𝔸) a b x₁ x₂ x₃ x₄ x₅ x₆
        (by rw [hs_def] at h₁; exact h₁) (by rw [hs_def] at h₂; exact h₂)
        (by rw [hs_def] at h₃; exact h₃) (by rw [hs_def] at h₄; exact h₄)
        (by rw [hs_def] at h₅; exact h₅) (by rw [hs_def] at h₆; exact h₆)
      rw [hs_def]; exact this
  -- 28 word-norm bounds (one per word in bch_sextic_term)
  have w01 := hw a a a a b b ha_le ha_le ha_le ha_le hb_le hb_le
  have w02 := hw a a a b a b ha_le ha_le ha_le hb_le ha_le hb_le
  have w03 := hw a a a b b b ha_le ha_le ha_le hb_le hb_le hb_le
  have w04 := hw a a b a a b ha_le ha_le hb_le ha_le ha_le hb_le
  have w05 := hw a a b a b b ha_le ha_le hb_le ha_le hb_le hb_le
  have w06 := hw a a b b a b ha_le ha_le hb_le hb_le ha_le hb_le
  have w07 := hw a a b b b b ha_le ha_le hb_le hb_le hb_le hb_le
  have w08 := hw a b a a a b ha_le hb_le ha_le ha_le ha_le hb_le
  have w09 := hw a b a a b b ha_le hb_le ha_le ha_le hb_le hb_le
  have w10 := hw a b a b a b ha_le hb_le ha_le hb_le ha_le hb_le
  have w11 := hw a b a b b b ha_le hb_le ha_le hb_le hb_le hb_le
  have w12 := hw a b b a a b ha_le hb_le hb_le ha_le ha_le hb_le
  have w13 := hw a b b a b b ha_le hb_le hb_le ha_le hb_le hb_le
  have w14 := hw a b b b a b ha_le hb_le hb_le hb_le ha_le hb_le
  have w15 := hw b a a a b a hb_le ha_le ha_le ha_le hb_le ha_le
  have w16 := hw b a a b a a hb_le ha_le ha_le hb_le ha_le ha_le
  have w17 := hw b a a b b a hb_le ha_le ha_le hb_le hb_le ha_le
  have w18 := hw b a b a a a hb_le ha_le hb_le ha_le ha_le ha_le
  have w19 := hw b a b a b a hb_le ha_le hb_le ha_le hb_le ha_le
  have w20 := hw b a b b a a hb_le ha_le hb_le hb_le ha_le ha_le
  have w21 := hw b a b b b a hb_le ha_le hb_le hb_le hb_le ha_le
  have w22 := hw b b a a a a hb_le hb_le ha_le ha_le ha_le ha_le
  have w23 := hw b b a a b a hb_le hb_le ha_le ha_le hb_le ha_le
  have w24 := hw b b a b a a hb_le hb_le ha_le hb_le ha_le ha_le
  have w25 := hw b b a b b a hb_le hb_le ha_le hb_le hb_le ha_le
  have w26 := hw b b b a a a hb_le hb_le hb_le ha_le ha_le ha_le
  have w27 := hw b b b a b a hb_le hb_le hb_le ha_le hb_le ha_le
  have w28 := hw b b b b a a hb_le hb_le hb_le hb_le ha_le ha_le
  -- 28 scaled-word bounds (helper applied to each)
  have c01 : ‖((-1 : 𝕂) / 1440) • (a * a * a * a * b * b)‖ ≤ 1 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-1) _ s w01 hs_nn
    simpa [show |((-1 : ℤ) : ℝ)| = 1 from by push_cast; norm_num,
           show ((-1 : ℤ) : 𝕂) / 1440 = (-1 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c02 : ‖((4 : 𝕂) / 1440) • (a * a * a * b * a * b)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 4 _ s w02 hs_nn
    simpa [show |((4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((4 : ℤ) : 𝕂) / 1440 = (4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c03 : ‖((4 : 𝕂) / 1440) • (a * a * a * b * b * b)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 4 _ s w03 hs_nn
    simpa [show |((4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((4 : ℤ) : 𝕂) / 1440 = (4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c04 : ‖((-6 : 𝕂) / 1440) • (a * a * b * a * a * b)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-6) _ s w04 hs_nn
    simpa [show |((-6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((-6 : ℤ) : 𝕂) / 1440 = (-6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c05 : ‖((-6 : 𝕂) / 1440) • (a * a * b * a * b * b)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-6) _ s w05 hs_nn
    simpa [show |((-6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((-6 : ℤ) : 𝕂) / 1440 = (-6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c06 : ‖((-6 : 𝕂) / 1440) • (a * a * b * b * a * b)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-6) _ s w06 hs_nn
    simpa [show |((-6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((-6 : ℤ) : 𝕂) / 1440 = (-6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c07 : ‖((-1 : 𝕂) / 1440) • (a * a * b * b * b * b)‖ ≤ 1 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-1) _ s w07 hs_nn
    simpa [show |((-1 : ℤ) : ℝ)| = 1 from by push_cast; norm_num,
           show ((-1 : ℤ) : 𝕂) / 1440 = (-1 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c08 : ‖((4 : 𝕂) / 1440) • (a * b * a * a * a * b)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 4 _ s w08 hs_nn
    simpa [show |((4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((4 : ℤ) : 𝕂) / 1440 = (4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c09 : ‖((-6 : 𝕂) / 1440) • (a * b * a * a * b * b)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-6) _ s w09 hs_nn
    simpa [show |((-6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((-6 : ℤ) : 𝕂) / 1440 = (-6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c10 : ‖((24 : 𝕂) / 1440) • (a * b * a * b * a * b)‖ ≤ 24 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 24 _ s w10 hs_nn
    simpa [show |((24 : ℤ) : ℝ)| = 24 from by push_cast; norm_num,
           show ((24 : ℤ) : 𝕂) / 1440 = (24 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c11 : ‖((4 : 𝕂) / 1440) • (a * b * a * b * b * b)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 4 _ s w11 hs_nn
    simpa [show |((4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((4 : ℤ) : 𝕂) / 1440 = (4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c12 : ‖((-6 : 𝕂) / 1440) • (a * b * b * a * a * b)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-6) _ s w12 hs_nn
    simpa [show |((-6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((-6 : ℤ) : 𝕂) / 1440 = (-6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c13 : ‖((-6 : 𝕂) / 1440) • (a * b * b * a * b * b)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-6) _ s w13 hs_nn
    simpa [show |((-6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((-6 : ℤ) : 𝕂) / 1440 = (-6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c14 : ‖((4 : 𝕂) / 1440) • (a * b * b * b * a * b)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 4 _ s w14 hs_nn
    simpa [show |((4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((4 : ℤ) : 𝕂) / 1440 = (4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c15 : ‖((-4 : 𝕂) / 1440) • (b * a * a * a * b * a)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-4) _ s w15 hs_nn
    simpa [show |((-4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((-4 : ℤ) : 𝕂) / 1440 = (-4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c16 : ‖((6 : 𝕂) / 1440) • (b * a * a * b * a * a)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 6 _ s w16 hs_nn
    simpa [show |((6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((6 : ℤ) : 𝕂) / 1440 = (6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c17 : ‖((6 : 𝕂) / 1440) • (b * a * a * b * b * a)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 6 _ s w17 hs_nn
    simpa [show |((6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((6 : ℤ) : 𝕂) / 1440 = (6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c18 : ‖((-4 : 𝕂) / 1440) • (b * a * b * a * a * a)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-4) _ s w18 hs_nn
    simpa [show |((-4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((-4 : ℤ) : 𝕂) / 1440 = (-4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c19 : ‖((-24 : 𝕂) / 1440) • (b * a * b * a * b * a)‖ ≤ 24 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-24) _ s w19 hs_nn
    simpa [show |((-24 : ℤ) : ℝ)| = 24 from by push_cast; norm_num,
           show ((-24 : ℤ) : 𝕂) / 1440 = (-24 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c20 : ‖((6 : 𝕂) / 1440) • (b * a * b * b * a * a)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 6 _ s w20 hs_nn
    simpa [show |((6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((6 : ℤ) : 𝕂) / 1440 = (6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c21 : ‖((-4 : 𝕂) / 1440) • (b * a * b * b * b * a)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-4) _ s w21 hs_nn
    simpa [show |((-4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((-4 : ℤ) : 𝕂) / 1440 = (-4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c22 : ‖((1 : 𝕂) / 1440) • (b * b * a * a * a * a)‖ ≤ 1 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 1 _ s w22 hs_nn
    simpa [show |((1 : ℤ) : ℝ)| = 1 from by push_cast; norm_num,
           show ((1 : ℤ) : 𝕂) / 1440 = (1 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c23 : ‖((6 : 𝕂) / 1440) • (b * b * a * a * b * a)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 6 _ s w23 hs_nn
    simpa [show |((6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((6 : ℤ) : 𝕂) / 1440 = (6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c24 : ‖((6 : 𝕂) / 1440) • (b * b * a * b * a * a)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 6 _ s w24 hs_nn
    simpa [show |((6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((6 : ℤ) : 𝕂) / 1440 = (6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c25 : ‖((6 : 𝕂) / 1440) • (b * b * a * b * b * a)‖ ≤ 6 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 6 _ s w25 hs_nn
    simpa [show |((6 : ℤ) : ℝ)| = 6 from by push_cast; norm_num,
           show ((6 : ℤ) : 𝕂) / 1440 = (6 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c26 : ‖((-4 : 𝕂) / 1440) • (b * b * b * a * a * a)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-4) _ s w26 hs_nn
    simpa [show |((-4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((-4 : ℤ) : 𝕂) / 1440 = (-4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c27 : ‖((-4 : 𝕂) / 1440) • (b * b * b * a * b * a)‖ ≤ 4 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) (-4) _ s w27 hs_nn
    simpa [show |((-4 : ℤ) : ℝ)| = 4 from by push_cast; norm_num,
           show ((-4 : ℤ) : 𝕂) / 1440 = (-4 : 𝕂) / 1440 from by push_cast; ring]
      using this
  have c28 : ‖((1 : 𝕂) / 1440) • (b * b * b * b * a * a)‖ ≤ 1 / 1440 * s ^ 6 := by
    have := norm_sextic_word_le (𝕂 := 𝕂) 1 _ s w28 hs_nn
    simpa [show |((1 : ℤ) : ℝ)| = 1 from by push_cast; norm_num,
           show ((1 : ℤ) : 𝕂) / 1440 = (1 : 𝕂) / 1440 from by push_cast; ring]
      using this
  -- Triangle inequality across 28 terms.
  unfold bch_sextic_term
  set t1 := ((-1 : 𝕂) / 1440) • (a * a * a * a * b * b)
  set t2 := ((4 : 𝕂) / 1440) • (a * a * a * b * a * b)
  set t3 := ((4 : 𝕂) / 1440) • (a * a * a * b * b * b)
  set t4 := ((-6 : 𝕂) / 1440) • (a * a * b * a * a * b)
  set t5 := ((-6 : 𝕂) / 1440) • (a * a * b * a * b * b)
  set t6 := ((-6 : 𝕂) / 1440) • (a * a * b * b * a * b)
  set t7 := ((-1 : 𝕂) / 1440) • (a * a * b * b * b * b)
  set t8 := ((4 : 𝕂) / 1440) • (a * b * a * a * a * b)
  set t9 := ((-6 : 𝕂) / 1440) • (a * b * a * a * b * b)
  set t10 := ((24 : 𝕂) / 1440) • (a * b * a * b * a * b)
  set t11 := ((4 : 𝕂) / 1440) • (a * b * a * b * b * b)
  set t12 := ((-6 : 𝕂) / 1440) • (a * b * b * a * a * b)
  set t13 := ((-6 : 𝕂) / 1440) • (a * b * b * a * b * b)
  set t14 := ((4 : 𝕂) / 1440) • (a * b * b * b * a * b)
  set t15 := ((-4 : 𝕂) / 1440) • (b * a * a * a * b * a)
  set t16 := ((6 : 𝕂) / 1440) • (b * a * a * b * a * a)
  set t17 := ((6 : 𝕂) / 1440) • (b * a * a * b * b * a)
  set t18 := ((-4 : 𝕂) / 1440) • (b * a * b * a * a * a)
  set t19 := ((-24 : 𝕂) / 1440) • (b * a * b * a * b * a)
  set t20 := ((6 : 𝕂) / 1440) • (b * a * b * b * a * a)
  set t21 := ((-4 : 𝕂) / 1440) • (b * a * b * b * b * a)
  set t22 := ((1 : 𝕂) / 1440) • (b * b * a * a * a * a)
  set t23 := ((6 : 𝕂) / 1440) • (b * b * a * a * b * a)
  set t24 := ((6 : 𝕂) / 1440) • (b * b * a * b * a * a)
  set t25 := ((6 : 𝕂) / 1440) • (b * b * a * b * b * a)
  set t26 := ((-4 : 𝕂) / 1440) • (b * b * b * a * a * a)
  set t27 := ((-4 : 𝕂) / 1440) • (b * b * b * a * b * a)
  set t28 := ((1 : 𝕂) / 1440) • (b * b * b * b * a * a)
  have h12 := norm_add_le t1 t2
  have h123 := norm_add_le (t1+t2) t3
  have h1234 := norm_add_le (t1+t2+t3) t4
  have h12345 := norm_add_le (t1+t2+t3+t4) t5
  have h123456 := norm_add_le (t1+t2+t3+t4+t5) t6
  have h1234567 := norm_add_le (t1+t2+t3+t4+t5+t6) t7
  have h12345678 := norm_add_le (t1+t2+t3+t4+t5+t6+t7) t8
  have h12_9 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8) t9
  have h12_10 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9) t10
  have h12_11 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10) t11
  have h12_12 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11) t12
  have h12_13 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12) t13
  have h12_14 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13) t14
  have h12_15 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14) t15
  have h12_16 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15) t16
  have h12_17 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16) t17
  have h12_18 := norm_add_le (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17) t18
  have h12_19 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18) t19
  have h12_20 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19) t20
  have h12_21 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20) t21
  have h12_22 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20+t21) t22
  have h12_23 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20+t21+t22) t23
  have h12_24 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20+t21+t22+t23) t24
  have h12_25 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20+t21+t22+t23+t24) t25
  have h12_26 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20+t21+t22+t23+t24+t25)
    t26
  have h12_27 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20+t21+t22+t23+t24+t25+
      t26) t27
  have h12_28 := norm_add_le
    (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13+t14+t15+t16+t17+t18+t19+t20+t21+t22+t23+t24+t25+
      t26+t27) t28
  -- Sum of |numerators|/1440 = 164/1440 ≈ 0.1139 ≤ 1.
  linarith

/-! ### `bch_septic_term` — the τ⁷ coefficient of `bch(a, b)`

Explicit 126-term polynomial in {a, b}, derived via the CAS pipeline at
`scripts/compute_bch_septic_term.py`. Common denominator 30240; integer
numerators in {±1, ±6, ±8, ±15, ±20, ±27, ±36, ±48, ±216}.
Sum of |numerators|/30240 = 2976/30240 = 31/315 ≈ 0.0984.

This is the next term in the BCH expansion after `bch_sextic_term`:
`bch(a, b) = a + b + ½[a,b] + Z₃ + Z₄ + Z₅ + Z₆ + Z₇ + O(·^8)`.

Used in the future octic identity (stepping stone 1) for canceling deg-7
contributions to `sym_bch_cubic - sym_E₃ - sym_E₅ - sym_E₇` (the deg-9
analog of the discharged `symmetric_bch_quintic_sub_poly_axiom`). -/

/-- **τ⁷ coefficient of `bch(a, b)`** — explicit 126-term polynomial in
{a, b}. The 126 non-zero 7-letter words (out of 128 = 2⁷ possible) come
from the free Lie algebra basis at degree 7. Coefficients are rational
with LCM 30240. -/
noncomputable def bch_septic_term (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
    (1 / 30240 : 𝕂) • (a * a * a * a * a * a * b)
  + (-6 / 30240 : 𝕂) • (a * a * a * a * a * b * a)
  + (-6 / 30240 : 𝕂) • (a * a * a * a * a * b * b)
  + (15 / 30240 : 𝕂) • (a * a * a * a * b * a * a)
  + (15 / 30240 : 𝕂) • (a * a * a * a * b * a * b)
  + (15 / 30240 : 𝕂) • (a * a * a * a * b * b * a)
  + (8 / 30240 : 𝕂) • (a * a * a * a * b * b * b)
  + (-20 / 30240 : 𝕂) • (a * a * a * b * a * a * a)
  + (-6 / 30240 : 𝕂) • (a * a * a * b * a * a * b)
  + (-48 / 30240 : 𝕂) • (a * a * a * b * a * b * a)
  + (-6 / 30240 : 𝕂) • (a * a * a * b * a * b * b)
  + (-6 / 30240 : 𝕂) • (a * a * a * b * b * a * a)
  + (-6 / 30240 : 𝕂) • (a * a * a * b * b * a * b)
  + (-20 / 30240 : 𝕂) • (a * a * a * b * b * b * a)
  + (8 / 30240 : 𝕂) • (a * a * a * b * b * b * b)
  + (15 / 30240 : 𝕂) • (a * a * b * a * a * a * a)
  + (-6 / 30240 : 𝕂) • (a * a * b * a * a * a * b)
  + (36 / 30240 : 𝕂) • (a * a * b * a * a * b * a)
  + (-27 / 30240 : 𝕂) • (a * a * b * a * a * b * b)
  + (36 / 30240 : 𝕂) • (a * a * b * a * b * a * a)
  + (36 / 30240 : 𝕂) • (a * a * b * a * b * a * b)
  + (36 / 30240 : 𝕂) • (a * a * b * a * b * b * a)
  + (-6 / 30240 : 𝕂) • (a * a * b * a * b * b * b)
  + (-6 / 30240 : 𝕂) • (a * a * b * b * a * a * a)
  + (-27 / 30240 : 𝕂) • (a * a * b * b * a * a * b)
  + (36 / 30240 : 𝕂) • (a * a * b * b * a * b * a)
  + (-27 / 30240 : 𝕂) • (a * a * b * b * a * b * b)
  + (-6 / 30240 : 𝕂) • (a * a * b * b * b * a * a)
  + (-6 / 30240 : 𝕂) • (a * a * b * b * b * a * b)
  + (15 / 30240 : 𝕂) • (a * a * b * b * b * b * a)
  + (-6 / 30240 : 𝕂) • (a * a * b * b * b * b * b)
  + (-6 / 30240 : 𝕂) • (a * b * a * a * a * a * a)
  + (15 / 30240 : 𝕂) • (a * b * a * a * a * a * b)
  + (-48 / 30240 : 𝕂) • (a * b * a * a * a * b * a)
  + (-6 / 30240 : 𝕂) • (a * b * a * a * a * b * b)
  + (36 / 30240 : 𝕂) • (a * b * a * a * b * a * a)
  + (36 / 30240 : 𝕂) • (a * b * a * a * b * a * b)
  + (36 / 30240 : 𝕂) • (a * b * a * a * b * b * a)
  + (-6 / 30240 : 𝕂) • (a * b * a * a * b * b * b)
  + (-48 / 30240 : 𝕂) • (a * b * a * b * a * a * a)
  + (36 / 30240 : 𝕂) • (a * b * a * b * a * a * b)
  + (-216 / 30240 : 𝕂) • (a * b * a * b * a * b * a)
  + (36 / 30240 : 𝕂) • (a * b * a * b * a * b * b)
  + (36 / 30240 : 𝕂) • (a * b * a * b * b * a * a)
  + (36 / 30240 : 𝕂) • (a * b * a * b * b * a * b)
  + (-48 / 30240 : 𝕂) • (a * b * a * b * b * b * a)
  + (15 / 30240 : 𝕂) • (a * b * a * b * b * b * b)
  + (15 / 30240 : 𝕂) • (a * b * b * a * a * a * a)
  + (-6 / 30240 : 𝕂) • (a * b * b * a * a * a * b)
  + (36 / 30240 : 𝕂) • (a * b * b * a * a * b * a)
  + (-27 / 30240 : 𝕂) • (a * b * b * a * a * b * b)
  + (36 / 30240 : 𝕂) • (a * b * b * a * b * a * a)
  + (36 / 30240 : 𝕂) • (a * b * b * a * b * a * b)
  + (36 / 30240 : 𝕂) • (a * b * b * a * b * b * a)
  + (-6 / 30240 : 𝕂) • (a * b * b * a * b * b * b)
  + (-20 / 30240 : 𝕂) • (a * b * b * b * a * a * a)
  + (-6 / 30240 : 𝕂) • (a * b * b * b * a * a * b)
  + (-48 / 30240 : 𝕂) • (a * b * b * b * a * b * a)
  + (-6 / 30240 : 𝕂) • (a * b * b * b * a * b * b)
  + (15 / 30240 : 𝕂) • (a * b * b * b * b * a * a)
  + (15 / 30240 : 𝕂) • (a * b * b * b * b * a * b)
  + (-6 / 30240 : 𝕂) • (a * b * b * b * b * b * a)
  + (1 / 30240 : 𝕂) • (a * b * b * b * b * b * b)
  + (1 / 30240 : 𝕂) • (b * a * a * a * a * a * a)
  + (-6 / 30240 : 𝕂) • (b * a * a * a * a * a * b)
  + (15 / 30240 : 𝕂) • (b * a * a * a * a * b * a)
  + (15 / 30240 : 𝕂) • (b * a * a * a * a * b * b)
  + (-6 / 30240 : 𝕂) • (b * a * a * a * b * a * a)
  + (-48 / 30240 : 𝕂) • (b * a * a * a * b * a * b)
  + (-6 / 30240 : 𝕂) • (b * a * a * a * b * b * a)
  + (-20 / 30240 : 𝕂) • (b * a * a * a * b * b * b)
  + (-6 / 30240 : 𝕂) • (b * a * a * b * a * a * a)
  + (36 / 30240 : 𝕂) • (b * a * a * b * a * a * b)
  + (36 / 30240 : 𝕂) • (b * a * a * b * a * b * a)
  + (36 / 30240 : 𝕂) • (b * a * a * b * a * b * b)
  + (-27 / 30240 : 𝕂) • (b * a * a * b * b * a * a)
  + (36 / 30240 : 𝕂) • (b * a * a * b * b * a * b)
  + (-6 / 30240 : 𝕂) • (b * a * a * b * b * b * a)
  + (15 / 30240 : 𝕂) • (b * a * a * b * b * b * b)
  + (15 / 30240 : 𝕂) • (b * a * b * a * a * a * a)
  + (-48 / 30240 : 𝕂) • (b * a * b * a * a * a * b)
  + (36 / 30240 : 𝕂) • (b * a * b * a * a * b * a)
  + (36 / 30240 : 𝕂) • (b * a * b * a * a * b * b)
  + (36 / 30240 : 𝕂) • (b * a * b * a * b * a * a)
  + (-216 / 30240 : 𝕂) • (b * a * b * a * b * a * b)
  + (36 / 30240 : 𝕂) • (b * a * b * a * b * b * a)
  + (-48 / 30240 : 𝕂) • (b * a * b * a * b * b * b)
  + (-6 / 30240 : 𝕂) • (b * a * b * b * a * a * a)
  + (36 / 30240 : 𝕂) • (b * a * b * b * a * a * b)
  + (36 / 30240 : 𝕂) • (b * a * b * b * a * b * a)
  + (36 / 30240 : 𝕂) • (b * a * b * b * a * b * b)
  + (-6 / 30240 : 𝕂) • (b * a * b * b * b * a * a)
  + (-48 / 30240 : 𝕂) • (b * a * b * b * b * a * b)
  + (15 / 30240 : 𝕂) • (b * a * b * b * b * b * a)
  + (-6 / 30240 : 𝕂) • (b * a * b * b * b * b * b)
  + (-6 / 30240 : 𝕂) • (b * b * a * a * a * a * a)
  + (15 / 30240 : 𝕂) • (b * b * a * a * a * a * b)
  + (-6 / 30240 : 𝕂) • (b * b * a * a * a * b * a)
  + (-6 / 30240 : 𝕂) • (b * b * a * a * a * b * b)
  + (-27 / 30240 : 𝕂) • (b * b * a * a * b * a * a)
  + (36 / 30240 : 𝕂) • (b * b * a * a * b * a * b)
  + (-27 / 30240 : 𝕂) • (b * b * a * a * b * b * a)
  + (-6 / 30240 : 𝕂) • (b * b * a * a * b * b * b)
  + (-6 / 30240 : 𝕂) • (b * b * a * b * a * a * a)
  + (36 / 30240 : 𝕂) • (b * b * a * b * a * a * b)
  + (36 / 30240 : 𝕂) • (b * b * a * b * a * b * a)
  + (36 / 30240 : 𝕂) • (b * b * a * b * a * b * b)
  + (-27 / 30240 : 𝕂) • (b * b * a * b * b * a * a)
  + (36 / 30240 : 𝕂) • (b * b * a * b * b * a * b)
  + (-6 / 30240 : 𝕂) • (b * b * a * b * b * b * a)
  + (15 / 30240 : 𝕂) • (b * b * a * b * b * b * b)
  + (8 / 30240 : 𝕂) • (b * b * b * a * a * a * a)
  + (-20 / 30240 : 𝕂) • (b * b * b * a * a * a * b)
  + (-6 / 30240 : 𝕂) • (b * b * b * a * a * b * a)
  + (-6 / 30240 : 𝕂) • (b * b * b * a * a * b * b)
  + (-6 / 30240 : 𝕂) • (b * b * b * a * b * a * a)
  + (-48 / 30240 : 𝕂) • (b * b * b * a * b * a * b)
  + (-6 / 30240 : 𝕂) • (b * b * b * a * b * b * a)
  + (-20 / 30240 : 𝕂) • (b * b * b * a * b * b * b)
  + (8 / 30240 : 𝕂) • (b * b * b * b * a * a * a)
  + (15 / 30240 : 𝕂) • (b * b * b * b * a * a * b)
  + (15 / 30240 : 𝕂) • (b * b * b * b * a * b * a)
  + (15 / 30240 : 𝕂) • (b * b * b * b * a * b * b)
  + (-6 / 30240 : 𝕂) • (b * b * b * b * b * a * a)
  + (-6 / 30240 : 𝕂) • (b * b * b * b * b * a * b)
  + (1 / 30240 : 𝕂) • (b * b * b * b * b * b * a)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **7-fold smul-product identity** (local copy for use in `bch_septic_term_smul`;
the same lemma appears as `private` in `SymmetricQuintic.lean` for septic poly
infrastructure, but is unavailable upstream). -/
private lemma bch_septic_term_seven_fold_smul_mul
    (c : 𝕂) (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : 𝔸) :
    (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) * (c • x₆) * (c • x₇) =
      c ^ 7 • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
  ring_nf

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Homogeneity of `bch_septic_term`**: `Z₇(c•a, c•b) = c⁷ • Z₇(a, b)`. -/
theorem bch_septic_term_smul (a b : 𝔸) (c : 𝕂) :
    bch_septic_term 𝕂 (c • a) (c • b) = c ^ 7 • bch_septic_term 𝕂 a b := by
  unfold bch_septic_term
  simp only [bch_septic_term_seven_fold_smul_mul c, smul_comm _ (c ^ 7 : 𝕂), ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Helper (deg-7, local copy)**: `‖c • (l₁·…·l7)‖ ≤ cb · s^7` if `‖c‖ ≤ cb`
and each `‖lᵢ‖ ≤ s`. Local copy of `SymmetricQuintic.deg7_smul_word_le`
(unavailable upstream in Basic.lean). -/
private lemma deg7_smul_word_le_basic
    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)
    (l1 l2 l3 l4 l5 l6 l7 : 𝔸) (s : ℝ)
    (h1 : ‖l1‖ ≤ s) (h2 : ‖l2‖ ≤ s) (h3 : ‖l3‖ ≤ s) (h4 : ‖l4‖ ≤ s) (h5 : ‖l5‖ ≤ s) (h6 : ‖l6‖ ≤ s) (h7 : ‖l7‖ ≤ s)
    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :
    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7)‖ ≤ cb * s ^ 7 := by
  calc ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7)‖
      ≤ ‖c‖ * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖ := norm_smul_le _ _
    _ ≤ cb * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖) :=
        mul_le_mul_of_nonneg_left (norm_7prod_le _ _ _ _ _ _ _) hcb
    _ ≤ cb * (s * s * s * s * s * s * s) := by
        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr
    _ = cb * s ^ 7 := by ring

-- Per-Nat-index family of terms in `bch_septic_term a b`.
-- Defined on Nat (not Fin) so `Finset.range`-based reduction works.
set_option maxHeartbeats 1600000 in
private noncomputable def bchSepticTermN (a b : 𝔸) : Nat → 𝔸
  | 0 => (1 / 30240 : 𝕂) • (a * a * a * a * a * a * b)
  | 1 => (-6 / 30240 : 𝕂) • (a * a * a * a * a * b * a)
  | 2 => (-6 / 30240 : 𝕂) • (a * a * a * a * a * b * b)
  | 3 => (15 / 30240 : 𝕂) • (a * a * a * a * b * a * a)
  | 4 => (15 / 30240 : 𝕂) • (a * a * a * a * b * a * b)
  | 5 => (15 / 30240 : 𝕂) • (a * a * a * a * b * b * a)
  | 6 => (8 / 30240 : 𝕂) • (a * a * a * a * b * b * b)
  | 7 => (-20 / 30240 : 𝕂) • (a * a * a * b * a * a * a)
  | 8 => (-6 / 30240 : 𝕂) • (a * a * a * b * a * a * b)
  | 9 => (-48 / 30240 : 𝕂) • (a * a * a * b * a * b * a)
  | 10 => (-6 / 30240 : 𝕂) • (a * a * a * b * a * b * b)
  | 11 => (-6 / 30240 : 𝕂) • (a * a * a * b * b * a * a)
  | 12 => (-6 / 30240 : 𝕂) • (a * a * a * b * b * a * b)
  | 13 => (-20 / 30240 : 𝕂) • (a * a * a * b * b * b * a)
  | 14 => (8 / 30240 : 𝕂) • (a * a * a * b * b * b * b)
  | 15 => (15 / 30240 : 𝕂) • (a * a * b * a * a * a * a)
  | 16 => (-6 / 30240 : 𝕂) • (a * a * b * a * a * a * b)
  | 17 => (36 / 30240 : 𝕂) • (a * a * b * a * a * b * a)
  | 18 => (-27 / 30240 : 𝕂) • (a * a * b * a * a * b * b)
  | 19 => (36 / 30240 : 𝕂) • (a * a * b * a * b * a * a)
  | 20 => (36 / 30240 : 𝕂) • (a * a * b * a * b * a * b)
  | 21 => (36 / 30240 : 𝕂) • (a * a * b * a * b * b * a)
  | 22 => (-6 / 30240 : 𝕂) • (a * a * b * a * b * b * b)
  | 23 => (-6 / 30240 : 𝕂) • (a * a * b * b * a * a * a)
  | 24 => (-27 / 30240 : 𝕂) • (a * a * b * b * a * a * b)
  | 25 => (36 / 30240 : 𝕂) • (a * a * b * b * a * b * a)
  | 26 => (-27 / 30240 : 𝕂) • (a * a * b * b * a * b * b)
  | 27 => (-6 / 30240 : 𝕂) • (a * a * b * b * b * a * a)
  | 28 => (-6 / 30240 : 𝕂) • (a * a * b * b * b * a * b)
  | 29 => (15 / 30240 : 𝕂) • (a * a * b * b * b * b * a)
  | 30 => (-6 / 30240 : 𝕂) • (a * a * b * b * b * b * b)
  | 31 => (-6 / 30240 : 𝕂) • (a * b * a * a * a * a * a)
  | 32 => (15 / 30240 : 𝕂) • (a * b * a * a * a * a * b)
  | 33 => (-48 / 30240 : 𝕂) • (a * b * a * a * a * b * a)
  | 34 => (-6 / 30240 : 𝕂) • (a * b * a * a * a * b * b)
  | 35 => (36 / 30240 : 𝕂) • (a * b * a * a * b * a * a)
  | 36 => (36 / 30240 : 𝕂) • (a * b * a * a * b * a * b)
  | 37 => (36 / 30240 : 𝕂) • (a * b * a * a * b * b * a)
  | 38 => (-6 / 30240 : 𝕂) • (a * b * a * a * b * b * b)
  | 39 => (-48 / 30240 : 𝕂) • (a * b * a * b * a * a * a)
  | 40 => (36 / 30240 : 𝕂) • (a * b * a * b * a * a * b)
  | 41 => (-216 / 30240 : 𝕂) • (a * b * a * b * a * b * a)
  | 42 => (36 / 30240 : 𝕂) • (a * b * a * b * a * b * b)
  | 43 => (36 / 30240 : 𝕂) • (a * b * a * b * b * a * a)
  | 44 => (36 / 30240 : 𝕂) • (a * b * a * b * b * a * b)
  | 45 => (-48 / 30240 : 𝕂) • (a * b * a * b * b * b * a)
  | 46 => (15 / 30240 : 𝕂) • (a * b * a * b * b * b * b)
  | 47 => (15 / 30240 : 𝕂) • (a * b * b * a * a * a * a)
  | 48 => (-6 / 30240 : 𝕂) • (a * b * b * a * a * a * b)
  | 49 => (36 / 30240 : 𝕂) • (a * b * b * a * a * b * a)
  | 50 => (-27 / 30240 : 𝕂) • (a * b * b * a * a * b * b)
  | 51 => (36 / 30240 : 𝕂) • (a * b * b * a * b * a * a)
  | 52 => (36 / 30240 : 𝕂) • (a * b * b * a * b * a * b)
  | 53 => (36 / 30240 : 𝕂) • (a * b * b * a * b * b * a)
  | 54 => (-6 / 30240 : 𝕂) • (a * b * b * a * b * b * b)
  | 55 => (-20 / 30240 : 𝕂) • (a * b * b * b * a * a * a)
  | 56 => (-6 / 30240 : 𝕂) • (a * b * b * b * a * a * b)
  | 57 => (-48 / 30240 : 𝕂) • (a * b * b * b * a * b * a)
  | 58 => (-6 / 30240 : 𝕂) • (a * b * b * b * a * b * b)
  | 59 => (15 / 30240 : 𝕂) • (a * b * b * b * b * a * a)
  | 60 => (15 / 30240 : 𝕂) • (a * b * b * b * b * a * b)
  | 61 => (-6 / 30240 : 𝕂) • (a * b * b * b * b * b * a)
  | 62 => (1 / 30240 : 𝕂) • (a * b * b * b * b * b * b)
  | 63 => (1 / 30240 : 𝕂) • (b * a * a * a * a * a * a)
  | 64 => (-6 / 30240 : 𝕂) • (b * a * a * a * a * a * b)
  | 65 => (15 / 30240 : 𝕂) • (b * a * a * a * a * b * a)
  | 66 => (15 / 30240 : 𝕂) • (b * a * a * a * a * b * b)
  | 67 => (-6 / 30240 : 𝕂) • (b * a * a * a * b * a * a)
  | 68 => (-48 / 30240 : 𝕂) • (b * a * a * a * b * a * b)
  | 69 => (-6 / 30240 : 𝕂) • (b * a * a * a * b * b * a)
  | 70 => (-20 / 30240 : 𝕂) • (b * a * a * a * b * b * b)
  | 71 => (-6 / 30240 : 𝕂) • (b * a * a * b * a * a * a)
  | 72 => (36 / 30240 : 𝕂) • (b * a * a * b * a * a * b)
  | 73 => (36 / 30240 : 𝕂) • (b * a * a * b * a * b * a)
  | 74 => (36 / 30240 : 𝕂) • (b * a * a * b * a * b * b)
  | 75 => (-27 / 30240 : 𝕂) • (b * a * a * b * b * a * a)
  | 76 => (36 / 30240 : 𝕂) • (b * a * a * b * b * a * b)
  | 77 => (-6 / 30240 : 𝕂) • (b * a * a * b * b * b * a)
  | 78 => (15 / 30240 : 𝕂) • (b * a * a * b * b * b * b)
  | 79 => (15 / 30240 : 𝕂) • (b * a * b * a * a * a * a)
  | 80 => (-48 / 30240 : 𝕂) • (b * a * b * a * a * a * b)
  | 81 => (36 / 30240 : 𝕂) • (b * a * b * a * a * b * a)
  | 82 => (36 / 30240 : 𝕂) • (b * a * b * a * a * b * b)
  | 83 => (36 / 30240 : 𝕂) • (b * a * b * a * b * a * a)
  | 84 => (-216 / 30240 : 𝕂) • (b * a * b * a * b * a * b)
  | 85 => (36 / 30240 : 𝕂) • (b * a * b * a * b * b * a)
  | 86 => (-48 / 30240 : 𝕂) • (b * a * b * a * b * b * b)
  | 87 => (-6 / 30240 : 𝕂) • (b * a * b * b * a * a * a)
  | 88 => (36 / 30240 : 𝕂) • (b * a * b * b * a * a * b)
  | 89 => (36 / 30240 : 𝕂) • (b * a * b * b * a * b * a)
  | 90 => (36 / 30240 : 𝕂) • (b * a * b * b * a * b * b)
  | 91 => (-6 / 30240 : 𝕂) • (b * a * b * b * b * a * a)
  | 92 => (-48 / 30240 : 𝕂) • (b * a * b * b * b * a * b)
  | 93 => (15 / 30240 : 𝕂) • (b * a * b * b * b * b * a)
  | 94 => (-6 / 30240 : 𝕂) • (b * a * b * b * b * b * b)
  | 95 => (-6 / 30240 : 𝕂) • (b * b * a * a * a * a * a)
  | 96 => (15 / 30240 : 𝕂) • (b * b * a * a * a * a * b)
  | 97 => (-6 / 30240 : 𝕂) • (b * b * a * a * a * b * a)
  | 98 => (-6 / 30240 : 𝕂) • (b * b * a * a * a * b * b)
  | 99 => (-27 / 30240 : 𝕂) • (b * b * a * a * b * a * a)
  | 100 => (36 / 30240 : 𝕂) • (b * b * a * a * b * a * b)
  | 101 => (-27 / 30240 : 𝕂) • (b * b * a * a * b * b * a)
  | 102 => (-6 / 30240 : 𝕂) • (b * b * a * a * b * b * b)
  | 103 => (-6 / 30240 : 𝕂) • (b * b * a * b * a * a * a)
  | 104 => (36 / 30240 : 𝕂) • (b * b * a * b * a * a * b)
  | 105 => (36 / 30240 : 𝕂) • (b * b * a * b * a * b * a)
  | 106 => (36 / 30240 : 𝕂) • (b * b * a * b * a * b * b)
  | 107 => (-27 / 30240 : 𝕂) • (b * b * a * b * b * a * a)
  | 108 => (36 / 30240 : 𝕂) • (b * b * a * b * b * a * b)
  | 109 => (-6 / 30240 : 𝕂) • (b * b * a * b * b * b * a)
  | 110 => (15 / 30240 : 𝕂) • (b * b * a * b * b * b * b)
  | 111 => (8 / 30240 : 𝕂) • (b * b * b * a * a * a * a)
  | 112 => (-20 / 30240 : 𝕂) • (b * b * b * a * a * a * b)
  | 113 => (-6 / 30240 : 𝕂) • (b * b * b * a * a * b * a)
  | 114 => (-6 / 30240 : 𝕂) • (b * b * b * a * a * b * b)
  | 115 => (-6 / 30240 : 𝕂) • (b * b * b * a * b * a * a)
  | 116 => (-48 / 30240 : 𝕂) • (b * b * b * a * b * a * b)
  | 117 => (-6 / 30240 : 𝕂) • (b * b * b * a * b * b * a)
  | 118 => (-20 / 30240 : 𝕂) • (b * b * b * a * b * b * b)
  | 119 => (8 / 30240 : 𝕂) • (b * b * b * b * a * a * a)
  | 120 => (15 / 30240 : 𝕂) • (b * b * b * b * a * a * b)
  | 121 => (15 / 30240 : 𝕂) • (b * b * b * b * a * b * a)
  | 122 => (15 / 30240 : 𝕂) • (b * b * b * b * a * b * b)
  | 123 => (-6 / 30240 : 𝕂) • (b * b * b * b * b * a * a)
  | 124 => (-6 / 30240 : 𝕂) • (b * b * b * b * b * a * b)
  | 125 => (1 / 30240 : 𝕂) • (b * b * b * b * b * b * a)
  | _ => 0

/-- `Fin 126`-indexed wrapper around `bchSepticTermN`. -/
private noncomputable def bchSepticTerm (a b : 𝔸) (i : Fin 126) : 𝔸 :=
  bchSepticTermN (𝕂 := 𝕂) a b i.val

-- `bch_septic_term` equals the `Finset.sum` over `Fin 126` of
-- `bchSepticTerm`. Used in the norm bound via `norm_sum_le`.
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 2000 in
private theorem bch_septic_term_eq_sum (a b : 𝔸) :
    bch_septic_term 𝕂 a b = ∑ i : Fin 126, bchSepticTerm (𝕂 := 𝕂) a b i := by
  unfold bch_septic_term bchSepticTerm
  rw [Fin.sum_univ_eq_sum_range (fun k => bchSepticTermN (𝕂 := 𝕂) a b k)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bchSepticTermN, zero_add]
  try abel

-- Per-index norm bound: `‖bchSepticTerm a b i‖ ≤ (216/30240) · s^7`
-- (uniform: 216 is the max `|scaled_num|` over all 126 entries).
set_option maxHeartbeats 32000000 in
private lemma bchSepticTerm_norm_le (a b : 𝔸) (s : ℝ)
    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :
    ∀ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) a b i‖ ≤ (216 / 30240 : ℝ) * s^7 := fun i =>
  match i with
  | ⟨0, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (a * a * a * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a a a b s ha ha ha ha ha ha hb (by norm_num) hs
  | ⟨1, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * a * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a a b a s ha ha ha ha ha hb ha (by norm_num) hs
  | ⟨2, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * a * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a a b b s ha ha ha ha ha hb hb (by norm_num) hs
  | ⟨3, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * a * a * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b a a s ha ha ha ha hb ha ha (by norm_num) hs
  | ⟨4, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * a * a * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b a b s ha ha ha ha hb ha hb (by norm_num) hs
  | ⟨5, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * a * a * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b b a s ha ha ha ha hb hb ha (by norm_num) hs
  | ⟨6, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (a * a * a * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b b b s ha ha ha ha hb hb hb (by norm_num) hs
  | ⟨7, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (a * a * a * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a a a s ha ha ha hb ha ha ha (by norm_num) hs
  | ⟨8, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * a * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a a b s ha ha ha hb ha ha hb (by norm_num) hs
  | ⟨9, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (a * a * a * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a b a s ha ha ha hb ha hb ha (by norm_num) hs
  | ⟨10, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * a * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a b b s ha ha ha hb ha hb hb (by norm_num) hs
  | ⟨11, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * a * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b a a s ha ha ha hb hb ha ha (by norm_num) hs
  | ⟨12, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * a * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b a b s ha ha ha hb hb ha hb (by norm_num) hs
  | ⟨13, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (a * a * a * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b b a s ha ha ha hb hb hb ha (by norm_num) hs
  | ⟨14, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (a * a * a * b * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b b b s ha ha ha hb hb hb hb (by norm_num) hs
  | ⟨15, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * a * b * a * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a a a s ha ha hb ha ha ha ha (by norm_num) hs
  | ⟨16, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * b * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a a b s ha ha hb ha ha ha hb (by norm_num) hs
  | ⟨17, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * a * b * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a b a s ha ha hb ha ha hb ha (by norm_num) hs
  | ⟨18, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (a * a * b * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a b b s ha ha hb ha ha hb hb (by norm_num) hs
  | ⟨19, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * a * b * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b a a s ha ha hb ha hb ha ha (by norm_num) hs
  | ⟨20, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * a * b * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b a b s ha ha hb ha hb ha hb (by norm_num) hs
  | ⟨21, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * a * b * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b b a s ha ha hb ha hb hb ha (by norm_num) hs
  | ⟨22, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * b * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b b b s ha ha hb ha hb hb hb (by norm_num) hs
  | ⟨23, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * b * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a a a s ha ha hb hb ha ha ha (by norm_num) hs
  | ⟨24, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (a * a * b * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a a b s ha ha hb hb ha ha hb (by norm_num) hs
  | ⟨25, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * a * b * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a b a s ha ha hb hb ha hb ha (by norm_num) hs
  | ⟨26, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (a * a * b * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a b b s ha ha hb hb ha hb hb (by norm_num) hs
  | ⟨27, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * b * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b a a s ha ha hb hb hb ha ha (by norm_num) hs
  | ⟨28, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * b * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b a b s ha ha hb hb hb ha hb (by norm_num) hs
  | ⟨29, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * a * b * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b b a s ha ha hb hb hb hb ha (by norm_num) hs
  | ⟨30, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * a * b * b * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b b b s ha ha hb hb hb hb hb (by norm_num) hs
  | ⟨31, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * a * a * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a a a s ha hb ha ha ha ha ha (by norm_num) hs
  | ⟨32, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * b * a * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a a b s ha hb ha ha ha ha hb (by norm_num) hs
  | ⟨33, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (a * b * a * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a b a s ha hb ha ha ha hb ha (by norm_num) hs
  | ⟨34, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * a * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a b b s ha hb ha ha ha hb hb (by norm_num) hs
  | ⟨35, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * a * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b a a s ha hb ha ha hb ha ha (by norm_num) hs
  | ⟨36, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * a * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b a b s ha hb ha ha hb ha hb (by norm_num) hs
  | ⟨37, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * a * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b b a s ha hb ha ha hb hb ha (by norm_num) hs
  | ⟨38, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * a * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b b b s ha hb ha ha hb hb hb (by norm_num) hs
  | ⟨39, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (a * b * a * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a a a s ha hb ha hb ha ha ha (by norm_num) hs
  | ⟨40, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * a * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a a b s ha hb ha hb ha ha hb (by norm_num) hs
  | ⟨41, _⟩ =>
    show ‖(-216 / 30240 : 𝕂) • (a * b * a * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-216 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a b a s ha hb ha hb ha hb ha (by norm_num) hs
  | ⟨42, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * a * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a b b s ha hb ha hb ha hb hb (by norm_num) hs
  | ⟨43, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * a * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b a a s ha hb ha hb hb ha ha (by norm_num) hs
  | ⟨44, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * a * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b a b s ha hb ha hb hb ha hb (by norm_num) hs
  | ⟨45, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (a * b * a * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b b a s ha hb ha hb hb hb ha (by norm_num) hs
  | ⟨46, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * b * a * b * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b b b s ha hb ha hb hb hb hb (by norm_num) hs
  | ⟨47, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * b * b * a * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a a a s ha hb hb ha ha ha ha (by norm_num) hs
  | ⟨48, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * b * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a a b s ha hb hb ha ha ha hb (by norm_num) hs
  | ⟨49, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * b * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a b a s ha hb hb ha ha hb ha (by norm_num) hs
  | ⟨50, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (a * b * b * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a b b s ha hb hb ha ha hb hb (by norm_num) hs
  | ⟨51, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * b * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b a a s ha hb hb ha hb ha ha (by norm_num) hs
  | ⟨52, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * b * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b a b s ha hb hb ha hb ha hb (by norm_num) hs
  | ⟨53, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (a * b * b * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b b a s ha hb hb ha hb hb ha (by norm_num) hs
  | ⟨54, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * b * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b b b s ha hb hb ha hb hb hb (by norm_num) hs
  | ⟨55, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (a * b * b * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a a a s ha hb hb hb ha ha ha (by norm_num) hs
  | ⟨56, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * b * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a a b s ha hb hb hb ha ha hb (by norm_num) hs
  | ⟨57, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (a * b * b * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a b a s ha hb hb hb ha hb ha (by norm_num) hs
  | ⟨58, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * b * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a b b s ha hb hb hb ha hb hb (by norm_num) hs
  | ⟨59, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * b * b * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b b a a s ha hb hb hb hb ha ha (by norm_num) hs
  | ⟨60, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (a * b * b * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b b a b s ha hb hb hb hb ha hb (by norm_num) hs
  | ⟨61, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (a * b * b * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b b b a s ha hb hb hb hb hb ha (by norm_num) hs
  | ⟨62, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (a * b * b * b * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b b b b s ha hb hb hb hb hb hb (by norm_num) hs
  | ⟨63, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (b * a * a * a * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a a a a s hb ha ha ha ha ha ha (by norm_num) hs
  | ⟨64, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * a * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a a a b s hb ha ha ha ha ha hb (by norm_num) hs
  | ⟨65, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * a * a * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a a b a s hb ha ha ha ha hb ha (by norm_num) hs
  | ⟨66, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * a * a * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a a b b s hb ha ha ha ha hb hb (by norm_num) hs
  | ⟨67, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * a * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b a a s hb ha ha ha hb ha ha (by norm_num) hs
  | ⟨68, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (b * a * a * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b a b s hb ha ha ha hb ha hb (by norm_num) hs
  | ⟨69, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * a * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b b a s hb ha ha ha hb hb ha (by norm_num) hs
  | ⟨70, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (b * a * a * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b b b s hb ha ha ha hb hb hb (by norm_num) hs
  | ⟨71, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * a * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a a a s hb ha ha hb ha ha ha (by norm_num) hs
  | ⟨72, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * a * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a a b s hb ha ha hb ha ha hb (by norm_num) hs
  | ⟨73, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * a * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a b a s hb ha ha hb ha hb ha (by norm_num) hs
  | ⟨74, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * a * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a b b s hb ha ha hb ha hb hb (by norm_num) hs
  | ⟨75, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (b * a * a * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b a a s hb ha ha hb hb ha ha (by norm_num) hs
  | ⟨76, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * a * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b a b s hb ha ha hb hb ha hb (by norm_num) hs
  | ⟨77, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * a * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b b a s hb ha ha hb hb hb ha (by norm_num) hs
  | ⟨78, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * a * a * b * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b b b s hb ha ha hb hb hb hb (by norm_num) hs
  | ⟨79, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * a * b * a * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a a a s hb ha hb ha ha ha ha (by norm_num) hs
  | ⟨80, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (b * a * b * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a a b s hb ha hb ha ha ha hb (by norm_num) hs
  | ⟨81, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * b * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a b a s hb ha hb ha ha hb ha (by norm_num) hs
  | ⟨82, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * b * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a b b s hb ha hb ha ha hb hb (by norm_num) hs
  | ⟨83, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * b * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b a a s hb ha hb ha hb ha ha (by norm_num) hs
  | ⟨84, _⟩ =>
    show ‖(-216 / 30240 : 𝕂) • (b * a * b * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-216 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b a b s hb ha hb ha hb ha hb (by norm_num) hs
  | ⟨85, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * b * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b b a s hb ha hb ha hb hb ha (by norm_num) hs
  | ⟨86, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (b * a * b * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b b b s hb ha hb ha hb hb hb (by norm_num) hs
  | ⟨87, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * b * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a a a s hb ha hb hb ha ha ha (by norm_num) hs
  | ⟨88, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * b * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a a b s hb ha hb hb ha ha hb (by norm_num) hs
  | ⟨89, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * b * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a b a s hb ha hb hb ha hb ha (by norm_num) hs
  | ⟨90, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * a * b * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a b b s hb ha hb hb ha hb hb (by norm_num) hs
  | ⟨91, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * b * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b a a s hb ha hb hb hb ha ha (by norm_num) hs
  | ⟨92, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (b * a * b * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b a b s hb ha hb hb hb ha hb (by norm_num) hs
  | ⟨93, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * a * b * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b b a s hb ha hb hb hb hb ha (by norm_num) hs
  | ⟨94, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * a * b * b * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b b b s hb ha hb hb hb hb hb (by norm_num) hs
  | ⟨95, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * a * a * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a a a s hb hb ha ha ha ha ha (by norm_num) hs
  | ⟨96, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * b * a * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a a b s hb hb ha ha ha ha hb (by norm_num) hs
  | ⟨97, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * a * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a b a s hb hb ha ha ha hb ha (by norm_num) hs
  | ⟨98, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * a * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a b b s hb hb ha ha ha hb hb (by norm_num) hs
  | ⟨99, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (b * b * a * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b a a s hb hb ha ha hb ha ha (by norm_num) hs
  | ⟨100, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * b * a * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b a b s hb hb ha ha hb ha hb (by norm_num) hs
  | ⟨101, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (b * b * a * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b b a s hb hb ha ha hb hb ha (by norm_num) hs
  | ⟨102, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * a * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b b b s hb hb ha ha hb hb hb (by norm_num) hs
  | ⟨103, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * a * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a a a s hb hb ha hb ha ha ha (by norm_num) hs
  | ⟨104, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * b * a * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a a b s hb hb ha hb ha ha hb (by norm_num) hs
  | ⟨105, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * b * a * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a b a s hb hb ha hb ha hb ha (by norm_num) hs
  | ⟨106, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * b * a * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a b b s hb hb ha hb ha hb hb (by norm_num) hs
  | ⟨107, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (b * b * a * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b a a s hb hb ha hb hb ha ha (by norm_num) hs
  | ⟨108, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (b * b * a * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b a b s hb hb ha hb hb ha hb (by norm_num) hs
  | ⟨109, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * a * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b b a s hb hb ha hb hb hb ha (by norm_num) hs
  | ⟨110, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * b * a * b * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b b b s hb hb ha hb hb hb hb (by norm_num) hs
  | ⟨111, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (b * b * b * a * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a a a s hb hb hb ha ha ha ha (by norm_num) hs
  | ⟨112, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (b * b * b * a * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a a b s hb hb hb ha ha ha hb (by norm_num) hs
  | ⟨113, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * b * a * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a b a s hb hb hb ha ha hb ha (by norm_num) hs
  | ⟨114, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * b * a * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a b b s hb hb hb ha ha hb hb (by norm_num) hs
  | ⟨115, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * b * a * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b a a s hb hb hb ha hb ha ha (by norm_num) hs
  | ⟨116, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (b * b * b * a * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b a b s hb hb hb ha hb ha hb (by norm_num) hs
  | ⟨117, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * b * a * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b b a s hb hb hb ha hb hb ha (by norm_num) hs
  | ⟨118, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (b * b * b * a * b * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b b b s hb hb hb ha hb hb hb (by norm_num) hs
  | ⟨119, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (b * b * b * b * a * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a a a s hb hb hb hb ha ha ha (by norm_num) hs
  | ⟨120, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * b * b * b * a * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a a b s hb hb hb hb ha ha hb (by norm_num) hs
  | ⟨121, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * b * b * b * a * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a b a s hb hb hb hb ha hb ha (by norm_num) hs
  | ⟨122, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (b * b * b * b * a * b * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a b b s hb hb hb hb ha hb hb (by norm_num) hs
  | ⟨123, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * b * b * b * a * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b b a a s hb hb hb hb hb ha ha (by norm_num) hs
  | ⟨124, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (b * b * b * b * b * a * b)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b b a b s hb hb hb hb hb ha hb (by norm_num) hs
  | ⟨125, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (b * b * b * b * b * b * a)‖ ≤ (216 / 30240 : ℝ) * s^7 from
      deg7_smul_word_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b b b a s hb hb hb hb hb hb ha (by norm_num) hs
  | ⟨_ + 126, h⟩ => absurd h (by omega)

set_option maxHeartbeats 800000 in
/-- **Norm bound for `bch_septic_term`**: `‖Z₇(a, b)‖ ≤ (‖a‖+‖b‖)⁷`.

The actual Σ|coef|/30240 = 2976/30240 = 31/315 ≈ 0.098413 (tight).
The proof uses a uniform per-i bound `216/30240` (max |scaled coef|),
giving `Σ ≤ 126·216/30240 = 27216/30240 = 9/10 ≤ 1`. -/
theorem norm_bch_septic_term_le (a b : 𝔸) :
    ‖bch_septic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]
  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]
  have hs7_nn : 0 ≤ s ^ 7 := pow_nonneg hs_nn 7
  rw [bch_septic_term_eq_sum]
  calc ‖∑ i : Fin 126, bchSepticTerm (𝕂 := 𝕂) a b i‖
      ≤ ∑ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 126, (216 / 30240 : ℝ) * s^7 :=
        Finset.sum_le_sum (fun i _ => bchSepticTerm_norm_le (𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)
    _ = 126 * ((216 / 30240 : ℝ) * s^7) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ 1 * s^7 := by nlinarith [hs7_nn]
    _ = s ^ 7 := one_mul _

/-! ## Vanishing of `bch_septic_term` on `(α•V, β•V)`

Since `bch(α•V, β•V) = log(exp(α•V)·exp(β•V)) = (α+β)•V` for any
`α, β : 𝕂` (all commutators `[V, V]` vanish), every τ⁷ Taylor
coefficient of bch at pure-V inputs must vanish:

  `bch_septic_term 𝕂 (α • V) (β • V) = 0`.

Analog of `SymmetricQuintic.symmetric_bch_septic_poly_apply_smul_smul`
for the (non-palindromic) bch deg-7 coefficient. Foundation for the
future `octic_pure_identity` (deg-7 cancellation algebraic identity at
substituted polynomials, the deg-9 analog of `septic_pure_identity`). -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **7-fold smul-mul absorption (single element)** (local copy):
7 factors each of the form `sᵢ • V` collapse to `(s₁·…·s₇) • V⁷`.
The same lemma exists as `private` in `SymmetricQuintic.lean`; this
copy is needed for use in `bch_septic_term_apply_smul_smul`. -/
private lemma bch_septic_term_seven_fold_smul_mul_eq (V : 𝔸)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ : 𝕂) :
    (s₁ • V) * (s₂ • V) * (s₃ • V) * (s₄ • V) * (s₅ • V) * (s₆ • V) * (s₇ • V) =
      (s₁ * s₂ * s₃ * s₄ * s₅ * s₆ * s₇) • (V * V * V * V * V * V * V) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1; ring

set_option maxHeartbeats 4000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Vanishing on scalar•V inputs**:
`bch_septic_term 𝕂 (α • V) (β • V) = 0` for any `α, β : 𝕂` and `V : 𝔸`.

Source: `log(exp(αV)·exp(βV)) = (α+β)V` (V commutes with itself), so all
deg-7 Taylor content must vanish identically as a polynomial in (α, β).

Proof template mirrors `symmetric_bch_septic_poly_apply_smul_smul`:
1. Collapse each 7-fold product `(αV)^k·(βV)^(7−k)` to `(α^k·β^(7−k)) • V⁷`.
2. Combine the 126 word coefficients into a single polynomial in (α, β)
   times `V⁷`.
3. The polynomial-in-(α, β) identity (each `(k, 7−k)` partial sum is 0)
   is closed by `ring`. -/
theorem bch_septic_term_apply_smul_smul (V : 𝔸) (α β : 𝕂) :
    bch_septic_term 𝕂 (α • V) (β • V) = 0 := by
  unfold bch_septic_term
  -- Step 1: collapse each 7-fold product to (scalar) • V⁷; combine outer scalars.
  simp only [bch_septic_term_seven_fold_smul_mul_eq, smul_smul, ← add_smul]
  -- Step 2: goal is now `(big_polynomial in α, β) • V⁷ = 0`.
  conv_rhs => rw [show (0 : 𝔸) = (0 : 𝕂) • (V * V * V * V * V * V * V) from
    (zero_smul _ _).symm]
  congr 1
  -- Polynomial-in-(α, β) identity: each (k, 7−k) coefficient group sums to 0.
  ring

/-! ### Lipschitz bound for `bch_septic_term`

Analog of `norm_bch_sextic_term_diff_le` at one degree higher; deg-7 BCH
coefficient is Lipschitz in its first argument with prefactor `7·M⁶`.

Foundation for stepping stone 1 (`symmetric_bch_septic_sub_poly_axiom`
discharge): with `z = (a'+b) + W` and `‖W‖ = O(s²)`, gives an
O(s⁸·‖W‖) bound on `‖Z₇(z, y) − Z₇(a'+b, y)‖`. -/

set_option maxHeartbeats 1600000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **7-letter product Lipschitz** (local copy):
`‖x₁·…·x₇ − y₁·…·y₇‖ ≤ N⁶·Σᵢ ‖xᵢ−yᵢ‖` when `‖xᵢ‖, ‖yᵢ‖ ≤ N`.
Local copy of `SymmetricQuintic.word_7_diff_le` (unavailable upstream). -/
private lemma word_7_diff_le_basic
    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : 𝔸) (N : ℝ)
    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)
    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N)
    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)
    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N) (hN_nn : 0 ≤ N) :
    ‖x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇‖ ≤
      N ^ 6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) := by
  have hid : x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ =
      (x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ +
      y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ +
      y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ +
      y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ +
      y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ +
      y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ +
      y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) := by noncomm_ring
  rw [hid]
  have hN_pow_nn : (0 : ℝ) ≤ N ^ 6 := pow_nonneg hN_nn 6
  have ht₁ : ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₁ - y₁‖ := by
    calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇‖
        ≤ ‖x₁ - y₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _
      _ ≤ ‖x₁ - y₁‖ * N * N * N * N * N * N := by gcongr
      _ = N ^ 6 * ‖x₁ - y₁‖ := by ring
  have ht₂ : ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₂ - y₂‖ := by
    calc ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇‖
        ≤ ‖y₁‖ * ‖x₂ - y₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _
      _ ≤ N * ‖x₂ - y₂‖ * N * N * N * N * N := by gcongr
      _ = N ^ 6 * ‖x₂ - y₂‖ := by ring
  have ht₃ : ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₃ - y₃‖ := by
    calc ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖x₃ - y₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _
      _ ≤ N * N * ‖x₃ - y₃‖ * N * N * N * N := by gcongr
      _ = N ^ 6 * ‖x₃ - y₃‖ := by ring
  have ht₄ : ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₄ - y₄‖ := by
    calc ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖x₄ - y₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _
      _ ≤ N * N * N * ‖x₄ - y₄‖ * N * N * N := by gcongr
      _ = N ^ 6 * ‖x₄ - y₄‖ := by ring
  have ht₅ : ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇‖ ≤ N ^ 6 * ‖x₅ - y₅‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖x₅ - y₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _
      _ ≤ N * N * N * N * ‖x₅ - y₅‖ * N * N := by gcongr
      _ = N ^ 6 * ‖x₅ - y₅‖ := by ring
  have ht₆ : ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇‖ ≤ N ^ 6 * ‖x₆ - y₆‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖y₅‖ * ‖x₆ - y₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _
      _ ≤ N * N * N * N * N * ‖x₆ - y₆‖ * N := by gcongr
      _ = N ^ 6 * ‖x₆ - y₆‖ := by ring
  have ht₇ : ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖ ≤ N ^ 6 * ‖x₇ - y₇‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖y₅‖ * ‖y₆‖ * ‖x₇ - y₇‖ := norm_7prod_le _ _ _ _ _ _ _
      _ ≤ N * N * N * N * N * N * ‖x₇ - y₇‖ := by gcongr
      _ = N ^ 6 * ‖x₇ - y₇‖ := by ring
  calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ +
        y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ +
        y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ +
        y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ +
        y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ +
        y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ +
        y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖
      ≤ ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇‖ +
          ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇‖ +
          ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇‖ +
          ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇‖ +
          ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇‖ +
          ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇‖ +
          ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖ := by
        have a1 := norm_add_le
              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ + y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇)
              (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇))
        have a2 := norm_add_le
              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇)
              (y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇)
        have a3 := norm_add_le
              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇)
              (y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇)
        have a4 := norm_add_le
              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇)
              (y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇)
        have a5 := norm_add_le
              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇)
              (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇)
        have a6 := norm_add_le
              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇)
              (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇)
        linarith
    _ ≤ N ^ 6 * ‖x₁ - y₁‖ + N ^ 6 * ‖x₂ - y₂‖ + N ^ 6 * ‖x₃ - y₃‖ + N ^ 6 * ‖x₄ - y₄‖ + N ^ 6 * ‖x₅ - y₅‖ + N ^ 6 * ‖x₆ - y₆‖ + N ^ 6 * ‖x₇ - y₇‖ := by
        linarith [ht₁, ht₂, ht₃, ht₄, ht₅, ht₆, ht₇]
    _ = N ^ 6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Scaled 7-letter Lipschitz** (local copy):
`‖c•(x₁·…·x₇) − c•(y₁·…·y₇)‖ ≤ cb·7·N⁶·D` when `‖c‖ ≤ cb`,
`‖xᵢ‖, ‖yᵢ‖ ≤ N`, and `‖xᵢ − yᵢ‖ ≤ D`.
Local copy of `SymmetricQuintic.deg7_smul_word_diff_le`. -/
private lemma deg7_smul_word_diff_le_basic
    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)
    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : 𝔸) (N D : ℝ)
    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)
    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N)
    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)
    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N)
    (hd₁ : ‖x₁ - y₁‖ ≤ D) (hd₂ : ‖x₂ - y₂‖ ≤ D) (hd₃ : ‖x₃ - y₃‖ ≤ D)
    (hd₄ : ‖x₄ - y₄‖ ≤ D) (hd₅ : ‖x₅ - y₅‖ ≤ D) (hd₆ : ‖x₆ - y₆‖ ≤ D) (hd₇ : ‖x₇ - y₇‖ ≤ D)
    (hcb : 0 ≤ cb) (hN_nn : 0 ≤ N) (hD_nn : 0 ≤ D) :
    ‖c • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇) - c • (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇)‖ ≤
      cb * 7 * N^6 * D := by
  rw [← smul_sub]
  have hwd : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ ≤
             N^6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) :=
    word_7_diff_le_basic x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ hx₇ hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hy₇ hN_nn
  have hwd_bound : N^6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) ≤
             7 * N^6 * D := by
    have hN6_nn : 0 ≤ N^6 := pow_nonneg hN_nn 6
    nlinarith [hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇, hN6_nn]
  have hwd2 : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ ≤ 7 * N^6 * D := le_trans hwd hwd_bound
  have h_pos : 0 ≤ 7 * N^6 * D := by positivity
  calc ‖c • (x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇)‖
      ≤ ‖c‖ * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ := norm_smul_le _ _
    _ ≤ cb * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * (7 * N^6 * D) := mul_le_mul_of_nonneg_left hwd2 hcb
    _ = cb * 7 * N^6 * D := by ring

-- Per-i diff bound: `‖bchSepticTerm z y i − bchSepticTerm x y i‖ ≤ (216/30240) · 7 · M⁶ · ‖z−x‖`
-- (uniform over all 126 indices, since each word has ≤ 7 'a'-positions).
set_option maxHeartbeats 64000000 in
private lemma bchSepticTerm_diff_norm_le (z x y : 𝔸) (M : ℝ)
    (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM_nn : 0 ≤ M) :
    ∀ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) z y i -
                     bchSepticTerm (𝕂 := 𝕂) x y i‖ ≤
      (216 / 30240 : ℝ) * 7 * M^6 * ‖z - x‖ := by
  intro i
  set D := ‖z - x‖ with hD_def
  have hD_nn : 0 ≤ D := norm_nonneg _
  have hzx_le_D : ‖z - x‖ ≤ D := le_refl _
  have hyy_le_D : ‖y - y‖ ≤ D := by rw [sub_self, norm_zero]; exact hD_nn
  match i with
  | ⟨0, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (z * z * z * z * z * z * y) - (1 / 30240 : 𝕂) • (x * x * x * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z z z y
        x x x x x x y
        M D
        hz hz hz hz hz hz hy
        hx hx hx hx hx hx hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨1, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * z * z * z * y * z) - (-6 / 30240 : 𝕂) • (x * x * x * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z z y z
        x x x x x y x
        M D
        hz hz hz hz hz hy hz
        hx hx hx hx hx hy hx
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨2, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * z * z * z * y * y) - (-6 / 30240 : 𝕂) • (x * x * x * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z z y y
        x x x x x y y
        M D
        hz hz hz hz hz hy hy
        hx hx hx hx hx hy hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨3, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * z * z * z * y * z * z) - (15 / 30240 : 𝕂) • (x * x * x * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y z z
        x x x x y x x
        M D
        hz hz hz hz hy hz hz
        hx hx hx hx hy hx hx
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨4, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * z * z * z * y * z * y) - (15 / 30240 : 𝕂) • (x * x * x * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y z y
        x x x x y x y
        M D
        hz hz hz hz hy hz hy
        hx hx hx hx hy hx hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨5, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * z * z * z * y * y * z) - (15 / 30240 : 𝕂) • (x * x * x * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y y z
        x x x x y y x
        M D
        hz hz hz hz hy hy hz
        hx hx hx hx hy hy hx
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨6, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (z * z * z * z * y * y * y) - (8 / 30240 : 𝕂) • (x * x * x * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y y y
        x x x x y y y
        M D
        hz hz hz hz hy hy hy
        hx hx hx hx hy hy hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨7, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (z * z * z * y * z * z * z) - (-20 / 30240 : 𝕂) • (x * x * x * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z z z
        x x x y x x x
        M D
        hz hz hz hy hz hz hz
        hx hx hx hy hx hx hx
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨8, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * z * y * z * z * y) - (-6 / 30240 : 𝕂) • (x * x * x * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z z y
        x x x y x x y
        M D
        hz hz hz hy hz hz hy
        hx hx hx hy hx hx hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨9, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (z * z * z * y * z * y * z) - (-48 / 30240 : 𝕂) • (x * x * x * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z y z
        x x x y x y x
        M D
        hz hz hz hy hz hy hz
        hx hx hx hy hx hy hx
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨10, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * z * y * z * y * y) - (-6 / 30240 : 𝕂) • (x * x * x * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z y y
        x x x y x y y
        M D
        hz hz hz hy hz hy hy
        hx hx hx hy hx hy hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨11, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * z * y * y * z * z) - (-6 / 30240 : 𝕂) • (x * x * x * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y z z
        x x x y y x x
        M D
        hz hz hz hy hy hz hz
        hx hx hx hy hy hx hx
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨12, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * z * y * y * z * y) - (-6 / 30240 : 𝕂) • (x * x * x * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y z y
        x x x y y x y
        M D
        hz hz hz hy hy hz hy
        hx hx hx hy hy hx hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨13, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (z * z * z * y * y * y * z) - (-20 / 30240 : 𝕂) • (x * x * x * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y y z
        x x x y y y x
        M D
        hz hz hz hy hy hy hz
        hx hx hx hy hy hy hx
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨14, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (z * z * z * y * y * y * y) - (8 / 30240 : 𝕂) • (x * x * x * y * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y y y
        x x x y y y y
        M D
        hz hz hz hy hy hy hy
        hx hx hx hy hy hy hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨15, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * z * y * z * z * z * z) - (15 / 30240 : 𝕂) • (x * x * y * x * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z z z
        x x y x x x x
        M D
        hz hz hy hz hz hz hz
        hx hx hy hx hx hx hx
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨16, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * y * z * z * z * y) - (-6 / 30240 : 𝕂) • (x * x * y * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z z y
        x x y x x x y
        M D
        hz hz hy hz hz hz hy
        hx hx hy hx hx hx hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨17, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * z * y * z * z * y * z) - (36 / 30240 : 𝕂) • (x * x * y * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z y z
        x x y x x y x
        M D
        hz hz hy hz hz hy hz
        hx hx hy hx hx hy hx
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨18, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (z * z * y * z * z * y * y) - (-27 / 30240 : 𝕂) • (x * x * y * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z y y
        x x y x x y y
        M D
        hz hz hy hz hz hy hy
        hx hx hy hx hx hy hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨19, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * z * y * z * y * z * z) - (36 / 30240 : 𝕂) • (x * x * y * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y z z
        x x y x y x x
        M D
        hz hz hy hz hy hz hz
        hx hx hy hx hy hx hx
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨20, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * z * y * z * y * z * y) - (36 / 30240 : 𝕂) • (x * x * y * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y z y
        x x y x y x y
        M D
        hz hz hy hz hy hz hy
        hx hx hy hx hy hx hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨21, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * z * y * z * y * y * z) - (36 / 30240 : 𝕂) • (x * x * y * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y y z
        x x y x y y x
        M D
        hz hz hy hz hy hy hz
        hx hx hy hx hy hy hx
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨22, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * y * z * y * y * y) - (-6 / 30240 : 𝕂) • (x * x * y * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y y y
        x x y x y y y
        M D
        hz hz hy hz hy hy hy
        hx hx hy hx hy hy hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨23, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * y * y * z * z * z) - (-6 / 30240 : 𝕂) • (x * x * y * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z z z
        x x y y x x x
        M D
        hz hz hy hy hz hz hz
        hx hx hy hy hx hx hx
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨24, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (z * z * y * y * z * z * y) - (-27 / 30240 : 𝕂) • (x * x * y * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z z y
        x x y y x x y
        M D
        hz hz hy hy hz hz hy
        hx hx hy hy hx hx hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨25, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * z * y * y * z * y * z) - (36 / 30240 : 𝕂) • (x * x * y * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z y z
        x x y y x y x
        M D
        hz hz hy hy hz hy hz
        hx hx hy hy hx hy hx
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨26, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (z * z * y * y * z * y * y) - (-27 / 30240 : 𝕂) • (x * x * y * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z y y
        x x y y x y y
        M D
        hz hz hy hy hz hy hy
        hx hx hy hy hx hy hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨27, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * y * y * y * z * z) - (-6 / 30240 : 𝕂) • (x * x * y * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y z z
        x x y y y x x
        M D
        hz hz hy hy hy hz hz
        hx hx hy hy hy hx hx
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨28, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * y * y * y * z * y) - (-6 / 30240 : 𝕂) • (x * x * y * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y z y
        x x y y y x y
        M D
        hz hz hy hy hy hz hy
        hx hx hy hy hy hx hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨29, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * z * y * y * y * y * z) - (15 / 30240 : 𝕂) • (x * x * y * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y y z
        x x y y y y x
        M D
        hz hz hy hy hy hy hz
        hx hx hy hy hy hy hx
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨30, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * z * y * y * y * y * y) - (-6 / 30240 : 𝕂) • (x * x * y * y * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y y y
        x x y y y y y
        M D
        hz hz hy hy hy hy hy
        hx hx hy hy hy hy hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨31, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * z * z * z * z * z) - (-6 / 30240 : 𝕂) • (x * y * x * x * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z z z
        x y x x x x x
        M D
        hz hy hz hz hz hz hz
        hx hy hx hx hx hx hx
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨32, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * y * z * z * z * z * y) - (15 / 30240 : 𝕂) • (x * y * x * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z z y
        x y x x x x y
        M D
        hz hy hz hz hz hz hy
        hx hy hx hx hx hx hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨33, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (z * y * z * z * z * y * z) - (-48 / 30240 : 𝕂) • (x * y * x * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z y z
        x y x x x y x
        M D
        hz hy hz hz hz hy hz
        hx hy hx hx hx hy hx
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨34, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * z * z * z * y * y) - (-6 / 30240 : 𝕂) • (x * y * x * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z y y
        x y x x x y y
        M D
        hz hy hz hz hz hy hy
        hx hy hx hx hx hy hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨35, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * z * z * y * z * z) - (36 / 30240 : 𝕂) • (x * y * x * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y z z
        x y x x y x x
        M D
        hz hy hz hz hy hz hz
        hx hy hx hx hy hx hx
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨36, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * z * z * y * z * y) - (36 / 30240 : 𝕂) • (x * y * x * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y z y
        x y x x y x y
        M D
        hz hy hz hz hy hz hy
        hx hy hx hx hy hx hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨37, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * z * z * y * y * z) - (36 / 30240 : 𝕂) • (x * y * x * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y y z
        x y x x y y x
        M D
        hz hy hz hz hy hy hz
        hx hy hx hx hy hy hx
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨38, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * z * z * y * y * y) - (-6 / 30240 : 𝕂) • (x * y * x * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y y y
        x y x x y y y
        M D
        hz hy hz hz hy hy hy
        hx hy hx hx hy hy hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨39, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (z * y * z * y * z * z * z) - (-48 / 30240 : 𝕂) • (x * y * x * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z z z
        x y x y x x x
        M D
        hz hy hz hy hz hz hz
        hx hy hx hy hx hx hx
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨40, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * z * y * z * z * y) - (36 / 30240 : 𝕂) • (x * y * x * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z z y
        x y x y x x y
        M D
        hz hy hz hy hz hz hy
        hx hy hx hy hx hx hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨41, _⟩ =>
    show ‖(-216 / 30240 : 𝕂) • (z * y * z * y * z * y * z) - (-216 / 30240 : 𝕂) • (x * y * x * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-216 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z y z
        x y x y x y x
        M D
        hz hy hz hy hz hy hz
        hx hy hx hy hx hy hx
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨42, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * z * y * z * y * y) - (36 / 30240 : 𝕂) • (x * y * x * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z y y
        x y x y x y y
        M D
        hz hy hz hy hz hy hy
        hx hy hx hy hx hy hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨43, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * z * y * y * z * z) - (36 / 30240 : 𝕂) • (x * y * x * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y z z
        x y x y y x x
        M D
        hz hy hz hy hy hz hz
        hx hy hx hy hy hx hx
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨44, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * z * y * y * z * y) - (36 / 30240 : 𝕂) • (x * y * x * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y z y
        x y x y y x y
        M D
        hz hy hz hy hy hz hy
        hx hy hx hy hy hx hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨45, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (z * y * z * y * y * y * z) - (-48 / 30240 : 𝕂) • (x * y * x * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y y z
        x y x y y y x
        M D
        hz hy hz hy hy hy hz
        hx hy hx hy hy hy hx
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨46, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * y * z * y * y * y * y) - (15 / 30240 : 𝕂) • (x * y * x * y * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y y y
        x y x y y y y
        M D
        hz hy hz hy hy hy hy
        hx hy hx hy hy hy hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨47, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * y * y * z * z * z * z) - (15 / 30240 : 𝕂) • (x * y * y * x * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z z z
        x y y x x x x
        M D
        hz hy hy hz hz hz hz
        hx hy hy hx hx hx hx
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨48, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * y * z * z * z * y) - (-6 / 30240 : 𝕂) • (x * y * y * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z z y
        x y y x x x y
        M D
        hz hy hy hz hz hz hy
        hx hy hy hx hx hx hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨49, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * y * z * z * y * z) - (36 / 30240 : 𝕂) • (x * y * y * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z y z
        x y y x x y x
        M D
        hz hy hy hz hz hy hz
        hx hy hy hx hx hy hx
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨50, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (z * y * y * z * z * y * y) - (-27 / 30240 : 𝕂) • (x * y * y * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z y y
        x y y x x y y
        M D
        hz hy hy hz hz hy hy
        hx hy hy hx hx hy hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨51, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * y * z * y * z * z) - (36 / 30240 : 𝕂) • (x * y * y * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y z z
        x y y x y x x
        M D
        hz hy hy hz hy hz hz
        hx hy hy hx hy hx hx
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨52, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * y * z * y * z * y) - (36 / 30240 : 𝕂) • (x * y * y * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y z y
        x y y x y x y
        M D
        hz hy hy hz hy hz hy
        hx hy hy hx hy hx hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨53, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (z * y * y * z * y * y * z) - (36 / 30240 : 𝕂) • (x * y * y * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y y z
        x y y x y y x
        M D
        hz hy hy hz hy hy hz
        hx hy hy hx hy hy hx
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨54, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * y * z * y * y * y) - (-6 / 30240 : 𝕂) • (x * y * y * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y y y
        x y y x y y y
        M D
        hz hy hy hz hy hy hy
        hx hy hy hx hy hy hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨55, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (z * y * y * y * z * z * z) - (-20 / 30240 : 𝕂) • (x * y * y * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z z z
        x y y y x x x
        M D
        hz hy hy hy hz hz hz
        hx hy hy hy hx hx hx
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨56, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * y * y * z * z * y) - (-6 / 30240 : 𝕂) • (x * y * y * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z z y
        x y y y x x y
        M D
        hz hy hy hy hz hz hy
        hx hy hy hy hx hx hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨57, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (z * y * y * y * z * y * z) - (-48 / 30240 : 𝕂) • (x * y * y * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z y z
        x y y y x y x
        M D
        hz hy hy hy hz hy hz
        hx hy hy hy hx hy hx
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨58, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * y * y * z * y * y) - (-6 / 30240 : 𝕂) • (x * y * y * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z y y
        x y y y x y y
        M D
        hz hy hy hy hz hy hy
        hx hy hy hy hx hy hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨59, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * y * y * y * y * z * z) - (15 / 30240 : 𝕂) • (x * y * y * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y y z z
        x y y y y x x
        M D
        hz hy hy hy hy hz hz
        hx hy hy hy hy hx hx
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨60, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (z * y * y * y * y * z * y) - (15 / 30240 : 𝕂) • (x * y * y * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y y z y
        x y y y y x y
        M D
        hz hy hy hy hy hz hy
        hx hy hy hy hy hx hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨61, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (z * y * y * y * y * y * z) - (-6 / 30240 : 𝕂) • (x * y * y * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y y y z
        x y y y y y x
        M D
        hz hy hy hy hy hy hz
        hx hy hy hy hy hy hx
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨62, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (z * y * y * y * y * y * y) - (1 / 30240 : 𝕂) • (x * y * y * y * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y y y y
        x y y y y y y
        M D
        hz hy hy hy hy hy hy
        hx hy hy hy hy hy hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨63, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (y * z * z * z * z * z * z) - (1 / 30240 : 𝕂) • (y * x * x * x * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z z z z
        y x x x x x x
        M D
        hy hz hz hz hz hz hz
        hy hx hx hx hx hx hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨64, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * z * z * z * z * y) - (-6 / 30240 : 𝕂) • (y * x * x * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z z z y
        y x x x x x y
        M D
        hy hz hz hz hz hz hy
        hy hx hx hx hx hx hy
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨65, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * z * z * z * z * y * z) - (15 / 30240 : 𝕂) • (y * x * x * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z z y z
        y x x x x y x
        M D
        hy hz hz hz hz hy hz
        hy hx hx hx hx hy hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨66, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * z * z * z * z * y * y) - (15 / 30240 : 𝕂) • (y * x * x * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z z y y
        y x x x x y y
        M D
        hy hz hz hz hz hy hy
        hy hx hx hx hx hy hy
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨67, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * z * z * y * z * z) - (-6 / 30240 : 𝕂) • (y * x * x * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y z z
        y x x x y x x
        M D
        hy hz hz hz hy hz hz
        hy hx hx hx hy hx hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨68, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (y * z * z * z * y * z * y) - (-48 / 30240 : 𝕂) • (y * x * x * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y z y
        y x x x y x y
        M D
        hy hz hz hz hy hz hy
        hy hx hx hx hy hx hy
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨69, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * z * z * y * y * z) - (-6 / 30240 : 𝕂) • (y * x * x * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y y z
        y x x x y y x
        M D
        hy hz hz hz hy hy hz
        hy hx hx hx hy hy hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨70, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (y * z * z * z * y * y * y) - (-20 / 30240 : 𝕂) • (y * x * x * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y y y
        y x x x y y y
        M D
        hy hz hz hz hy hy hy
        hy hx hx hx hy hy hy
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨71, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * z * y * z * z * z) - (-6 / 30240 : 𝕂) • (y * x * x * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z z z
        y x x y x x x
        M D
        hy hz hz hy hz hz hz
        hy hx hx hy hx hx hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨72, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * z * y * z * z * y) - (36 / 30240 : 𝕂) • (y * x * x * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z z y
        y x x y x x y
        M D
        hy hz hz hy hz hz hy
        hy hx hx hy hx hx hy
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨73, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * z * y * z * y * z) - (36 / 30240 : 𝕂) • (y * x * x * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z y z
        y x x y x y x
        M D
        hy hz hz hy hz hy hz
        hy hx hx hy hx hy hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨74, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * z * y * z * y * y) - (36 / 30240 : 𝕂) • (y * x * x * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z y y
        y x x y x y y
        M D
        hy hz hz hy hz hy hy
        hy hx hx hy hx hy hy
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨75, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (y * z * z * y * y * z * z) - (-27 / 30240 : 𝕂) • (y * x * x * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y z z
        y x x y y x x
        M D
        hy hz hz hy hy hz hz
        hy hx hx hy hy hx hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨76, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * z * y * y * z * y) - (36 / 30240 : 𝕂) • (y * x * x * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y z y
        y x x y y x y
        M D
        hy hz hz hy hy hz hy
        hy hx hx hy hy hx hy
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨77, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * z * y * y * y * z) - (-6 / 30240 : 𝕂) • (y * x * x * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y y z
        y x x y y y x
        M D
        hy hz hz hy hy hy hz
        hy hx hx hy hy hy hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨78, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * z * z * y * y * y * y) - (15 / 30240 : 𝕂) • (y * x * x * y * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y y y
        y x x y y y y
        M D
        hy hz hz hy hy hy hy
        hy hx hx hy hy hy hy
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨79, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * z * y * z * z * z * z) - (15 / 30240 : 𝕂) • (y * x * y * x * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z z z
        y x y x x x x
        M D
        hy hz hy hz hz hz hz
        hy hx hy hx hx hx hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨80, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (y * z * y * z * z * z * y) - (-48 / 30240 : 𝕂) • (y * x * y * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z z y
        y x y x x x y
        M D
        hy hz hy hz hz hz hy
        hy hx hy hx hx hx hy
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨81, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * y * z * z * y * z) - (36 / 30240 : 𝕂) • (y * x * y * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z y z
        y x y x x y x
        M D
        hy hz hy hz hz hy hz
        hy hx hy hx hx hy hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨82, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * y * z * z * y * y) - (36 / 30240 : 𝕂) • (y * x * y * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z y y
        y x y x x y y
        M D
        hy hz hy hz hz hy hy
        hy hx hy hx hx hy hy
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨83, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * y * z * y * z * z) - (36 / 30240 : 𝕂) • (y * x * y * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y z z
        y x y x y x x
        M D
        hy hz hy hz hy hz hz
        hy hx hy hx hy hx hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨84, _⟩ =>
    show ‖(-216 / 30240 : 𝕂) • (y * z * y * z * y * z * y) - (-216 / 30240 : 𝕂) • (y * x * y * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-216 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y z y
        y x y x y x y
        M D
        hy hz hy hz hy hz hy
        hy hx hy hx hy hx hy
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨85, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * y * z * y * y * z) - (36 / 30240 : 𝕂) • (y * x * y * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y y z
        y x y x y y x
        M D
        hy hz hy hz hy hy hz
        hy hx hy hx hy hy hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨86, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (y * z * y * z * y * y * y) - (-48 / 30240 : 𝕂) • (y * x * y * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y y y
        y x y x y y y
        M D
        hy hz hy hz hy hy hy
        hy hx hy hx hy hy hy
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨87, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * y * y * z * z * z) - (-6 / 30240 : 𝕂) • (y * x * y * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z z z
        y x y y x x x
        M D
        hy hz hy hy hz hz hz
        hy hx hy hy hx hx hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨88, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * y * y * z * z * y) - (36 / 30240 : 𝕂) • (y * x * y * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z z y
        y x y y x x y
        M D
        hy hz hy hy hz hz hy
        hy hx hy hy hx hx hy
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨89, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * y * y * z * y * z) - (36 / 30240 : 𝕂) • (y * x * y * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z y z
        y x y y x y x
        M D
        hy hz hy hy hz hy hz
        hy hx hy hy hx hy hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨90, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * z * y * y * z * y * y) - (36 / 30240 : 𝕂) • (y * x * y * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z y y
        y x y y x y y
        M D
        hy hz hy hy hz hy hy
        hy hx hy hy hx hy hy
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨91, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * y * y * y * z * z) - (-6 / 30240 : 𝕂) • (y * x * y * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y z z
        y x y y y x x
        M D
        hy hz hy hy hy hz hz
        hy hx hy hy hy hx hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨92, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (y * z * y * y * y * z * y) - (-48 / 30240 : 𝕂) • (y * x * y * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y z y
        y x y y y x y
        M D
        hy hz hy hy hy hz hy
        hy hx hy hy hy hx hy
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨93, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * z * y * y * y * y * z) - (15 / 30240 : 𝕂) • (y * x * y * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y y z
        y x y y y y x
        M D
        hy hz hy hy hy hy hz
        hy hx hy hy hy hy hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨94, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * z * y * y * y * y * y) - (-6 / 30240 : 𝕂) • (y * x * y * y * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y y y
        y x y y y y y
        M D
        hy hz hy hy hy hy hy
        hy hx hy hy hy hy hy
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨95, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * z * z * z * z * z) - (-6 / 30240 : 𝕂) • (y * y * x * x * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z z z
        y y x x x x x
        M D
        hy hy hz hz hz hz hz
        hy hy hx hx hx hx hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨96, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * y * z * z * z * z * y) - (15 / 30240 : 𝕂) • (y * y * x * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z z y
        y y x x x x y
        M D
        hy hy hz hz hz hz hy
        hy hy hx hx hx hx hy
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨97, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * z * z * z * y * z) - (-6 / 30240 : 𝕂) • (y * y * x * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z y z
        y y x x x y x
        M D
        hy hy hz hz hz hy hz
        hy hy hx hx hx hy hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨98, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * z * z * z * y * y) - (-6 / 30240 : 𝕂) • (y * y * x * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z y y
        y y x x x y y
        M D
        hy hy hz hz hz hy hy
        hy hy hx hx hx hy hy
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨99, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (y * y * z * z * y * z * z) - (-27 / 30240 : 𝕂) • (y * y * x * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y z z
        y y x x y x x
        M D
        hy hy hz hz hy hz hz
        hy hy hx hx hy hx hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨100, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * y * z * z * y * z * y) - (36 / 30240 : 𝕂) • (y * y * x * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y z y
        y y x x y x y
        M D
        hy hy hz hz hy hz hy
        hy hy hx hx hy hx hy
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨101, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (y * y * z * z * y * y * z) - (-27 / 30240 : 𝕂) • (y * y * x * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y y z
        y y x x y y x
        M D
        hy hy hz hz hy hy hz
        hy hy hx hx hy hy hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨102, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * z * z * y * y * y) - (-6 / 30240 : 𝕂) • (y * y * x * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y y y
        y y x x y y y
        M D
        hy hy hz hz hy hy hy
        hy hy hx hx hy hy hy
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨103, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * z * y * z * z * z) - (-6 / 30240 : 𝕂) • (y * y * x * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z z z
        y y x y x x x
        M D
        hy hy hz hy hz hz hz
        hy hy hx hy hx hx hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨104, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * y * z * y * z * z * y) - (36 / 30240 : 𝕂) • (y * y * x * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z z y
        y y x y x x y
        M D
        hy hy hz hy hz hz hy
        hy hy hx hy hx hx hy
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨105, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * y * z * y * z * y * z) - (36 / 30240 : 𝕂) • (y * y * x * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z y z
        y y x y x y x
        M D
        hy hy hz hy hz hy hz
        hy hy hx hy hx hy hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨106, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * y * z * y * z * y * y) - (36 / 30240 : 𝕂) • (y * y * x * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z y y
        y y x y x y y
        M D
        hy hy hz hy hz hy hy
        hy hy hx hy hx hy hy
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨107, _⟩ =>
    show ‖(-27 / 30240 : 𝕂) • (y * y * z * y * y * z * z) - (-27 / 30240 : 𝕂) • (y * y * x * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-27 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y z z
        y y x y y x x
        M D
        hy hy hz hy hy hz hz
        hy hy hx hy hy hx hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨108, _⟩ =>
    show ‖(36 / 30240 : 𝕂) • (y * y * z * y * y * z * y) - (36 / 30240 : 𝕂) • (y * y * x * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (36 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y z y
        y y x y y x y
        M D
        hy hy hz hy hy hz hy
        hy hy hx hy hy hx hy
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨109, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * z * y * y * y * z) - (-6 / 30240 : 𝕂) • (y * y * x * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y y z
        y y x y y y x
        M D
        hy hy hz hy hy hy hz
        hy hy hx hy hy hy hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨110, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * y * z * y * y * y * y) - (15 / 30240 : 𝕂) • (y * y * x * y * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y y y
        y y x y y y y
        M D
        hy hy hz hy hy hy hy
        hy hy hx hy hy hy hy
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨111, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (y * y * y * z * z * z * z) - (8 / 30240 : 𝕂) • (y * y * y * x * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z z z
        y y y x x x x
        M D
        hy hy hy hz hz hz hz
        hy hy hy hx hx hx hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨112, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (y * y * y * z * z * z * y) - (-20 / 30240 : 𝕂) • (y * y * y * x * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z z y
        y y y x x x y
        M D
        hy hy hy hz hz hz hy
        hy hy hy hx hx hx hy
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨113, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * y * z * z * y * z) - (-6 / 30240 : 𝕂) • (y * y * y * x * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z y z
        y y y x x y x
        M D
        hy hy hy hz hz hy hz
        hy hy hy hx hx hy hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨114, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * y * z * z * y * y) - (-6 / 30240 : 𝕂) • (y * y * y * x * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z y y
        y y y x x y y
        M D
        hy hy hy hz hz hy hy
        hy hy hy hx hx hy hy
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨115, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * y * z * y * z * z) - (-6 / 30240 : 𝕂) • (y * y * y * x * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y z z
        y y y x y x x
        M D
        hy hy hy hz hy hz hz
        hy hy hy hx hy hx hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨116, _⟩ =>
    show ‖(-48 / 30240 : 𝕂) • (y * y * y * z * y * z * y) - (-48 / 30240 : 𝕂) • (y * y * y * x * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-48 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y z y
        y y y x y x y
        M D
        hy hy hy hz hy hz hy
        hy hy hy hx hy hx hy
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨117, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * y * z * y * y * z) - (-6 / 30240 : 𝕂) • (y * y * y * x * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y y z
        y y y x y y x
        M D
        hy hy hy hz hy hy hz
        hy hy hy hx hy hy hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨118, _⟩ =>
    show ‖(-20 / 30240 : 𝕂) • (y * y * y * z * y * y * y) - (-20 / 30240 : 𝕂) • (y * y * y * x * y * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-20 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y y y
        y y y x y y y
        M D
        hy hy hy hz hy hy hy
        hy hy hy hx hy hy hy
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨119, _⟩ =>
    show ‖(8 / 30240 : 𝕂) • (y * y * y * y * z * z * z) - (8 / 30240 : 𝕂) • (y * y * y * y * x * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (8 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z z z
        y y y y x x x
        M D
        hy hy hy hy hz hz hz
        hy hy hy hy hx hx hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨120, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * y * y * y * z * z * y) - (15 / 30240 : 𝕂) • (y * y * y * y * x * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z z y
        y y y y x x y
        M D
        hy hy hy hy hz hz hy
        hy hy hy hy hx hx hy
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨121, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * y * y * y * z * y * z) - (15 / 30240 : 𝕂) • (y * y * y * y * x * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z y z
        y y y y x y x
        M D
        hy hy hy hy hz hy hz
        hy hy hy hy hx hy hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨122, _⟩ =>
    show ‖(15 / 30240 : 𝕂) • (y * y * y * y * z * y * y) - (15 / 30240 : 𝕂) • (y * y * y * y * x * y * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (15 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z y y
        y y y y x y y
        M D
        hy hy hy hy hz hy hy
        hy hy hy hy hx hy hy
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨123, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * y * y * y * z * z) - (-6 / 30240 : 𝕂) • (y * y * y * y * y * x * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y y z z
        y y y y y x x
        M D
        hy hy hy hy hy hz hz
        hy hy hy hy hy hx hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨124, _⟩ =>
    show ‖(-6 / 30240 : 𝕂) • (y * y * y * y * y * z * y) - (-6 / 30240 : 𝕂) • (y * y * y * y * y * x * y)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (-6 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y y z y
        y y y y y x y
        M D
        hy hy hy hy hy hz hy
        hy hy hy hy hy hx hy
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨125, _⟩ =>
    show ‖(1 / 30240 : 𝕂) • (y * y * y * y * y * y * z) - (1 / 30240 : 𝕂) • (y * y * y * y * y * y * x)‖ ≤
         (216 / 30240 : ℝ) * 7 * M^6 * D
    exact deg7_smul_word_diff_le_basic (1 / 30240 : 𝕂) (216 / 30240 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y y y z
        y y y y y y x
        M D
        hy hy hy hy hy hy hz
        hy hy hy hy hy hy hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨_ + 126, h⟩ => exact absurd h (by omega)

set_option maxHeartbeats 800000 in
/-- **Lipschitz bound for `bch_septic_term`**: `‖Z₇(z, y) − Z₇(x, y)‖ ≤ 7·M⁶·‖z−x‖`
where `M = ‖z‖+‖x‖+‖y‖`.

Analog of `norm_bch_sextic_term_diff_le` at one degree higher; with
`z = (a'+b) + W` and `‖W‖ = O(s²)`, gives an O(s⁸·‖W‖) bound on
`‖C₇(z, y) − C₇(a'+b, y)‖`. Foundation for stepping stone 1
(`symmetric_bch_septic_sub_poly_axiom` discharge).

The proof uses a uniform per-i bound `(216/30240) · 7 · M⁶ · ‖z−x‖`,
giving `Σ ≤ 126·216·7/30240 = 190512/30240 = 63/10 ≤ 7`. -/
theorem norm_bch_septic_term_diff_le (z x y : 𝔸) :
    ‖bch_septic_term 𝕂 z y - bch_septic_term 𝕂 x y‖ ≤
      7 * (‖z‖ + ‖x‖ + ‖y‖) ^ 6 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  have hM_nn : 0 ≤ M := by positivity
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have hM6_nn : 0 ≤ M^6 := pow_nonneg hM_nn 6
  have hzx_nn : 0 ≤ ‖z - x‖ := norm_nonneg _
  rw [bch_septic_term_eq_sum, bch_septic_term_eq_sum, ← Finset.sum_sub_distrib]
  calc ‖∑ i : Fin 126, (bchSepticTerm (𝕂 := 𝕂) z y i - bchSepticTerm (𝕂 := 𝕂) x y i)‖
      ≤ ∑ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) z y i - bchSepticTerm (𝕂 := 𝕂) x y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 126, (216 / 30240 : ℝ) * 7 * M^6 * ‖z - x‖ :=
        Finset.sum_le_sum (fun i _ => bchSepticTerm_diff_norm_le (𝕂 := 𝕂) z x y M hz_le hx_le hy_le hM_nn i)
    _ = 126 * ((216 / 30240 : ℝ) * 7 * M^6 * ‖z - x‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ 7 * M^6 * ‖z - x‖ := by nlinarith [hM6_nn, hzx_nn]

/-! ### `bch_octic_term` — the τ⁸ coefficient of `bch(a, b)`

Explicit 124-term polynomial in {a, b}, derived via the CAS pipeline at
`scripts/compute_bch_octic_term.py`. Common denominator 120960; integer
numerators in {±2, ±12, ±23, ±30, ±40, ±54, ±72, ±96, ±432}.
Sum of |numerators|/120960 = 5970/120960 = 199/4032 ≈ 0.0494.

This is the next term in the BCH expansion after `bch_septic_term`:
`bch(a, b) = a + b + ½[a,b] + Z₃ + Z₄ + Z₅ + Z₆ + Z₇ + Z₈ + O(·^9)`.

Used in the future nonic identity (stepping stone 1) for canceling deg-8
contributions to `sym_bch_cubic - sym_E₃ - sym_E₅ - sym_E₇` (the deg-9
analog of the discharged `symmetric_bch_quintic_sub_poly_axiom`). -/

/-- **τ⁸ coefficient of `bch(a, b)`** — explicit 124-term polynomial in
{a, b}. The 124 non-zero 8-letter words (out of 256 = 2⁸ possible) come
from the free Lie algebra basis at degree 8. Coefficients are rational
with LCM 120960. -/
noncomputable def bch_octic_term (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) : 𝔸 :=
    (2 / 120960 : 𝕂) • (a * a * a * a * a * a * b * b)
  + (-12 / 120960 : 𝕂) • (a * a * a * a * a * b * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * a * a * a * b * b * b)
  + (30 / 120960 : 𝕂) • (a * a * a * a * b * a * a * b)
  + (30 / 120960 : 𝕂) • (a * a * a * a * b * a * b * b)
  + (30 / 120960 : 𝕂) • (a * a * a * a * b * b * a * b)
  + (23 / 120960 : 𝕂) • (a * a * a * a * b * b * b * b)
  + (-40 / 120960 : 𝕂) • (a * a * a * b * a * a * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * a * b * a * a * b * b)
  + (-96 / 120960 : 𝕂) • (a * a * a * b * a * b * a * b)
  + (-40 / 120960 : 𝕂) • (a * a * a * b * a * b * b * b)
  + (-12 / 120960 : 𝕂) • (a * a * a * b * b * a * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * a * b * b * a * b * b)
  + (-40 / 120960 : 𝕂) • (a * a * a * b * b * b * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * a * b * b * b * b * b)
  + (30 / 120960 : 𝕂) • (a * a * b * a * a * a * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * b * a * a * a * b * b)
  + (72 / 120960 : 𝕂) • (a * a * b * a * a * b * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * b * a * a * b * b * b)
  + (72 / 120960 : 𝕂) • (a * a * b * a * b * a * a * b)
  + (72 / 120960 : 𝕂) • (a * a * b * a * b * a * b * b)
  + (72 / 120960 : 𝕂) • (a * a * b * a * b * b * a * b)
  + (30 / 120960 : 𝕂) • (a * a * b * a * b * b * b * b)
  + (-12 / 120960 : 𝕂) • (a * a * b * b * a * a * a * b)
  + (-54 / 120960 : 𝕂) • (a * a * b * b * a * a * b * b)
  + (72 / 120960 : 𝕂) • (a * a * b * b * a * b * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * b * b * a * b * b * b)
  + (-12 / 120960 : 𝕂) • (a * a * b * b * b * a * a * b)
  + (-12 / 120960 : 𝕂) • (a * a * b * b * b * a * b * b)
  + (30 / 120960 : 𝕂) • (a * a * b * b * b * b * a * b)
  + (2 / 120960 : 𝕂) • (a * a * b * b * b * b * b * b)
  + (-12 / 120960 : 𝕂) • (a * b * a * a * a * a * a * b)
  + (30 / 120960 : 𝕂) • (a * b * a * a * a * a * b * b)
  + (-96 / 120960 : 𝕂) • (a * b * a * a * a * b * a * b)
  + (-40 / 120960 : 𝕂) • (a * b * a * a * a * b * b * b)
  + (72 / 120960 : 𝕂) • (a * b * a * a * b * a * a * b)
  + (72 / 120960 : 𝕂) • (a * b * a * a * b * a * b * b)
  + (72 / 120960 : 𝕂) • (a * b * a * a * b * b * a * b)
  + (30 / 120960 : 𝕂) • (a * b * a * a * b * b * b * b)
  + (-96 / 120960 : 𝕂) • (a * b * a * b * a * a * a * b)
  + (72 / 120960 : 𝕂) • (a * b * a * b * a * a * b * b)
  + (-432 / 120960 : 𝕂) • (a * b * a * b * a * b * a * b)
  + (-96 / 120960 : 𝕂) • (a * b * a * b * a * b * b * b)
  + (72 / 120960 : 𝕂) • (a * b * a * b * b * a * a * b)
  + (72 / 120960 : 𝕂) • (a * b * a * b * b * a * b * b)
  + (-96 / 120960 : 𝕂) • (a * b * a * b * b * b * a * b)
  + (-12 / 120960 : 𝕂) • (a * b * a * b * b * b * b * b)
  + (30 / 120960 : 𝕂) • (a * b * b * a * a * a * a * b)
  + (-12 / 120960 : 𝕂) • (a * b * b * a * a * a * b * b)
  + (72 / 120960 : 𝕂) • (a * b * b * a * a * b * a * b)
  + (-12 / 120960 : 𝕂) • (a * b * b * a * a * b * b * b)
  + (72 / 120960 : 𝕂) • (a * b * b * a * b * a * a * b)
  + (72 / 120960 : 𝕂) • (a * b * b * a * b * a * b * b)
  + (72 / 120960 : 𝕂) • (a * b * b * a * b * b * a * b)
  + (30 / 120960 : 𝕂) • (a * b * b * a * b * b * b * b)
  + (-40 / 120960 : 𝕂) • (a * b * b * b * a * a * a * b)
  + (-12 / 120960 : 𝕂) • (a * b * b * b * a * a * b * b)
  + (-96 / 120960 : 𝕂) • (a * b * b * b * a * b * a * b)
  + (-40 / 120960 : 𝕂) • (a * b * b * b * a * b * b * b)
  + (30 / 120960 : 𝕂) • (a * b * b * b * b * a * a * b)
  + (30 / 120960 : 𝕂) • (a * b * b * b * b * a * b * b)
  + (-12 / 120960 : 𝕂) • (a * b * b * b * b * b * a * b)
  + (12 / 120960 : 𝕂) • (b * a * a * a * a * a * b * a)
  + (-30 / 120960 : 𝕂) • (b * a * a * a * a * b * a * a)
  + (-30 / 120960 : 𝕂) • (b * a * a * a * a * b * b * a)
  + (40 / 120960 : 𝕂) • (b * a * a * a * b * a * a * a)
  + (96 / 120960 : 𝕂) • (b * a * a * a * b * a * b * a)
  + (12 / 120960 : 𝕂) • (b * a * a * a * b * b * a * a)
  + (40 / 120960 : 𝕂) • (b * a * a * a * b * b * b * a)
  + (-30 / 120960 : 𝕂) • (b * a * a * b * a * a * a * a)
  + (-72 / 120960 : 𝕂) • (b * a * a * b * a * a * b * a)
  + (-72 / 120960 : 𝕂) • (b * a * a * b * a * b * a * a)
  + (-72 / 120960 : 𝕂) • (b * a * a * b * a * b * b * a)
  + (12 / 120960 : 𝕂) • (b * a * a * b * b * a * a * a)
  + (-72 / 120960 : 𝕂) • (b * a * a * b * b * a * b * a)
  + (12 / 120960 : 𝕂) • (b * a * a * b * b * b * a * a)
  + (-30 / 120960 : 𝕂) • (b * a * a * b * b * b * b * a)
  + (12 / 120960 : 𝕂) • (b * a * b * a * a * a * a * a)
  + (96 / 120960 : 𝕂) • (b * a * b * a * a * a * b * a)
  + (-72 / 120960 : 𝕂) • (b * a * b * a * a * b * a * a)
  + (-72 / 120960 : 𝕂) • (b * a * b * a * a * b * b * a)
  + (96 / 120960 : 𝕂) • (b * a * b * a * b * a * a * a)
  + (432 / 120960 : 𝕂) • (b * a * b * a * b * a * b * a)
  + (-72 / 120960 : 𝕂) • (b * a * b * a * b * b * a * a)
  + (96 / 120960 : 𝕂) • (b * a * b * a * b * b * b * a)
  + (-30 / 120960 : 𝕂) • (b * a * b * b * a * a * a * a)
  + (-72 / 120960 : 𝕂) • (b * a * b * b * a * a * b * a)
  + (-72 / 120960 : 𝕂) • (b * a * b * b * a * b * a * a)
  + (-72 / 120960 : 𝕂) • (b * a * b * b * a * b * b * a)
  + (40 / 120960 : 𝕂) • (b * a * b * b * b * a * a * a)
  + (96 / 120960 : 𝕂) • (b * a * b * b * b * a * b * a)
  + (-30 / 120960 : 𝕂) • (b * a * b * b * b * b * a * a)
  + (12 / 120960 : 𝕂) • (b * a * b * b * b * b * b * a)
  + (-2 / 120960 : 𝕂) • (b * b * a * a * a * a * a * a)
  + (-30 / 120960 : 𝕂) • (b * b * a * a * a * a * b * a)
  + (12 / 120960 : 𝕂) • (b * b * a * a * a * b * a * a)
  + (12 / 120960 : 𝕂) • (b * b * a * a * a * b * b * a)
  + (12 / 120960 : 𝕂) • (b * b * a * a * b * a * a * a)
  + (-72 / 120960 : 𝕂) • (b * b * a * a * b * a * b * a)
  + (54 / 120960 : 𝕂) • (b * b * a * a * b * b * a * a)
  + (12 / 120960 : 𝕂) • (b * b * a * a * b * b * b * a)
  + (-30 / 120960 : 𝕂) • (b * b * a * b * a * a * a * a)
  + (-72 / 120960 : 𝕂) • (b * b * a * b * a * a * b * a)
  + (-72 / 120960 : 𝕂) • (b * b * a * b * a * b * a * a)
  + (-72 / 120960 : 𝕂) • (b * b * a * b * a * b * b * a)
  + (12 / 120960 : 𝕂) • (b * b * a * b * b * a * a * a)
  + (-72 / 120960 : 𝕂) • (b * b * a * b * b * a * b * a)
  + (12 / 120960 : 𝕂) • (b * b * a * b * b * b * a * a)
  + (-30 / 120960 : 𝕂) • (b * b * a * b * b * b * b * a)
  + (12 / 120960 : 𝕂) • (b * b * b * a * a * a * a * a)
  + (40 / 120960 : 𝕂) • (b * b * b * a * a * a * b * a)
  + (12 / 120960 : 𝕂) • (b * b * b * a * a * b * a * a)
  + (12 / 120960 : 𝕂) • (b * b * b * a * a * b * b * a)
  + (40 / 120960 : 𝕂) • (b * b * b * a * b * a * a * a)
  + (96 / 120960 : 𝕂) • (b * b * b * a * b * a * b * a)
  + (12 / 120960 : 𝕂) • (b * b * b * a * b * b * a * a)
  + (40 / 120960 : 𝕂) • (b * b * b * a * b * b * b * a)
  + (-23 / 120960 : 𝕂) • (b * b * b * b * a * a * a * a)
  + (-30 / 120960 : 𝕂) • (b * b * b * b * a * a * b * a)
  + (-30 / 120960 : 𝕂) • (b * b * b * b * a * b * a * a)
  + (-30 / 120960 : 𝕂) • (b * b * b * b * a * b * b * a)
  + (12 / 120960 : 𝕂) • (b * b * b * b * b * a * a * a)
  + (12 / 120960 : 𝕂) • (b * b * b * b * b * a * b * a)
  + (-2 / 120960 : 𝕂) • (b * b * b * b * b * b * a * a)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **8-fold smul-product identity** (local copy for use in `bch_octic_term_smul`). -/
private lemma bch_octic_term_eight_fold_smul_mul
    (c : 𝕂) (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : 𝔸) :
    (c • x₁) * (c • x₂) * (c • x₃) * (c • x₄) * (c • x₅) * (c • x₆) * (c • x₇) * (c • x₈) =
      c ^ 8 • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
  ring_nf

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Homogeneity of `bch_octic_term`**: `Z₈(c•a, c•b) = c⁸ • Z₈(a, b)`. -/
theorem bch_octic_term_smul (a b : 𝔸) (c : 𝕂) :
    bch_octic_term 𝕂 (c • a) (c • b) = c ^ 8 • bch_octic_term 𝕂 a b := by
  unfold bch_octic_term
  simp only [bch_octic_term_eight_fold_smul_mul c, smul_comm _ (c ^ 8 : 𝕂), ← smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Helper (deg-8, local copy)**: `‖c • (l₁·…·l8)‖ ≤ cb · s^8` if `‖c‖ ≤ cb`
and each `‖lᵢ‖ ≤ s`. -/
private lemma deg8_smul_word_le_basic
    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)
    (l1 l2 l3 l4 l5 l6 l7 l8 : 𝔸) (s : ℝ)
    (h1 : ‖l1‖ ≤ s) (h2 : ‖l2‖ ≤ s) (h3 : ‖l3‖ ≤ s) (h4 : ‖l4‖ ≤ s)
    (h5 : ‖l5‖ ≤ s) (h6 : ‖l6‖ ≤ s) (h7 : ‖l7‖ ≤ s) (h8 : ‖l8‖ ≤ s)
    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :
    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8)‖ ≤ cb * s ^ 8 := by
  calc ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8)‖
      ≤ ‖c‖ * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8‖ := norm_smul_le _ _
    _ ≤ cb * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖ * ‖l8‖) :=
        mul_le_mul_of_nonneg_left (norm_8prod_le _ _ _ _ _ _ _ _) hcb
    _ ≤ cb * (s * s * s * s * s * s * s * s) := by
        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr
    _ = cb * s ^ 8 := by ring

-- Per-Nat-index family of terms in `bch_octic_term a b`.
set_option maxHeartbeats 1600000 in
private noncomputable def bchOcticTermN (a b : 𝔸) : Nat → 𝔸
  | 0 => (2 / 120960 : 𝕂) • (a * a * a * a * a * a * b * b)
  | 1 => (-12 / 120960 : 𝕂) • (a * a * a * a * a * b * a * b)
  | 2 => (-12 / 120960 : 𝕂) • (a * a * a * a * a * b * b * b)
  | 3 => (30 / 120960 : 𝕂) • (a * a * a * a * b * a * a * b)
  | 4 => (30 / 120960 : 𝕂) • (a * a * a * a * b * a * b * b)
  | 5 => (30 / 120960 : 𝕂) • (a * a * a * a * b * b * a * b)
  | 6 => (23 / 120960 : 𝕂) • (a * a * a * a * b * b * b * b)
  | 7 => (-40 / 120960 : 𝕂) • (a * a * a * b * a * a * a * b)
  | 8 => (-12 / 120960 : 𝕂) • (a * a * a * b * a * a * b * b)
  | 9 => (-96 / 120960 : 𝕂) • (a * a * a * b * a * b * a * b)
  | 10 => (-40 / 120960 : 𝕂) • (a * a * a * b * a * b * b * b)
  | 11 => (-12 / 120960 : 𝕂) • (a * a * a * b * b * a * a * b)
  | 12 => (-12 / 120960 : 𝕂) • (a * a * a * b * b * a * b * b)
  | 13 => (-40 / 120960 : 𝕂) • (a * a * a * b * b * b * a * b)
  | 14 => (-12 / 120960 : 𝕂) • (a * a * a * b * b * b * b * b)
  | 15 => (30 / 120960 : 𝕂) • (a * a * b * a * a * a * a * b)
  | 16 => (-12 / 120960 : 𝕂) • (a * a * b * a * a * a * b * b)
  | 17 => (72 / 120960 : 𝕂) • (a * a * b * a * a * b * a * b)
  | 18 => (-12 / 120960 : 𝕂) • (a * a * b * a * a * b * b * b)
  | 19 => (72 / 120960 : 𝕂) • (a * a * b * a * b * a * a * b)
  | 20 => (72 / 120960 : 𝕂) • (a * a * b * a * b * a * b * b)
  | 21 => (72 / 120960 : 𝕂) • (a * a * b * a * b * b * a * b)
  | 22 => (30 / 120960 : 𝕂) • (a * a * b * a * b * b * b * b)
  | 23 => (-12 / 120960 : 𝕂) • (a * a * b * b * a * a * a * b)
  | 24 => (-54 / 120960 : 𝕂) • (a * a * b * b * a * a * b * b)
  | 25 => (72 / 120960 : 𝕂) • (a * a * b * b * a * b * a * b)
  | 26 => (-12 / 120960 : 𝕂) • (a * a * b * b * a * b * b * b)
  | 27 => (-12 / 120960 : 𝕂) • (a * a * b * b * b * a * a * b)
  | 28 => (-12 / 120960 : 𝕂) • (a * a * b * b * b * a * b * b)
  | 29 => (30 / 120960 : 𝕂) • (a * a * b * b * b * b * a * b)
  | 30 => (2 / 120960 : 𝕂) • (a * a * b * b * b * b * b * b)
  | 31 => (-12 / 120960 : 𝕂) • (a * b * a * a * a * a * a * b)
  | 32 => (30 / 120960 : 𝕂) • (a * b * a * a * a * a * b * b)
  | 33 => (-96 / 120960 : 𝕂) • (a * b * a * a * a * b * a * b)
  | 34 => (-40 / 120960 : 𝕂) • (a * b * a * a * a * b * b * b)
  | 35 => (72 / 120960 : 𝕂) • (a * b * a * a * b * a * a * b)
  | 36 => (72 / 120960 : 𝕂) • (a * b * a * a * b * a * b * b)
  | 37 => (72 / 120960 : 𝕂) • (a * b * a * a * b * b * a * b)
  | 38 => (30 / 120960 : 𝕂) • (a * b * a * a * b * b * b * b)
  | 39 => (-96 / 120960 : 𝕂) • (a * b * a * b * a * a * a * b)
  | 40 => (72 / 120960 : 𝕂) • (a * b * a * b * a * a * b * b)
  | 41 => (-432 / 120960 : 𝕂) • (a * b * a * b * a * b * a * b)
  | 42 => (-96 / 120960 : 𝕂) • (a * b * a * b * a * b * b * b)
  | 43 => (72 / 120960 : 𝕂) • (a * b * a * b * b * a * a * b)
  | 44 => (72 / 120960 : 𝕂) • (a * b * a * b * b * a * b * b)
  | 45 => (-96 / 120960 : 𝕂) • (a * b * a * b * b * b * a * b)
  | 46 => (-12 / 120960 : 𝕂) • (a * b * a * b * b * b * b * b)
  | 47 => (30 / 120960 : 𝕂) • (a * b * b * a * a * a * a * b)
  | 48 => (-12 / 120960 : 𝕂) • (a * b * b * a * a * a * b * b)
  | 49 => (72 / 120960 : 𝕂) • (a * b * b * a * a * b * a * b)
  | 50 => (-12 / 120960 : 𝕂) • (a * b * b * a * a * b * b * b)
  | 51 => (72 / 120960 : 𝕂) • (a * b * b * a * b * a * a * b)
  | 52 => (72 / 120960 : 𝕂) • (a * b * b * a * b * a * b * b)
  | 53 => (72 / 120960 : 𝕂) • (a * b * b * a * b * b * a * b)
  | 54 => (30 / 120960 : 𝕂) • (a * b * b * a * b * b * b * b)
  | 55 => (-40 / 120960 : 𝕂) • (a * b * b * b * a * a * a * b)
  | 56 => (-12 / 120960 : 𝕂) • (a * b * b * b * a * a * b * b)
  | 57 => (-96 / 120960 : 𝕂) • (a * b * b * b * a * b * a * b)
  | 58 => (-40 / 120960 : 𝕂) • (a * b * b * b * a * b * b * b)
  | 59 => (30 / 120960 : 𝕂) • (a * b * b * b * b * a * a * b)
  | 60 => (30 / 120960 : 𝕂) • (a * b * b * b * b * a * b * b)
  | 61 => (-12 / 120960 : 𝕂) • (a * b * b * b * b * b * a * b)
  | 62 => (12 / 120960 : 𝕂) • (b * a * a * a * a * a * b * a)
  | 63 => (-30 / 120960 : 𝕂) • (b * a * a * a * a * b * a * a)
  | 64 => (-30 / 120960 : 𝕂) • (b * a * a * a * a * b * b * a)
  | 65 => (40 / 120960 : 𝕂) • (b * a * a * a * b * a * a * a)
  | 66 => (96 / 120960 : 𝕂) • (b * a * a * a * b * a * b * a)
  | 67 => (12 / 120960 : 𝕂) • (b * a * a * a * b * b * a * a)
  | 68 => (40 / 120960 : 𝕂) • (b * a * a * a * b * b * b * a)
  | 69 => (-30 / 120960 : 𝕂) • (b * a * a * b * a * a * a * a)
  | 70 => (-72 / 120960 : 𝕂) • (b * a * a * b * a * a * b * a)
  | 71 => (-72 / 120960 : 𝕂) • (b * a * a * b * a * b * a * a)
  | 72 => (-72 / 120960 : 𝕂) • (b * a * a * b * a * b * b * a)
  | 73 => (12 / 120960 : 𝕂) • (b * a * a * b * b * a * a * a)
  | 74 => (-72 / 120960 : 𝕂) • (b * a * a * b * b * a * b * a)
  | 75 => (12 / 120960 : 𝕂) • (b * a * a * b * b * b * a * a)
  | 76 => (-30 / 120960 : 𝕂) • (b * a * a * b * b * b * b * a)
  | 77 => (12 / 120960 : 𝕂) • (b * a * b * a * a * a * a * a)
  | 78 => (96 / 120960 : 𝕂) • (b * a * b * a * a * a * b * a)
  | 79 => (-72 / 120960 : 𝕂) • (b * a * b * a * a * b * a * a)
  | 80 => (-72 / 120960 : 𝕂) • (b * a * b * a * a * b * b * a)
  | 81 => (96 / 120960 : 𝕂) • (b * a * b * a * b * a * a * a)
  | 82 => (432 / 120960 : 𝕂) • (b * a * b * a * b * a * b * a)
  | 83 => (-72 / 120960 : 𝕂) • (b * a * b * a * b * b * a * a)
  | 84 => (96 / 120960 : 𝕂) • (b * a * b * a * b * b * b * a)
  | 85 => (-30 / 120960 : 𝕂) • (b * a * b * b * a * a * a * a)
  | 86 => (-72 / 120960 : 𝕂) • (b * a * b * b * a * a * b * a)
  | 87 => (-72 / 120960 : 𝕂) • (b * a * b * b * a * b * a * a)
  | 88 => (-72 / 120960 : 𝕂) • (b * a * b * b * a * b * b * a)
  | 89 => (40 / 120960 : 𝕂) • (b * a * b * b * b * a * a * a)
  | 90 => (96 / 120960 : 𝕂) • (b * a * b * b * b * a * b * a)
  | 91 => (-30 / 120960 : 𝕂) • (b * a * b * b * b * b * a * a)
  | 92 => (12 / 120960 : 𝕂) • (b * a * b * b * b * b * b * a)
  | 93 => (-2 / 120960 : 𝕂) • (b * b * a * a * a * a * a * a)
  | 94 => (-30 / 120960 : 𝕂) • (b * b * a * a * a * a * b * a)
  | 95 => (12 / 120960 : 𝕂) • (b * b * a * a * a * b * a * a)
  | 96 => (12 / 120960 : 𝕂) • (b * b * a * a * a * b * b * a)
  | 97 => (12 / 120960 : 𝕂) • (b * b * a * a * b * a * a * a)
  | 98 => (-72 / 120960 : 𝕂) • (b * b * a * a * b * a * b * a)
  | 99 => (54 / 120960 : 𝕂) • (b * b * a * a * b * b * a * a)
  | 100 => (12 / 120960 : 𝕂) • (b * b * a * a * b * b * b * a)
  | 101 => (-30 / 120960 : 𝕂) • (b * b * a * b * a * a * a * a)
  | 102 => (-72 / 120960 : 𝕂) • (b * b * a * b * a * a * b * a)
  | 103 => (-72 / 120960 : 𝕂) • (b * b * a * b * a * b * a * a)
  | 104 => (-72 / 120960 : 𝕂) • (b * b * a * b * a * b * b * a)
  | 105 => (12 / 120960 : 𝕂) • (b * b * a * b * b * a * a * a)
  | 106 => (-72 / 120960 : 𝕂) • (b * b * a * b * b * a * b * a)
  | 107 => (12 / 120960 : 𝕂) • (b * b * a * b * b * b * a * a)
  | 108 => (-30 / 120960 : 𝕂) • (b * b * a * b * b * b * b * a)
  | 109 => (12 / 120960 : 𝕂) • (b * b * b * a * a * a * a * a)
  | 110 => (40 / 120960 : 𝕂) • (b * b * b * a * a * a * b * a)
  | 111 => (12 / 120960 : 𝕂) • (b * b * b * a * a * b * a * a)
  | 112 => (12 / 120960 : 𝕂) • (b * b * b * a * a * b * b * a)
  | 113 => (40 / 120960 : 𝕂) • (b * b * b * a * b * a * a * a)
  | 114 => (96 / 120960 : 𝕂) • (b * b * b * a * b * a * b * a)
  | 115 => (12 / 120960 : 𝕂) • (b * b * b * a * b * b * a * a)
  | 116 => (40 / 120960 : 𝕂) • (b * b * b * a * b * b * b * a)
  | 117 => (-23 / 120960 : 𝕂) • (b * b * b * b * a * a * a * a)
  | 118 => (-30 / 120960 : 𝕂) • (b * b * b * b * a * a * b * a)
  | 119 => (-30 / 120960 : 𝕂) • (b * b * b * b * a * b * a * a)
  | 120 => (-30 / 120960 : 𝕂) • (b * b * b * b * a * b * b * a)
  | 121 => (12 / 120960 : 𝕂) • (b * b * b * b * b * a * a * a)
  | 122 => (12 / 120960 : 𝕂) • (b * b * b * b * b * a * b * a)
  | 123 => (-2 / 120960 : 𝕂) • (b * b * b * b * b * b * a * a)
  | _ => 0

/-- `Fin 124`-indexed wrapper around `bchOcticTermN`. -/
private noncomputable def bchOcticTerm (a b : 𝔸) (i : Fin 124) : 𝔸 :=
  bchOcticTermN (𝕂 := 𝕂) a b i.val

-- `bch_octic_term` equals the `Finset.sum` over `Fin 124` of `bchOcticTerm`.
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 2000 in
private theorem bch_octic_term_eq_sum (a b : 𝔸) :
    bch_octic_term 𝕂 a b = ∑ i : Fin 124, bchOcticTerm (𝕂 := 𝕂) a b i := by
  unfold bch_octic_term bchOcticTerm
  rw [Fin.sum_univ_eq_sum_range (fun k => bchOcticTermN (𝕂 := 𝕂) a b k)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bchOcticTermN, zero_add]
  try abel

-- Per-index norm bound: `‖bchOcticTerm a b i‖ ≤ (432/120960) · s^8`
-- (uniform: 432 is the max `|scaled_num|` over all 124 entries).
set_option maxHeartbeats 32000000 in
private lemma bchOcticTerm_norm_le (a b : 𝔸) (s : ℝ)
    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :
    ∀ i : Fin 124, ‖bchOcticTerm (𝕂 := 𝕂) a b i‖ ≤ (432 / 120960 : ℝ) * s^8 := fun i =>
  match i with
  | ⟨0, _⟩ =>
    show ‖(2 / 120960 : 𝕂) • (a * a * a * a * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a a a b b s ha ha ha ha ha ha hb hb (by norm_num) hs
  | ⟨1, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * a * a * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a a b a b s ha ha ha ha ha hb ha hb (by norm_num) hs
  | ⟨2, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * a * a * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a a b b b s ha ha ha ha ha hb hb hb (by norm_num) hs
  | ⟨3, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * a * a * a * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b a a b s ha ha ha ha hb ha ha hb (by norm_num) hs
  | ⟨4, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * a * a * a * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b a b b s ha ha ha ha hb ha hb hb (by norm_num) hs
  | ⟨5, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * a * a * a * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b b a b s ha ha ha ha hb hb ha hb (by norm_num) hs
  | ⟨6, _⟩ =>
    show ‖(23 / 120960 : 𝕂) • (a * a * a * a * b * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (23 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a a b b b b s ha ha ha ha hb hb hb hb (by norm_num) hs
  | ⟨7, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (a * a * a * b * a * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a a a b s ha ha ha hb ha ha ha hb (by norm_num) hs
  | ⟨8, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * a * b * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a a b b s ha ha ha hb ha ha hb hb (by norm_num) hs
  | ⟨9, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (a * a * a * b * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a b a b s ha ha ha hb ha hb ha hb (by norm_num) hs
  | ⟨10, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (a * a * a * b * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b a b b b s ha ha ha hb ha hb hb hb (by norm_num) hs
  | ⟨11, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * a * b * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b a a b s ha ha ha hb hb ha ha hb (by norm_num) hs
  | ⟨12, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * a * b * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b a b b s ha ha ha hb hb ha hb hb (by norm_num) hs
  | ⟨13, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (a * a * a * b * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b b a b s ha ha ha hb hb hb ha hb (by norm_num) hs
  | ⟨14, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * a * b * b * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a a b b b b b s ha ha ha hb hb hb hb hb (by norm_num) hs
  | ⟨15, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * a * b * a * a * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a a a b s ha ha hb ha ha ha ha hb (by norm_num) hs
  | ⟨16, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * b * a * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a a b b s ha ha hb ha ha ha hb hb (by norm_num) hs
  | ⟨17, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * a * b * a * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a b a b s ha ha hb ha ha hb ha hb (by norm_num) hs
  | ⟨18, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * b * a * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a a b b b s ha ha hb ha ha hb hb hb (by norm_num) hs
  | ⟨19, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * a * b * a * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b a a b s ha ha hb ha hb ha ha hb (by norm_num) hs
  | ⟨20, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * a * b * a * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b a b b s ha ha hb ha hb ha hb hb (by norm_num) hs
  | ⟨21, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * a * b * a * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b b a b s ha ha hb ha hb hb ha hb (by norm_num) hs
  | ⟨22, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * a * b * a * b * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b a b b b b s ha ha hb ha hb hb hb hb (by norm_num) hs
  | ⟨23, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * b * b * a * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a a a b s ha ha hb hb ha ha ha hb (by norm_num) hs
  | ⟨24, _⟩ =>
    show ‖(-54 / 120960 : 𝕂) • (a * a * b * b * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-54 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a a b b s ha ha hb hb ha ha hb hb (by norm_num) hs
  | ⟨25, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * a * b * b * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a b a b s ha ha hb hb ha hb ha hb (by norm_num) hs
  | ⟨26, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * b * b * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b a b b b s ha ha hb hb ha hb hb hb (by norm_num) hs
  | ⟨27, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * b * b * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b a a b s ha ha hb hb hb ha ha hb (by norm_num) hs
  | ⟨28, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * a * b * b * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b a b b s ha ha hb hb hb ha hb hb (by norm_num) hs
  | ⟨29, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * a * b * b * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b b a b s ha ha hb hb hb hb ha hb (by norm_num) hs
  | ⟨30, _⟩ =>
    show ‖(2 / 120960 : 𝕂) • (a * a * b * b * b * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a a b b b b b b s ha ha hb hb hb hb hb hb (by norm_num) hs
  | ⟨31, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * b * a * a * a * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a a a b s ha hb ha ha ha ha ha hb (by norm_num) hs
  | ⟨32, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * b * a * a * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a a b b s ha hb ha ha ha ha hb hb (by norm_num) hs
  | ⟨33, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (a * b * a * a * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a b a b s ha hb ha ha ha hb ha hb (by norm_num) hs
  | ⟨34, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (a * b * a * a * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a a b b b s ha hb ha ha ha hb hb hb (by norm_num) hs
  | ⟨35, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * a * a * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b a a b s ha hb ha ha hb ha ha hb (by norm_num) hs
  | ⟨36, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * a * a * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b a b b s ha hb ha ha hb ha hb hb (by norm_num) hs
  | ⟨37, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * a * a * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b b a b s ha hb ha ha hb hb ha hb (by norm_num) hs
  | ⟨38, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * b * a * a * b * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a a b b b b s ha hb ha ha hb hb hb hb (by norm_num) hs
  | ⟨39, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (a * b * a * b * a * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a a a b s ha hb ha hb ha ha ha hb (by norm_num) hs
  | ⟨40, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * a * b * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a a b b s ha hb ha hb ha ha hb hb (by norm_num) hs
  | ⟨41, _⟩ =>
    show ‖(-432 / 120960 : 𝕂) • (a * b * a * b * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-432 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a b a b s ha hb ha hb ha hb ha hb (by norm_num) hs
  | ⟨42, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (a * b * a * b * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b a b b b s ha hb ha hb ha hb hb hb (by norm_num) hs
  | ⟨43, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * a * b * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b a a b s ha hb ha hb hb ha ha hb (by norm_num) hs
  | ⟨44, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * a * b * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b a b b s ha hb ha hb hb ha hb hb (by norm_num) hs
  | ⟨45, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (a * b * a * b * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b b a b s ha hb ha hb hb hb ha hb (by norm_num) hs
  | ⟨46, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * b * a * b * b * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b a b b b b b s ha hb ha hb hb hb hb hb (by norm_num) hs
  | ⟨47, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * b * b * a * a * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a a a b s ha hb hb ha ha ha ha hb (by norm_num) hs
  | ⟨48, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * b * b * a * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a a b b s ha hb hb ha ha ha hb hb (by norm_num) hs
  | ⟨49, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * b * a * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a b a b s ha hb hb ha ha hb ha hb (by norm_num) hs
  | ⟨50, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * b * b * a * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a a b b b s ha hb hb ha ha hb hb hb (by norm_num) hs
  | ⟨51, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * b * a * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b a a b s ha hb hb ha hb ha ha hb (by norm_num) hs
  | ⟨52, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * b * a * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b a b b s ha hb hb ha hb ha hb hb (by norm_num) hs
  | ⟨53, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (a * b * b * a * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b b a b s ha hb hb ha hb hb ha hb (by norm_num) hs
  | ⟨54, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * b * b * a * b * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b a b b b b s ha hb hb ha hb hb hb hb (by norm_num) hs
  | ⟨55, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (a * b * b * b * a * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a a a b s ha hb hb hb ha ha ha hb (by norm_num) hs
  | ⟨56, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * b * b * b * a * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a a b b s ha hb hb hb ha ha hb hb (by norm_num) hs
  | ⟨57, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (a * b * b * b * a * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a b a b s ha hb hb hb ha hb ha hb (by norm_num) hs
  | ⟨58, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (a * b * b * b * a * b * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b a b b b s ha hb hb hb ha hb hb hb (by norm_num) hs
  | ⟨59, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * b * b * b * b * a * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b b a a b s ha hb hb hb hb ha ha hb (by norm_num) hs
  | ⟨60, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (a * b * b * b * b * a * b * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b b a b b s ha hb hb hb hb ha hb hb (by norm_num) hs
  | ⟨61, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (a * b * b * b * b * b * a * b)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        a b b b b b a b s ha hb hb hb hb hb ha hb (by norm_num) hs
  | ⟨62, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * a * a * a * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a a a b a s hb ha ha ha ha ha hb ha (by norm_num) hs
  | ⟨63, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * a * a * a * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a a b a a s hb ha ha ha ha hb ha ha (by norm_num) hs
  | ⟨64, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * a * a * a * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a a b b a s hb ha ha ha ha hb hb ha (by norm_num) hs
  | ⟨65, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (b * a * a * a * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b a a a s hb ha ha ha hb ha ha ha (by norm_num) hs
  | ⟨66, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (b * a * a * a * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b a b a s hb ha ha ha hb ha hb ha (by norm_num) hs
  | ⟨67, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * a * a * a * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b b a a s hb ha ha ha hb hb ha ha (by norm_num) hs
  | ⟨68, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (b * a * a * a * b * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a a b b b a s hb ha ha ha hb hb hb ha (by norm_num) hs
  | ⟨69, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * a * a * b * a * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a a a a s hb ha ha hb ha ha ha ha (by norm_num) hs
  | ⟨70, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * a * b * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a a b a s hb ha ha hb ha ha hb ha (by norm_num) hs
  | ⟨71, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * a * b * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a b a a s hb ha ha hb ha hb ha ha (by norm_num) hs
  | ⟨72, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * a * b * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b a b b a s hb ha ha hb ha hb hb ha (by norm_num) hs
  | ⟨73, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * a * a * b * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b a a a s hb ha ha hb hb ha ha ha (by norm_num) hs
  | ⟨74, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * a * b * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b a b a s hb ha ha hb hb ha hb ha (by norm_num) hs
  | ⟨75, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * a * a * b * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b b a a s hb ha ha hb hb hb ha ha (by norm_num) hs
  | ⟨76, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * a * a * b * b * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a a b b b b a s hb ha ha hb hb hb hb ha (by norm_num) hs
  | ⟨77, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * a * b * a * a * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a a a a s hb ha hb ha ha ha ha ha (by norm_num) hs
  | ⟨78, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (b * a * b * a * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a a b a s hb ha hb ha ha ha hb ha (by norm_num) hs
  | ⟨79, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * b * a * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a b a a s hb ha hb ha ha hb ha ha (by norm_num) hs
  | ⟨80, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * b * a * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a a b b a s hb ha hb ha ha hb hb ha (by norm_num) hs
  | ⟨81, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (b * a * b * a * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b a a a s hb ha hb ha hb ha ha ha (by norm_num) hs
  | ⟨82, _⟩ =>
    show ‖(432 / 120960 : 𝕂) • (b * a * b * a * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (432 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b a b a s hb ha hb ha hb ha hb ha (by norm_num) hs
  | ⟨83, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * b * a * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b b a a s hb ha hb ha hb hb ha ha (by norm_num) hs
  | ⟨84, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (b * a * b * a * b * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b a b b b a s hb ha hb ha hb hb hb ha (by norm_num) hs
  | ⟨85, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * a * b * b * a * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a a a a s hb ha hb hb ha ha ha ha (by norm_num) hs
  | ⟨86, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * b * b * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a a b a s hb ha hb hb ha ha hb ha (by norm_num) hs
  | ⟨87, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * b * b * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a b a a s hb ha hb hb ha hb ha ha (by norm_num) hs
  | ⟨88, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * a * b * b * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b a b b a s hb ha hb hb ha hb hb ha (by norm_num) hs
  | ⟨89, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (b * a * b * b * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b a a a s hb ha hb hb hb ha ha ha (by norm_num) hs
  | ⟨90, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (b * a * b * b * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b a b a s hb ha hb hb hb ha hb ha (by norm_num) hs
  | ⟨91, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * a * b * b * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b b a a s hb ha hb hb hb hb ha ha (by norm_num) hs
  | ⟨92, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * a * b * b * b * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b a b b b b b a s hb ha hb hb hb hb hb ha (by norm_num) hs
  | ⟨93, _⟩ =>
    show ‖(-2 / 120960 : 𝕂) • (b * b * a * a * a * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a a a a s hb hb ha ha ha ha ha ha (by norm_num) hs
  | ⟨94, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * b * a * a * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a a b a s hb hb ha ha ha ha hb ha (by norm_num) hs
  | ⟨95, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * a * a * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a b a a s hb hb ha ha ha hb ha ha (by norm_num) hs
  | ⟨96, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * a * a * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a a b b a s hb hb ha ha ha hb hb ha (by norm_num) hs
  | ⟨97, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * a * a * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b a a a s hb hb ha ha hb ha ha ha (by norm_num) hs
  | ⟨98, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * b * a * a * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b a b a s hb hb ha ha hb ha hb ha (by norm_num) hs
  | ⟨99, _⟩ =>
    show ‖(54 / 120960 : 𝕂) • (b * b * a * a * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (54 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b b a a s hb hb ha ha hb hb ha ha (by norm_num) hs
  | ⟨100, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * a * a * b * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a a b b b a s hb hb ha ha hb hb hb ha (by norm_num) hs
  | ⟨101, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * b * a * b * a * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a a a a s hb hb ha hb ha ha ha ha (by norm_num) hs
  | ⟨102, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * b * a * b * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a a b a s hb hb ha hb ha ha hb ha (by norm_num) hs
  | ⟨103, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * b * a * b * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a b a a s hb hb ha hb ha hb ha ha (by norm_num) hs
  | ⟨104, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * b * a * b * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b a b b a s hb hb ha hb ha hb hb ha (by norm_num) hs
  | ⟨105, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * a * b * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b a a a s hb hb ha hb hb ha ha ha (by norm_num) hs
  | ⟨106, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (b * b * a * b * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b a b a s hb hb ha hb hb ha hb ha (by norm_num) hs
  | ⟨107, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * a * b * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b b a a s hb hb ha hb hb hb ha ha (by norm_num) hs
  | ⟨108, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * b * a * b * b * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b a b b b b a s hb hb ha hb hb hb hb ha (by norm_num) hs
  | ⟨109, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * b * a * a * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a a a a s hb hb hb ha ha ha ha ha (by norm_num) hs
  | ⟨110, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (b * b * b * a * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a a b a s hb hb hb ha ha ha hb ha (by norm_num) hs
  | ⟨111, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * b * a * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a b a a s hb hb hb ha ha hb ha ha (by norm_num) hs
  | ⟨112, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * b * a * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a a b b a s hb hb hb ha ha hb hb ha (by norm_num) hs
  | ⟨113, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (b * b * b * a * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b a a a s hb hb hb ha hb ha ha ha (by norm_num) hs
  | ⟨114, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (b * b * b * a * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b a b a s hb hb hb ha hb ha hb ha (by norm_num) hs
  | ⟨115, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * b * a * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b b a a s hb hb hb ha hb hb ha ha (by norm_num) hs
  | ⟨116, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (b * b * b * a * b * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b a b b b a s hb hb hb ha hb hb hb ha (by norm_num) hs
  | ⟨117, _⟩ =>
    show ‖(-23 / 120960 : 𝕂) • (b * b * b * b * a * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-23 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a a a a s hb hb hb hb ha ha ha ha (by norm_num) hs
  | ⟨118, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * b * b * b * a * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a a b a s hb hb hb hb ha ha hb ha (by norm_num) hs
  | ⟨119, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * b * b * b * a * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a b a a s hb hb hb hb ha hb ha ha (by norm_num) hs
  | ⟨120, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (b * b * b * b * a * b * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b a b b a s hb hb hb hb ha hb hb ha (by norm_num) hs
  | ⟨121, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * b * b * b * a * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b b a a a s hb hb hb hb hb ha ha ha (by norm_num) hs
  | ⟨122, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (b * b * b * b * b * a * b * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b b a b a s hb hb hb hb hb ha hb ha (by norm_num) hs
  | ⟨123, _⟩ =>
    show ‖(-2 / 120960 : 𝕂) • (b * b * b * b * b * b * a * a)‖ ≤ (432 / 120960 : ℝ) * s^8 from
      deg8_smul_word_le_basic (-2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        b b b b b b a a s hb hb hb hb hb hb ha ha (by norm_num) hs
  | ⟨_ + 124, h⟩ => absurd h (by omega)

set_option maxHeartbeats 800000 in
/-- **Norm bound for `bch_octic_term`**: `‖Z₈(a, b)‖ ≤ (‖a‖+‖b‖)⁸`.

The actual Σ|coef|/120960 = 5970/120960 = 199/4032 ≈ 0.049355 (tight).
The proof uses a uniform per-i bound `432/120960` (max |scaled coef|),
giving `Σ ≤ 124·432/120960 = 53568/120960 = 31/70 ≤ 1`. -/
theorem norm_bch_octic_term_le (a b : 𝔸) :
    ‖bch_octic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 8 := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]
  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]
  have hs8_nn : 0 ≤ s ^ 8 := pow_nonneg hs_nn 8
  rw [bch_octic_term_eq_sum]
  calc ‖∑ i : Fin 124, bchOcticTerm (𝕂 := 𝕂) a b i‖
      ≤ ∑ i : Fin 124, ‖bchOcticTerm (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 124, (432 / 120960 : ℝ) * s^8 :=
        Finset.sum_le_sum (fun i _ => bchOcticTerm_norm_le (𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)
    _ = 124 * ((432 / 120960 : ℝ) * s^8) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ 1 * s^8 := by nlinarith [hs8_nn]
    _ = s ^ 8 := one_mul _

/-! ### `bch_octic_term` vanishes on `(α•V, β•V)` inputs

By the same source as `bch_septic_term_apply_smul_smul`: when both
arguments are scalar multiples of a single element `V`, the BCH series
`log(exp(α•V)·exp(β•V)) = (α+β)•V` (V commutes with itself), so every
τ⁸ Taylor coefficient at pure-V inputs must vanish:

  `bch_octic_term 𝕂 (α • V) (β • V) = 0`.

Foundation for the future `nonic_pure_identity` (deg-8 cancellation
algebraic identity at substituted polynomials, the deg-9 analog of
`septic_pure_identity` from session 18 — used in the deg-9-precision
small-s discharge mirroring stepping stone 2's `norm_bch_septic_remainder_small_s_le`). -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **8-fold smul-mul absorption (single element)**: 8 factors each of
the form `sᵢ • V` collapse to `(s₁·…·s₈) • V⁸`. -/
private lemma bch_octic_term_eight_fold_smul_mul_eq (V : 𝔸)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : 𝕂) :
    (s₁ • V) * (s₂ • V) * (s₃ • V) * (s₄ • V) * (s₅ • V) * (s₆ • V) * (s₇ • V) * (s₈ • V) =
      (s₁ * s₂ * s₃ * s₄ * s₅ * s₆ * s₇ * s₈) • (V * V * V * V * V * V * V * V) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1; ring

set_option maxHeartbeats 4000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Vanishing on scalar•V inputs**:
`bch_octic_term 𝕂 (α • V) (β • V) = 0` for any `α, β : 𝕂` and `V : 𝔸`.

Source: `log(exp(αV)·exp(βV)) = (α+β)V` (V commutes with itself, so all
nested commutators vanish). Every τ⁸ Taylor coefficient at pure-V inputs
must vanish identically as a polynomial in (α, β).

Proof template mirrors `bch_septic_term_apply_smul_smul` at one degree higher:
1. Collapse each 8-fold product `(αV)^k·(βV)^(8−k)` to `(α^k·β^(8−k)) • V⁸`.
2. Combine the 124 word coefficients into a single polynomial in (α, β)
   times `V⁸`.
3. The polynomial-in-(α, β) identity (each `(k, 8−k)` partial sum is 0)
   is closed by `ring`. -/
theorem bch_octic_term_apply_smul_smul (V : 𝔸) (α β : 𝕂) :
    bch_octic_term 𝕂 (α • V) (β • V) = 0 := by
  unfold bch_octic_term
  -- Step 1: collapse each 8-fold product to (scalar) • V⁸; combine outer scalars.
  simp only [bch_octic_term_eight_fold_smul_mul_eq, smul_smul, ← add_smul]
  -- Step 2: goal is now `(big_polynomial in α, β) • V⁸ = 0`.
  conv_rhs => rw [show (0 : 𝔸) = (0 : 𝕂) • (V * V * V * V * V * V * V * V) from
    (zero_smul _ _).symm]
  congr 1
  -- Polynomial-in-(α, β) identity: each (k, 8−k) coefficient group sums to 0.
  ring

/-! ### Lipschitz bound for `bch_octic_term`

Analog of `norm_bch_septic_term_diff_le` (session 28) at one degree higher;
the deg-8 BCH coefficient is Lipschitz in its first argument:
  `‖Z₈(z, y) − Z₈(x, y)‖ ≤ 8 · M⁷ · ‖z − x‖`, `M = ‖z‖+‖x‖+‖y‖`.

Completes the `bch_octic_term` infrastructure quartet (def + norm bound +
vanishing + Lipschitz) for stepping stone 1
(`symmetric_bch_septic_sub_poly_axiom`) discharge. -/

set_option maxHeartbeats 1600000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **8-letter product Lipschitz** (local copy, deg-9 analog of `word_7_diff_le_basic`):
`‖x₁·…·x₈ − y₁·…·y₈‖ ≤ N⁷·Σᵢ ‖xᵢ−yᵢ‖` when `‖xᵢ‖, ‖yᵢ‖ ≤ N`. -/
private lemma word_8_diff_le_basic
    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : 𝔸) (N : ℝ)
    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)
    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N) (hx₈ : ‖x₈‖ ≤ N)
    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)
    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N) (hy₈ : ‖y₈‖ ≤ N) (hN_nn : 0 ≤ N) :
    ‖x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * y₈‖ ≤
      N ^ 7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) := by
  have hid : x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * y₈ =
      (x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +
      y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +
      y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈ +
      y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈ +
      y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈ +
      y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈ +
      y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈ +
      y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈) := by noncomm_ring
  rw [hid]
  have hN_pow_nn : (0 : ℝ) ≤ N ^ 7 := pow_nonneg hN_nn 7
  have ht1 : ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖ ≤ N ^ 7 * ‖x₁ - y₁‖ := by
    calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖
        ≤ ‖x₁ - y₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ * ‖x₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ ‖x₁ - y₁‖ * N * N * N * N * N * N * N := by gcongr
      _ = N ^ 7 * ‖x₁ - y₁‖ := by ring
  have ht2 : ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖ ≤ N ^ 7 * ‖x₂ - y₂‖ := by
    calc ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖
        ≤ ‖y₁‖ * ‖x₂ - y₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ * ‖x₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ N * ‖x₂ - y₂‖ * N * N * N * N * N * N := by gcongr
      _ = N ^ 7 * ‖x₂ - y₂‖ := by ring
  have ht3 : ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈‖ ≤ N ^ 7 * ‖x₃ - y₃‖ := by
    calc ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖x₃ - y₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ * ‖x₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ N * N * ‖x₃ - y₃‖ * N * N * N * N * N := by gcongr
      _ = N ^ 7 * ‖x₃ - y₃‖ := by ring
  have ht4 : ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈‖ ≤ N ^ 7 * ‖x₄ - y₄‖ := by
    calc ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖x₄ - y₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ * ‖x₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ N * N * N * ‖x₄ - y₄‖ * N * N * N * N := by gcongr
      _ = N ^ 7 * ‖x₄ - y₄‖ := by ring
  have ht5 : ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈‖ ≤ N ^ 7 * ‖x₅ - y₅‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖x₅ - y₅‖ * ‖x₆‖ * ‖x₇‖ * ‖x₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ N * N * N * N * ‖x₅ - y₅‖ * N * N * N := by gcongr
      _ = N ^ 7 * ‖x₅ - y₅‖ := by ring
  have ht6 : ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈‖ ≤ N ^ 7 * ‖x₆ - y₆‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖y₅‖ * ‖x₆ - y₆‖ * ‖x₇‖ * ‖x₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ N * N * N * N * N * ‖x₆ - y₆‖ * N * N := by gcongr
      _ = N ^ 7 * ‖x₆ - y₆‖ := by ring
  have ht7 : ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈‖ ≤ N ^ 7 * ‖x₇ - y₇‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖y₅‖ * ‖y₆‖ * ‖x₇ - y₇‖ * ‖x₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ N * N * N * N * N * N * ‖x₇ - y₇‖ * N := by gcongr
      _ = N ^ 7 * ‖x₇ - y₇‖ := by ring
  have ht8 : ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈)‖ ≤ N ^ 7 * ‖x₈ - y₈‖ := by
    calc ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈)‖
        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖y₅‖ * ‖y₆‖ * ‖y₇‖ * ‖x₈ - y₈‖ := norm_8prod_le _ _ _ _ _ _ _ _
      _ ≤ N * N * N * N * N * N * N * ‖x₈ - y₈‖ := by gcongr
      _ = N ^ 7 * ‖x₈ - y₈‖ := by ring
  calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +
        y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +
        y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈ +
        y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈ +
        y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈ +
        y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈ +
        y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈ +
        y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈)‖
      ≤ ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖ +
          ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖ +
          ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈‖ +
          ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈‖ +
          ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈‖ +
          ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈‖ +
          ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈‖ +
          ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈)‖ := by
        have a1 := norm_add_le
              (((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈) + (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈))
              (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈))
        have a2 := norm_add_le
              (((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈))
              (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈)
        have a3 := norm_add_le
              (((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈))
              (y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈)
        have a4 := norm_add_le
              (((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈))
              (y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈)
        have a5 := norm_add_le
              (((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈))
              (y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈)
        have a6 := norm_add_le
              (((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) + (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈))
              (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈)
        have a7 := norm_add_le
              (((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈))
              (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈)
        linarith
    _ ≤ N ^ 7 * ‖x₁ - y₁‖ + N ^ 7 * ‖x₂ - y₂‖ + N ^ 7 * ‖x₃ - y₃‖ + N ^ 7 * ‖x₄ - y₄‖ + N ^ 7 * ‖x₅ - y₅‖ + N ^ 7 * ‖x₆ - y₆‖ + N ^ 7 * ‖x₇ - y₇‖ + N ^ 7 * ‖x₈ - y₈‖ := by
        linarith [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]
    _ = N ^ 7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Scaled 8-letter Lipschitz** (local copy, deg-9 analog of `deg7_smul_word_diff_le_basic`):
`‖c•(x₁·…·x₈) − c•(y₁·…·y₈)‖ ≤ cb·8·N⁷·D` when `‖c‖ ≤ cb`, all `‖xᵢ‖, ‖yᵢ‖ ≤ N`, all `‖xᵢ-yᵢ‖ ≤ D`. -/
private lemma deg8_smul_word_diff_le_basic
    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)
    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : 𝔸) (N D : ℝ)
    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)
    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N) (hx₈ : ‖x₈‖ ≤ N)
    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)
    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N) (hy₈ : ‖y₈‖ ≤ N)
    (hd₁ : ‖x₁ - y₁‖ ≤ D) (hd₂ : ‖x₂ - y₂‖ ≤ D) (hd₃ : ‖x₃ - y₃‖ ≤ D) (hd₄ : ‖x₄ - y₄‖ ≤ D)
    (hd₅ : ‖x₅ - y₅‖ ≤ D) (hd₆ : ‖x₆ - y₆‖ ≤ D) (hd₇ : ‖x₇ - y₇‖ ≤ D) (hd₈ : ‖x₈ - y₈‖ ≤ D)
    (hcb : 0 ≤ cb) (hN_nn : 0 ≤ N) (hD_nn : 0 ≤ D) :
    ‖c • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) - c • (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * y₈)‖ ≤
      cb * 8 * N^7 * D := by
  rw [← smul_sub]
  have hwd : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ ≤
             N^7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) :=
    word_8_diff_le_basic x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ hx₇ hx₈ hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hy₇ hy₈ hN_nn
  have hwd_bound : N^7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) ≤
             8 * N^7 * D := by
    have hN7_nn : 0 ≤ N^7 := pow_nonneg hN_nn 7
    nlinarith [hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇, hd₈, hN7_nn]
  have hwd2 : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ ≤ 8 * N^7 * D := le_trans hwd hwd_bound
  have h_pos : 0 ≤ 8 * N^7 * D := by positivity
  calc ‖c • (x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈)‖
      ≤ ‖c‖ * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ := norm_smul_le _ _
    _ ≤ cb * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * (8 * N^7 * D) := mul_le_mul_of_nonneg_left hwd2 hcb
    _ = cb * 8 * N^7 * D := by ring

-- Per-i diff bound: `‖bchOcticTerm z y i − bchOcticTerm x y i‖ ≤ (432/120960) · 8 · M⁷ · ‖z−x‖`
-- (uniform over all 124 indices, since each word has ≤ 8 'a'-positions).
set_option maxHeartbeats 64000000 in
private lemma bchOcticTerm_diff_norm_le (z x y : 𝔸) (M : ℝ)
    (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM_nn : 0 ≤ M) :
    ∀ i : Fin 124, ‖bchOcticTerm (𝕂 := 𝕂) z y i -
                     bchOcticTerm (𝕂 := 𝕂) x y i‖ ≤
      (432 / 120960 : ℝ) * 8 * M^7 * ‖z - x‖ := by
  intro i
  set D := ‖z - x‖ with hD_def
  have hD_nn : 0 ≤ D := norm_nonneg _
  have hzx_le_D : ‖z - x‖ ≤ D := le_refl _
  have hyy_le_D : ‖y - y‖ ≤ D := by rw [sub_self, norm_zero]; exact hD_nn
  match i with
  | ⟨0, _⟩ =>
    show ‖(2 / 120960 : 𝕂) • (z * z * z * z * z * z * y * y) - (2 / 120960 : 𝕂) • (x * x * x * x * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z z z y y
        x x x x x x y y
        M D
        hz hz hz hz hz hz hy hy
        hx hx hx hx hx hx hy hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨1, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * z * z * z * y * z * y) - (-12 / 120960 : 𝕂) • (x * x * x * x * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z z y z y
        x x x x x y x y
        M D
        hz hz hz hz hz hy hz hy
        hx hx hx hx hx hy hx hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨2, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * z * z * z * y * y * y) - (-12 / 120960 : 𝕂) • (x * x * x * x * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z z y y y
        x x x x x y y y
        M D
        hz hz hz hz hz hy hy hy
        hx hx hx hx hx hy hy hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨3, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * z * z * z * y * z * z * y) - (30 / 120960 : 𝕂) • (x * x * x * x * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y z z y
        x x x x y x x y
        M D
        hz hz hz hz hy hz hz hy
        hx hx hx hx hy hx hx hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨4, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * z * z * z * y * z * y * y) - (30 / 120960 : 𝕂) • (x * x * x * x * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y z y y
        x x x x y x y y
        M D
        hz hz hz hz hy hz hy hy
        hx hx hx hx hy hx hy hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨5, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * z * z * z * y * y * z * y) - (30 / 120960 : 𝕂) • (x * x * x * x * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y y z y
        x x x x y y x y
        M D
        hz hz hz hz hy hy hz hy
        hx hx hx hx hy hy hx hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨6, _⟩ =>
    show ‖(23 / 120960 : 𝕂) • (z * z * z * z * y * y * y * y) - (23 / 120960 : 𝕂) • (x * x * x * x * y * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (23 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z z y y y y
        x x x x y y y y
        M D
        hz hz hz hz hy hy hy hy
        hx hx hx hx hy hy hy hy
        hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨7, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (z * z * z * y * z * z * z * y) - (-40 / 120960 : 𝕂) • (x * x * x * y * x * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z z z y
        x x x y x x x y
        M D
        hz hz hz hy hz hz hz hy
        hx hx hx hy hx hx hx hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨8, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * z * y * z * z * y * y) - (-12 / 120960 : 𝕂) • (x * x * x * y * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z z y y
        x x x y x x y y
        M D
        hz hz hz hy hz hz hy hy
        hx hx hx hy hx hx hy hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨9, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (z * z * z * y * z * y * z * y) - (-96 / 120960 : 𝕂) • (x * x * x * y * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z y z y
        x x x y x y x y
        M D
        hz hz hz hy hz hy hz hy
        hx hx hx hy hx hy hx hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨10, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (z * z * z * y * z * y * y * y) - (-40 / 120960 : 𝕂) • (x * x * x * y * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y z y y y
        x x x y x y y y
        M D
        hz hz hz hy hz hy hy hy
        hx hx hx hy hx hy hy hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨11, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * z * y * y * z * z * y) - (-12 / 120960 : 𝕂) • (x * x * x * y * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y z z y
        x x x y y x x y
        M D
        hz hz hz hy hy hz hz hy
        hx hx hx hy hy hx hx hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨12, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * z * y * y * z * y * y) - (-12 / 120960 : 𝕂) • (x * x * x * y * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y z y y
        x x x y y x y y
        M D
        hz hz hz hy hy hz hy hy
        hx hx hx hy hy hx hy hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨13, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (z * z * z * y * y * y * z * y) - (-40 / 120960 : 𝕂) • (x * x * x * y * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y y z y
        x x x y y y x y
        M D
        hz hz hz hy hy hy hz hy
        hx hx hx hy hy hy hx hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨14, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * z * y * y * y * y * y) - (-12 / 120960 : 𝕂) • (x * x * x * y * y * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z z y y y y y
        x x x y y y y y
        M D
        hz hz hz hy hy hy hy hy
        hx hx hx hy hy hy hy hy
        hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨15, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * z * y * z * z * z * z * y) - (30 / 120960 : 𝕂) • (x * x * y * x * x * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z z z y
        x x y x x x x y
        M D
        hz hz hy hz hz hz hz hy
        hx hx hy hx hx hx hx hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨16, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * y * z * z * z * y * y) - (-12 / 120960 : 𝕂) • (x * x * y * x * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z z y y
        x x y x x x y y
        M D
        hz hz hy hz hz hz hy hy
        hx hx hy hx hx hx hy hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨17, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * z * y * z * z * y * z * y) - (72 / 120960 : 𝕂) • (x * x * y * x * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z y z y
        x x y x x y x y
        M D
        hz hz hy hz hz hy hz hy
        hx hx hy hx hx hy hx hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨18, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * y * z * z * y * y * y) - (-12 / 120960 : 𝕂) • (x * x * y * x * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z z y y y
        x x y x x y y y
        M D
        hz hz hy hz hz hy hy hy
        hx hx hy hx hx hy hy hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨19, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * z * y * z * y * z * z * y) - (72 / 120960 : 𝕂) • (x * x * y * x * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y z z y
        x x y x y x x y
        M D
        hz hz hy hz hy hz hz hy
        hx hx hy hx hy hx hx hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨20, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * z * y * z * y * z * y * y) - (72 / 120960 : 𝕂) • (x * x * y * x * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y z y y
        x x y x y x y y
        M D
        hz hz hy hz hy hz hy hy
        hx hx hy hx hy hx hy hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨21, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * z * y * z * y * y * z * y) - (72 / 120960 : 𝕂) • (x * x * y * x * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y y z y
        x x y x y y x y
        M D
        hz hz hy hz hy hy hz hy
        hx hx hy hx hy hy hx hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨22, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * z * y * z * y * y * y * y) - (30 / 120960 : 𝕂) • (x * x * y * x * y * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y z y y y y
        x x y x y y y y
        M D
        hz hz hy hz hy hy hy hy
        hx hx hy hx hy hy hy hy
        hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨23, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * y * y * z * z * z * y) - (-12 / 120960 : 𝕂) • (x * x * y * y * x * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z z z y
        x x y y x x x y
        M D
        hz hz hy hy hz hz hz hy
        hx hx hy hy hx hx hx hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨24, _⟩ =>
    show ‖(-54 / 120960 : 𝕂) • (z * z * y * y * z * z * y * y) - (-54 / 120960 : 𝕂) • (x * x * y * y * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-54 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z z y y
        x x y y x x y y
        M D
        hz hz hy hy hz hz hy hy
        hx hx hy hy hx hx hy hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨25, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * z * y * y * z * y * z * y) - (72 / 120960 : 𝕂) • (x * x * y * y * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z y z y
        x x y y x y x y
        M D
        hz hz hy hy hz hy hz hy
        hx hx hy hy hx hy hx hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨26, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * y * y * z * y * y * y) - (-12 / 120960 : 𝕂) • (x * x * y * y * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y z y y y
        x x y y x y y y
        M D
        hz hz hy hy hz hy hy hy
        hx hx hy hy hx hy hy hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨27, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * y * y * y * z * z * y) - (-12 / 120960 : 𝕂) • (x * x * y * y * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y z z y
        x x y y y x x y
        M D
        hz hz hy hy hy hz hz hy
        hx hx hy hy hy hx hx hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨28, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * z * y * y * y * z * y * y) - (-12 / 120960 : 𝕂) • (x * x * y * y * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y z y y
        x x y y y x y y
        M D
        hz hz hy hy hy hz hy hy
        hx hx hy hy hy hx hy hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨29, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * z * y * y * y * y * z * y) - (30 / 120960 : 𝕂) • (x * x * y * y * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y y z y
        x x y y y y x y
        M D
        hz hz hy hy hy hy hz hy
        hx hx hy hy hy hy hx hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨30, _⟩ =>
    show ‖(2 / 120960 : 𝕂) • (z * z * y * y * y * y * y * y) - (2 / 120960 : 𝕂) • (x * x * y * y * y * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z z y y y y y y
        x x y y y y y y
        M D
        hz hz hy hy hy hy hy hy
        hx hx hy hy hy hy hy hy
        hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨31, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * y * z * z * z * z * z * y) - (-12 / 120960 : 𝕂) • (x * y * x * x * x * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z z z y
        x y x x x x x y
        M D
        hz hy hz hz hz hz hz hy
        hx hy hx hx hx hx hx hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨32, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * y * z * z * z * z * y * y) - (30 / 120960 : 𝕂) • (x * y * x * x * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z z y y
        x y x x x x y y
        M D
        hz hy hz hz hz hz hy hy
        hx hy hx hx hx hx hy hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨33, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (z * y * z * z * z * y * z * y) - (-96 / 120960 : 𝕂) • (x * y * x * x * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z y z y
        x y x x x y x y
        M D
        hz hy hz hz hz hy hz hy
        hx hy hx hx hx hy hx hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨34, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (z * y * z * z * z * y * y * y) - (-40 / 120960 : 𝕂) • (x * y * x * x * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z z y y y
        x y x x x y y y
        M D
        hz hy hz hz hz hy hy hy
        hx hy hx hx hx hy hy hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨35, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * z * z * y * z * z * y) - (72 / 120960 : 𝕂) • (x * y * x * x * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y z z y
        x y x x y x x y
        M D
        hz hy hz hz hy hz hz hy
        hx hy hx hx hy hx hx hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨36, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * z * z * y * z * y * y) - (72 / 120960 : 𝕂) • (x * y * x * x * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y z y y
        x y x x y x y y
        M D
        hz hy hz hz hy hz hy hy
        hx hy hx hx hy hx hy hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨37, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * z * z * y * y * z * y) - (72 / 120960 : 𝕂) • (x * y * x * x * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y y z y
        x y x x y y x y
        M D
        hz hy hz hz hy hy hz hy
        hx hy hx hx hy hy hx hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨38, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * y * z * z * y * y * y * y) - (30 / 120960 : 𝕂) • (x * y * x * x * y * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z z y y y y
        x y x x y y y y
        M D
        hz hy hz hz hy hy hy hy
        hx hy hx hx hy hy hy hy
        hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨39, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (z * y * z * y * z * z * z * y) - (-96 / 120960 : 𝕂) • (x * y * x * y * x * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z z z y
        x y x y x x x y
        M D
        hz hy hz hy hz hz hz hy
        hx hy hx hy hx hx hx hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨40, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * z * y * z * z * y * y) - (72 / 120960 : 𝕂) • (x * y * x * y * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z z y y
        x y x y x x y y
        M D
        hz hy hz hy hz hz hy hy
        hx hy hx hy hx hx hy hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨41, _⟩ =>
    show ‖(-432 / 120960 : 𝕂) • (z * y * z * y * z * y * z * y) - (-432 / 120960 : 𝕂) • (x * y * x * y * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-432 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z y z y
        x y x y x y x y
        M D
        hz hy hz hy hz hy hz hy
        hx hy hx hy hx hy hx hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨42, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (z * y * z * y * z * y * y * y) - (-96 / 120960 : 𝕂) • (x * y * x * y * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y z y y y
        x y x y x y y y
        M D
        hz hy hz hy hz hy hy hy
        hx hy hx hy hx hy hy hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨43, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * z * y * y * z * z * y) - (72 / 120960 : 𝕂) • (x * y * x * y * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y z z y
        x y x y y x x y
        M D
        hz hy hz hy hy hz hz hy
        hx hy hx hy hy hx hx hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨44, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * z * y * y * z * y * y) - (72 / 120960 : 𝕂) • (x * y * x * y * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y z y y
        x y x y y x y y
        M D
        hz hy hz hy hy hz hy hy
        hx hy hx hy hy hx hy hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨45, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (z * y * z * y * y * y * z * y) - (-96 / 120960 : 𝕂) • (x * y * x * y * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y y z y
        x y x y y y x y
        M D
        hz hy hz hy hy hy hz hy
        hx hy hx hy hy hy hx hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨46, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * y * z * y * y * y * y * y) - (-12 / 120960 : 𝕂) • (x * y * x * y * y * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y z y y y y y
        x y x y y y y y
        M D
        hz hy hz hy hy hy hy hy
        hx hy hx hy hy hy hy hy
        hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨47, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * y * y * z * z * z * z * y) - (30 / 120960 : 𝕂) • (x * y * y * x * x * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z z z y
        x y y x x x x y
        M D
        hz hy hy hz hz hz hz hy
        hx hy hy hx hx hx hx hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨48, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * y * y * z * z * z * y * y) - (-12 / 120960 : 𝕂) • (x * y * y * x * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z z y y
        x y y x x x y y
        M D
        hz hy hy hz hz hz hy hy
        hx hy hy hx hx hx hy hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨49, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * y * z * z * y * z * y) - (72 / 120960 : 𝕂) • (x * y * y * x * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z y z y
        x y y x x y x y
        M D
        hz hy hy hz hz hy hz hy
        hx hy hy hx hx hy hx hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨50, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * y * y * z * z * y * y * y) - (-12 / 120960 : 𝕂) • (x * y * y * x * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z z y y y
        x y y x x y y y
        M D
        hz hy hy hz hz hy hy hy
        hx hy hy hx hx hy hy hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨51, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * y * z * y * z * z * y) - (72 / 120960 : 𝕂) • (x * y * y * x * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y z z y
        x y y x y x x y
        M D
        hz hy hy hz hy hz hz hy
        hx hy hy hx hy hx hx hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨52, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * y * z * y * z * y * y) - (72 / 120960 : 𝕂) • (x * y * y * x * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y z y y
        x y y x y x y y
        M D
        hz hy hy hz hy hz hy hy
        hx hy hy hx hy hx hy hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨53, _⟩ =>
    show ‖(72 / 120960 : 𝕂) • (z * y * y * z * y * y * z * y) - (72 / 120960 : 𝕂) • (x * y * y * x * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y y z y
        x y y x y y x y
        M D
        hz hy hy hz hy hy hz hy
        hx hy hy hx hy hy hx hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨54, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * y * y * z * y * y * y * y) - (30 / 120960 : 𝕂) • (x * y * y * x * y * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y z y y y y
        x y y x y y y y
        M D
        hz hy hy hz hy hy hy hy
        hx hy hy hx hy hy hy hy
        hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨55, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (z * y * y * y * z * z * z * y) - (-40 / 120960 : 𝕂) • (x * y * y * y * x * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z z z y
        x y y y x x x y
        M D
        hz hy hy hy hz hz hz hy
        hx hy hy hy hx hx hx hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨56, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * y * y * y * z * z * y * y) - (-12 / 120960 : 𝕂) • (x * y * y * y * x * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z z y y
        x y y y x x y y
        M D
        hz hy hy hy hz hz hy hy
        hx hy hy hy hx hx hy hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨57, _⟩ =>
    show ‖(-96 / 120960 : 𝕂) • (z * y * y * y * z * y * z * y) - (-96 / 120960 : 𝕂) • (x * y * y * y * x * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z y z y
        x y y y x y x y
        M D
        hz hy hy hy hz hy hz hy
        hx hy hy hy hx hy hx hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨58, _⟩ =>
    show ‖(-40 / 120960 : 𝕂) • (z * y * y * y * z * y * y * y) - (-40 / 120960 : 𝕂) • (x * y * y * y * x * y * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y z y y y
        x y y y x y y y
        M D
        hz hy hy hy hz hy hy hy
        hx hy hy hy hx hy hy hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨59, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * y * y * y * y * z * z * y) - (30 / 120960 : 𝕂) • (x * y * y * y * y * x * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y y z z y
        x y y y y x x y
        M D
        hz hy hy hy hy hz hz hy
        hx hy hy hy hy hx hx hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨60, _⟩ =>
    show ‖(30 / 120960 : 𝕂) • (z * y * y * y * y * z * y * y) - (30 / 120960 : 𝕂) • (x * y * y * y * y * x * y * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y y z y y
        x y y y y x y y
        M D
        hz hy hy hy hy hz hy hy
        hx hy hy hy hy hx hy hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨61, _⟩ =>
    show ‖(-12 / 120960 : 𝕂) • (z * y * y * y * y * y * z * y) - (-12 / 120960 : 𝕂) • (x * y * y * y * y * y * x * y)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        z y y y y y z y
        x y y y y y x y
        M D
        hz hy hy hy hy hy hz hy
        hx hy hy hy hy hy hx hy
        hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨62, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * z * z * z * z * z * y * z) - (12 / 120960 : 𝕂) • (y * x * x * x * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z z z y z
        y x x x x x y x
        M D
        hy hz hz hz hz hz hy hz
        hy hx hx hx hx hx hy hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨63, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * z * z * z * z * y * z * z) - (-30 / 120960 : 𝕂) • (y * x * x * x * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z z y z z
        y x x x x y x x
        M D
        hy hz hz hz hz hy hz hz
        hy hx hx hx hx hy hx hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨64, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * z * z * z * z * y * y * z) - (-30 / 120960 : 𝕂) • (y * x * x * x * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z z y y z
        y x x x x y y x
        M D
        hy hz hz hz hz hy hy hz
        hy hx hx hx hx hy hy hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨65, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (y * z * z * z * y * z * z * z) - (40 / 120960 : 𝕂) • (y * x * x * x * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y z z z
        y x x x y x x x
        M D
        hy hz hz hz hy hz hz hz
        hy hx hx hx hy hx hx hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨66, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (y * z * z * z * y * z * y * z) - (96 / 120960 : 𝕂) • (y * x * x * x * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y z y z
        y x x x y x y x
        M D
        hy hz hz hz hy hz hy hz
        hy hx hx hx hy hx hy hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨67, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * z * z * z * y * y * z * z) - (12 / 120960 : 𝕂) • (y * x * x * x * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y y z z
        y x x x y y x x
        M D
        hy hz hz hz hy hy hz hz
        hy hx hx hx hy hy hx hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨68, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (y * z * z * z * y * y * y * z) - (40 / 120960 : 𝕂) • (y * x * x * x * y * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z z y y y z
        y x x x y y y x
        M D
        hy hz hz hz hy hy hy hz
        hy hx hx hx hy hy hy hx
        hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨69, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * z * z * y * z * z * z * z) - (-30 / 120960 : 𝕂) • (y * x * x * y * x * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z z z z
        y x x y x x x x
        M D
        hy hz hz hy hz hz hz hz
        hy hx hx hy hx hx hx hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨70, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * z * y * z * z * y * z) - (-72 / 120960 : 𝕂) • (y * x * x * y * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z z y z
        y x x y x x y x
        M D
        hy hz hz hy hz hz hy hz
        hy hx hx hy hx hx hy hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨71, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * z * y * z * y * z * z) - (-72 / 120960 : 𝕂) • (y * x * x * y * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z y z z
        y x x y x y x x
        M D
        hy hz hz hy hz hy hz hz
        hy hx hx hy hx hy hx hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨72, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * z * y * z * y * y * z) - (-72 / 120960 : 𝕂) • (y * x * x * y * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y z y y z
        y x x y x y y x
        M D
        hy hz hz hy hz hy hy hz
        hy hx hx hy hx hy hy hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨73, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * z * z * y * y * z * z * z) - (12 / 120960 : 𝕂) • (y * x * x * y * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y z z z
        y x x y y x x x
        M D
        hy hz hz hy hy hz hz hz
        hy hx hx hy hy hx hx hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨74, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * z * y * y * z * y * z) - (-72 / 120960 : 𝕂) • (y * x * x * y * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y z y z
        y x x y y x y x
        M D
        hy hz hz hy hy hz hy hz
        hy hx hx hy hy hx hy hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨75, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * z * z * y * y * y * z * z) - (12 / 120960 : 𝕂) • (y * x * x * y * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y y z z
        y x x y y y x x
        M D
        hy hz hz hy hy hy hz hz
        hy hx hx hy hy hy hx hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨76, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * z * z * y * y * y * y * z) - (-30 / 120960 : 𝕂) • (y * x * x * y * y * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z z y y y y z
        y x x y y y y x
        M D
        hy hz hz hy hy hy hy hz
        hy hx hx hy hy hy hy hx
        hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨77, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * z * y * z * z * z * z * z) - (12 / 120960 : 𝕂) • (y * x * y * x * x * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z z z z
        y x y x x x x x
        M D
        hy hz hy hz hz hz hz hz
        hy hx hy hx hx hx hx hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨78, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (y * z * y * z * z * z * y * z) - (96 / 120960 : 𝕂) • (y * x * y * x * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z z y z
        y x y x x x y x
        M D
        hy hz hy hz hz hz hy hz
        hy hx hy hx hx hx hy hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨79, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * y * z * z * y * z * z) - (-72 / 120960 : 𝕂) • (y * x * y * x * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z y z z
        y x y x x y x x
        M D
        hy hz hy hz hz hy hz hz
        hy hx hy hx hx hy hx hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨80, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * y * z * z * y * y * z) - (-72 / 120960 : 𝕂) • (y * x * y * x * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z z y y z
        y x y x x y y x
        M D
        hy hz hy hz hz hy hy hz
        hy hx hy hx hx hy hy hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨81, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (y * z * y * z * y * z * z * z) - (96 / 120960 : 𝕂) • (y * x * y * x * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y z z z
        y x y x y x x x
        M D
        hy hz hy hz hy hz hz hz
        hy hx hy hx hy hx hx hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨82, _⟩ =>
    show ‖(432 / 120960 : 𝕂) • (y * z * y * z * y * z * y * z) - (432 / 120960 : 𝕂) • (y * x * y * x * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (432 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y z y z
        y x y x y x y x
        M D
        hy hz hy hz hy hz hy hz
        hy hx hy hx hy hx hy hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨83, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * y * z * y * y * z * z) - (-72 / 120960 : 𝕂) • (y * x * y * x * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y y z z
        y x y x y y x x
        M D
        hy hz hy hz hy hy hz hz
        hy hx hy hx hy hy hx hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨84, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (y * z * y * z * y * y * y * z) - (96 / 120960 : 𝕂) • (y * x * y * x * y * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y z y y y z
        y x y x y y y x
        M D
        hy hz hy hz hy hy hy hz
        hy hx hy hx hy hy hy hx
        hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨85, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * z * y * y * z * z * z * z) - (-30 / 120960 : 𝕂) • (y * x * y * y * x * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z z z z
        y x y y x x x x
        M D
        hy hz hy hy hz hz hz hz
        hy hx hy hy hx hx hx hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨86, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * y * y * z * z * y * z) - (-72 / 120960 : 𝕂) • (y * x * y * y * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z z y z
        y x y y x x y x
        M D
        hy hz hy hy hz hz hy hz
        hy hx hy hy hx hx hy hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨87, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * y * y * z * y * z * z) - (-72 / 120960 : 𝕂) • (y * x * y * y * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z y z z
        y x y y x y x x
        M D
        hy hz hy hy hz hy hz hz
        hy hx hy hy hx hy hx hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨88, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * z * y * y * z * y * y * z) - (-72 / 120960 : 𝕂) • (y * x * y * y * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y z y y z
        y x y y x y y x
        M D
        hy hz hy hy hz hy hy hz
        hy hx hy hy hx hy hy hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨89, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (y * z * y * y * y * z * z * z) - (40 / 120960 : 𝕂) • (y * x * y * y * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y z z z
        y x y y y x x x
        M D
        hy hz hy hy hy hz hz hz
        hy hx hy hy hy hx hx hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨90, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (y * z * y * y * y * z * y * z) - (96 / 120960 : 𝕂) • (y * x * y * y * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y z y z
        y x y y y x y x
        M D
        hy hz hy hy hy hz hy hz
        hy hx hy hy hy hx hy hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨91, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * z * y * y * y * y * z * z) - (-30 / 120960 : 𝕂) • (y * x * y * y * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y y z z
        y x y y y y x x
        M D
        hy hz hy hy hy hy hz hz
        hy hx hy hy hy hy hx hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨92, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * z * y * y * y * y * y * z) - (12 / 120960 : 𝕂) • (y * x * y * y * y * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y z y y y y y z
        y x y y y y y x
        M D
        hy hz hy hy hy hy hy hz
        hy hx hy hy hy hy hy hx
        hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨93, _⟩ =>
    show ‖(-2 / 120960 : 𝕂) • (y * y * z * z * z * z * z * z) - (-2 / 120960 : 𝕂) • (y * y * x * x * x * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z z z z
        y y x x x x x x
        M D
        hy hy hz hz hz hz hz hz
        hy hy hx hx hx hx hx hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨94, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * y * z * z * z * z * y * z) - (-30 / 120960 : 𝕂) • (y * y * x * x * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z z y z
        y y x x x x y x
        M D
        hy hy hz hz hz hz hy hz
        hy hy hx hx hx hx hy hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨95, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * z * z * z * y * z * z) - (12 / 120960 : 𝕂) • (y * y * x * x * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z y z z
        y y x x x y x x
        M D
        hy hy hz hz hz hy hz hz
        hy hy hx hx hx hy hx hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨96, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * z * z * z * y * y * z) - (12 / 120960 : 𝕂) • (y * y * x * x * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z z y y z
        y y x x x y y x
        M D
        hy hy hz hz hz hy hy hz
        hy hy hx hx hx hy hy hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨97, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * z * z * y * z * z * z) - (12 / 120960 : 𝕂) • (y * y * x * x * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y z z z
        y y x x y x x x
        M D
        hy hy hz hz hy hz hz hz
        hy hy hx hx hy hx hx hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨98, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * y * z * z * y * z * y * z) - (-72 / 120960 : 𝕂) • (y * y * x * x * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y z y z
        y y x x y x y x
        M D
        hy hy hz hz hy hz hy hz
        hy hy hx hx hy hx hy hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨99, _⟩ =>
    show ‖(54 / 120960 : 𝕂) • (y * y * z * z * y * y * z * z) - (54 / 120960 : 𝕂) • (y * y * x * x * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (54 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y y z z
        y y x x y y x x
        M D
        hy hy hz hz hy hy hz hz
        hy hy hx hx hy hy hx hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨100, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * z * z * y * y * y * z) - (12 / 120960 : 𝕂) • (y * y * x * x * y * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z z y y y z
        y y x x y y y x
        M D
        hy hy hz hz hy hy hy hz
        hy hy hx hx hy hy hy hx
        hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨101, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * y * z * y * z * z * z * z) - (-30 / 120960 : 𝕂) • (y * y * x * y * x * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z z z z
        y y x y x x x x
        M D
        hy hy hz hy hz hz hz hz
        hy hy hx hy hx hx hx hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨102, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * y * z * y * z * z * y * z) - (-72 / 120960 : 𝕂) • (y * y * x * y * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z z y z
        y y x y x x y x
        M D
        hy hy hz hy hz hz hy hz
        hy hy hx hy hx hx hy hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨103, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * y * z * y * z * y * z * z) - (-72 / 120960 : 𝕂) • (y * y * x * y * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z y z z
        y y x y x y x x
        M D
        hy hy hz hy hz hy hz hz
        hy hy hx hy hx hy hx hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨104, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * y * z * y * z * y * y * z) - (-72 / 120960 : 𝕂) • (y * y * x * y * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y z y y z
        y y x y x y y x
        M D
        hy hy hz hy hz hy hy hz
        hy hy hx hy hx hy hy hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨105, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * z * y * y * z * z * z) - (12 / 120960 : 𝕂) • (y * y * x * y * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y z z z
        y y x y y x x x
        M D
        hy hy hz hy hy hz hz hz
        hy hy hx hy hy hx hx hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨106, _⟩ =>
    show ‖(-72 / 120960 : 𝕂) • (y * y * z * y * y * z * y * z) - (-72 / 120960 : 𝕂) • (y * y * x * y * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-72 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y z y z
        y y x y y x y x
        M D
        hy hy hz hy hy hz hy hz
        hy hy hx hy hy hx hy hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨107, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * z * y * y * y * z * z) - (12 / 120960 : 𝕂) • (y * y * x * y * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y y z z
        y y x y y y x x
        M D
        hy hy hz hy hy hy hz hz
        hy hy hx hy hy hy hx hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨108, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * y * z * y * y * y * y * z) - (-30 / 120960 : 𝕂) • (y * y * x * y * y * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y z y y y y z
        y y x y y y y x
        M D
        hy hy hz hy hy hy hy hz
        hy hy hx hy hy hy hy hx
        hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨109, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * y * z * z * z * z * z) - (12 / 120960 : 𝕂) • (y * y * y * x * x * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z z z z
        y y y x x x x x
        M D
        hy hy hy hz hz hz hz hz
        hy hy hy hx hx hx hx hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨110, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (y * y * y * z * z * z * y * z) - (40 / 120960 : 𝕂) • (y * y * y * x * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z z y z
        y y y x x x y x
        M D
        hy hy hy hz hz hz hy hz
        hy hy hy hx hx hx hy hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨111, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * y * z * z * y * z * z) - (12 / 120960 : 𝕂) • (y * y * y * x * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z y z z
        y y y x x y x x
        M D
        hy hy hy hz hz hy hz hz
        hy hy hy hx hx hy hx hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨112, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * y * z * z * y * y * z) - (12 / 120960 : 𝕂) • (y * y * y * x * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z z y y z
        y y y x x y y x
        M D
        hy hy hy hz hz hy hy hz
        hy hy hy hx hx hy hy hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨113, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (y * y * y * z * y * z * z * z) - (40 / 120960 : 𝕂) • (y * y * y * x * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y z z z
        y y y x y x x x
        M D
        hy hy hy hz hy hz hz hz
        hy hy hy hx hy hx hx hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨114, _⟩ =>
    show ‖(96 / 120960 : 𝕂) • (y * y * y * z * y * z * y * z) - (96 / 120960 : 𝕂) • (y * y * y * x * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (96 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y z y z
        y y y x y x y x
        M D
        hy hy hy hz hy hz hy hz
        hy hy hy hx hy hx hy hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨115, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * y * z * y * y * z * z) - (12 / 120960 : 𝕂) • (y * y * y * x * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y y z z
        y y y x y y x x
        M D
        hy hy hy hz hy hy hz hz
        hy hy hy hx hy hy hx hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨116, _⟩ =>
    show ‖(40 / 120960 : 𝕂) • (y * y * y * z * y * y * y * z) - (40 / 120960 : 𝕂) • (y * y * y * x * y * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (40 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y z y y y z
        y y y x y y y x
        M D
        hy hy hy hz hy hy hy hz
        hy hy hy hx hy hy hy hx
        hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨117, _⟩ =>
    show ‖(-23 / 120960 : 𝕂) • (y * y * y * y * z * z * z * z) - (-23 / 120960 : 𝕂) • (y * y * y * y * x * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-23 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z z z z
        y y y y x x x x
        M D
        hy hy hy hy hz hz hz hz
        hy hy hy hy hx hx hx hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨118, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * y * y * y * z * z * y * z) - (-30 / 120960 : 𝕂) • (y * y * y * y * x * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z z y z
        y y y y x x y x
        M D
        hy hy hy hy hz hz hy hz
        hy hy hy hy hx hx hy hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨119, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * y * y * y * z * y * z * z) - (-30 / 120960 : 𝕂) • (y * y * y * y * x * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z y z z
        y y y y x y x x
        M D
        hy hy hy hy hz hy hz hz
        hy hy hy hy hx hy hx hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨120, _⟩ =>
    show ‖(-30 / 120960 : 𝕂) • (y * y * y * y * z * y * y * z) - (-30 / 120960 : 𝕂) • (y * y * y * y * x * y * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-30 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y z y y z
        y y y y x y y x
        M D
        hy hy hy hy hz hy hy hz
        hy hy hy hy hx hy hy hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨121, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * y * y * y * z * z * z) - (12 / 120960 : 𝕂) • (y * y * y * y * y * x * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y y z z z
        y y y y y x x x
        M D
        hy hy hy hy hy hz hz hz
        hy hy hy hy hy hx hx hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨122, _⟩ =>
    show ‖(12 / 120960 : 𝕂) • (y * y * y * y * y * z * y * z) - (12 / 120960 : 𝕂) • (y * y * y * y * y * x * y * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (12 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y y z y z
        y y y y y x y x
        M D
        hy hy hy hy hy hz hy hz
        hy hy hy hy hy hx hy hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hyy_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨123, _⟩ =>
    show ‖(-2 / 120960 : 𝕂) • (y * y * y * y * y * y * z * z) - (-2 / 120960 : 𝕂) • (y * y * y * y * y * y * x * x)‖ ≤
         (432 / 120960 : ℝ) * 8 * M^7 * D
    exact deg8_smul_word_diff_le_basic (-2 / 120960 : 𝕂) (432 / 120960 : ℝ)
        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)
        y y y y y y z z
        y y y y y y x x
        M D
        hy hy hy hy hy hy hz hz
        hy hy hy hy hy hy hx hx
        hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hyy_le_D hzx_le_D hzx_le_D
        (by norm_num) hM_nn hD_nn
  | ⟨_ + 124, h⟩ => exact absurd h (by omega)

set_option maxHeartbeats 800000 in
/-- **Lipschitz bound for `bch_octic_term`**: `‖Z₈(z, y) − Z₈(x, y)‖ ≤ 8·M⁷·‖z−x‖`
where `M = ‖z‖+‖x‖+‖y‖`.

Analog of `norm_bch_septic_term_diff_le` (session 28) at one degree higher;
the deg-8 BCH coefficient is Lipschitz in its first argument.

With `z = (a'+b) + W` and `‖W‖ = O(s²)`, gives an O(s⁹·‖W‖) bound on
`‖C₈(z, y) − C₈(a'+b, y)‖`. Completes the `bch_octic_term` infrastructure
quartet (def + norm bound + vanishing + Lipschitz) for stepping stone 1.

The proof uses a uniform per-i bound `(432/120960) · 8 · M⁷ · ‖z−x‖`,
giving `Σ ≤ 124·432·8/120960 = 428544/120960 = 124/35 ≤ 8`. -/
theorem norm_bch_octic_term_diff_le (z x y : 𝔸) :
    ‖bch_octic_term 𝕂 z y - bch_octic_term 𝕂 x y‖ ≤
      8 * (‖z‖ + ‖x‖ + ‖y‖) ^ 7 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  have hM_nn : 0 ≤ M := by positivity
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have hM7_nn : 0 ≤ M^7 := pow_nonneg hM_nn 7
  have hzx_nn : 0 ≤ ‖z - x‖ := norm_nonneg _
  rw [bch_octic_term_eq_sum, bch_octic_term_eq_sum, ← Finset.sum_sub_distrib]
  calc ‖∑ i : Fin 124, (bchOcticTerm (𝕂 := 𝕂) z y i - bchOcticTerm (𝕂 := 𝕂) x y i)‖
      ≤ ∑ i : Fin 124, ‖bchOcticTerm (𝕂 := 𝕂) z y i - bchOcticTerm (𝕂 := 𝕂) x y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 124, (432 / 120960 : ℝ) * 8 * M^7 * ‖z - x‖ :=
        Finset.sum_le_sum (fun i _ => bchOcticTerm_diff_norm_le (𝕂 := 𝕂) z x y M hz_le hx_le hy_le hM_nn i)
    _ = 124 * ((432 / 120960 : ℝ) * 8 * M^7 * ‖z - x‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ 8 * M^7 * ‖z - x‖ := by nlinarith [hM7_nn, hzx_nn]

/-! #### Lipschitz bounds for `bch_sextic_term` per-word — sample (Phase A.2 of T2-F7e)

Per-word Lipschitz bounds: for each 6-letter word `w` in `bch_sextic_term`,
`‖w(z, y) − w(x, y)‖ ≤ k_w · M⁵ · ‖z−x‖` where `M = ‖z‖+‖x‖+‖y‖` and
`k_w` = number of a-positions in w. This sample contains the 4 words with
|coef|=1, demonstrating the technique that scales to all 28 words. -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Lipschitz bound for word #1 (a·a·a·a·b·b, 4 a-positions, |coef|=1). -/
private lemma bch_sextic_word01_diff_le (z x y : 𝔸) :
    ‖z * z * z * z * y * y - x * x * x * x * y * y‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * z * z * z * y * y - x * x * x * x * y * y =
      (z - x) * z * z * z * y * y + x * (z - x) * z * z * y * y +
      x * x * (z - x) * z * y * y + x * x * x * (z - x) * y * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 : ‖(z - x) * z * z * z * y * y‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖z - x‖ * ‖z‖ * ‖z‖ * ‖z‖ * ‖y‖ * ‖y‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ d * M * M * M * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h2 : ‖x * (z - x) * z * z * y * y‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖x‖ * ‖z - x‖ * ‖z‖ * ‖z‖ * ‖y‖ * ‖y‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * d * M * M * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h3 : ‖x * x * (z - x) * z * y * y‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖x‖ * ‖x‖ * ‖z - x‖ * ‖z‖ * ‖y‖ * ‖y‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * d * M * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h4 : ‖x * x * x * (z - x) * y * y‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖x‖ * ‖x‖ * ‖x‖ * ‖z - x‖ * ‖y‖ * ‖y‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * M * d * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  set s1 : 𝔸 := (z - x) * z * z * z * y * y
  set s2 : 𝔸 := x * (z - x) * z * z * y * y
  set s3 : 𝔸 := x * x * (z - x) * z * y * y
  set s4 : 𝔸 := x * x * x * (z - x) * y * y
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Lipschitz bound for word #7 (a·a·b·b·b·b, 2 a-positions, |coef|=1). -/
private lemma bch_sextic_word07_diff_le (z x y : 𝔸) :
    ‖z * z * y * y * y * y - x * x * y * y * y * y‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * z * y * y * y * y - x * x * y * y * y * y =
      (z - x) * z * y * y * y * y + x * (z - x) * y * y * y * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 : ‖(z - x) * z * y * y * y * y‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖z - x‖ * ‖z‖ * ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ d * M * M * M * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h2 : ‖x * (z - x) * y * y * y * y‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖x‖ * ‖z - x‖ * ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * d * M * M * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  set s1 : 𝔸 := (z - x) * z * y * y * y * y
  set s2 : 𝔸 := x * (z - x) * y * y * y * y
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Lipschitz bound for word #22 (b·b·a·a·a·a, 4 a-positions, |coef|=1). -/
private lemma bch_sextic_word22_diff_le (z x y : 𝔸) :
    ‖y * y * z * z * z * z - y * y * x * x * x * x‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * y * z * z * z * z - y * y * x * x * x * x =
      y * y * (z - x) * z * z * z + y * y * x * (z - x) * z * z +
      y * y * x * x * (z - x) * z + y * y * x * x * x * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 : ‖y * y * (z - x) * z * z * z‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖z - x‖ * ‖z‖ * ‖z‖ * ‖z‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * d * M * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h2 : ‖y * y * x * (z - x) * z * z‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖x‖ * ‖z - x‖ * ‖z‖ * ‖z‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * M * d * M * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h3 : ‖y * y * x * x * (z - x) * z‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖x‖ * ‖x‖ * ‖z - x‖ * ‖z‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * M * M * d * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h4 : ‖y * y * x * x * x * (z - x)‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖x‖ * ‖x‖ * ‖x‖ * ‖z - x‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * M * M * M * d := by gcongr
      _ = M ^ 5 * d := by ring
  set s1 : 𝔸 := y * y * (z - x) * z * z * z
  set s2 : 𝔸 := y * y * x * (z - x) * z * z
  set s3 : 𝔸 := y * y * x * x * (z - x) * z
  set s4 : 𝔸 := y * y * x * x * x * (z - x)
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Lipschitz bound for word #28 (b·b·b·b·a·a, 2 a-positions, |coef|=1). -/
private lemma bch_sextic_word28_diff_le (z x y : 𝔸) :
    ‖y * y * y * y * z * z - y * y * y * y * x * x‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * y * y * y * z * z - y * y * y * y * x * x =
      y * y * y * y * (z - x) * z + y * y * y * y * x * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 : ‖y * y * y * y * (z - x) * z‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ * ‖z - x‖ * ‖z‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * M * M * d * M := by gcongr
      _ = M ^ 5 * d := by ring
  have h2 : ‖y * y * y * y * x * (z - x)‖ ≤ M ^ 5 * d := by
    calc _ ≤ ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ * ‖x‖ * ‖z - x‖ := norm_6prod_le _ _ _ _ _ _
      _ ≤ M * M * M * M * M * d := by gcongr
      _ = M ^ 5 * d := by ring
  set s1 : 𝔸 := y * y * y * y * (z - x) * z
  set s2 : 𝔸 := y * y * y * y * x * (z - x)
  have a1 := norm_add_le s1 s2
  linarith

/-! #### Position helpers for `bch_sextic_term` per-word diffs -/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- 6-product norm bound when (z-x) is at position 1 and other 5 factors ≤ M. -/
private lemma norm_6prod_pos1_le (z x y A B C D E : 𝔸)
    (hA : ‖A‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hB : ‖B‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hC : ‖C‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hD : ‖D‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hE : ‖E‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) :
    ‖(z - x) * A * B * C * D * E‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  calc _ ≤ ‖z - x‖ * ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := norm_6prod_le _ _ _ _ _ _
    _ ≤ d * M * M * M * M * M := by gcongr
    _ = M ^ 5 * d := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma norm_6prod_pos2_le (z x y A B C D E : 𝔸)
    (hA : ‖A‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hB : ‖B‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hC : ‖C‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hD : ‖D‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hE : ‖E‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) :
    ‖A * (z - x) * B * C * D * E‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  calc _ ≤ ‖A‖ * ‖z - x‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := norm_6prod_le _ _ _ _ _ _
    _ ≤ M * d * M * M * M * M := by gcongr
    _ = M ^ 5 * d := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma norm_6prod_pos3_le (z x y A B C D E : 𝔸)
    (hA : ‖A‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hB : ‖B‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hC : ‖C‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hD : ‖D‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hE : ‖E‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) :
    ‖A * B * (z - x) * C * D * E‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  calc _ ≤ ‖A‖ * ‖B‖ * ‖z - x‖ * ‖C‖ * ‖D‖ * ‖E‖ := norm_6prod_le _ _ _ _ _ _
    _ ≤ M * M * d * M * M * M := by gcongr
    _ = M ^ 5 * d := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma norm_6prod_pos4_le (z x y A B C D E : 𝔸)
    (hA : ‖A‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hB : ‖B‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hC : ‖C‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hD : ‖D‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hE : ‖E‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) :
    ‖A * B * C * (z - x) * D * E‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  calc _ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖z - x‖ * ‖D‖ * ‖E‖ := norm_6prod_le _ _ _ _ _ _
    _ ≤ M * M * M * d * M * M := by gcongr
    _ = M ^ 5 * d := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma norm_6prod_pos5_le (z x y A B C D E : 𝔸)
    (hA : ‖A‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hB : ‖B‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hC : ‖C‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hD : ‖D‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hE : ‖E‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) :
    ‖A * B * C * D * (z - x) * E‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  calc _ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖z - x‖ * ‖E‖ := norm_6prod_le _ _ _ _ _ _
    _ ≤ M * M * M * M * d * M := by gcongr
    _ = M ^ 5 * d := by ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma norm_6prod_pos6_le (z x y A B C D E : 𝔸)
    (hA : ‖A‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hB : ‖B‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hC : ‖C‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) (hD : ‖D‖ ≤ ‖z‖ + ‖x‖ + ‖y‖)
    (hE : ‖E‖ ≤ ‖z‖ + ‖x‖ + ‖y‖) :
    ‖A * B * C * D * E * (z - x)‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖
  set d := ‖z - x‖
  calc _ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ * ‖z - x‖ := norm_6prod_le _ _ _ _ _ _
    _ ≤ M * M * M * M * M * d := by gcongr
    _ = M ^ 5 * d := by ring

/-! #### Remaining bch_sextic per-word diff bounds (24 of 28 words).

Each follows the same template: telescope identity (`noncomm_ring`) +
position-helper applications + (k-1)-step triangle inequality. -/

set_option maxHeartbeats 400000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #2 (a·a·a·b·a·b, 4 a-positions). -/
private lemma bch_sextic_word02_diff_le (z x y : 𝔸) :
    ‖z * z * z * y * z * y - x * x * x * y * x * y‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * z * z * y * z * y - x * x * x * y * x * y =
      (z - x) * z * z * y * z * y + x * (z - x) * z * y * z * y +
      x * x * (z - x) * y * z * y + x * x * x * y * (z - x) * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y z z y z y hz_le hz_le hy_le hz_le hy_le
  have h2 := norm_6prod_pos2_le z x y x z y z y hx_le hz_le hy_le hz_le hy_le
  have h3 := norm_6prod_pos3_le z x y x x y z y hx_le hx_le hy_le hz_le hy_le
  have h5 := norm_6prod_pos5_le z x y x x x y y hx_le hx_le hx_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * z * z * y * z * y
  set s2 : 𝔸 := x * (z - x) * z * y * z * y
  set s3 : 𝔸 := x * x * (z - x) * y * z * y
  set s4 : 𝔸 := x * x * x * y * (z - x) * y
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #3 (a·a·a·b·b·b, 3 a-positions). -/
private lemma bch_sextic_word03_diff_le (z x y : 𝔸) :
    ‖z * z * z * y * y * y - x * x * x * y * y * y‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * z * z * y * y * y - x * x * x * y * y * y =
      (z - x) * z * z * y * y * y + x * (z - x) * z * y * y * y +
      x * x * (z - x) * y * y * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y z z y y y hz_le hz_le hy_le hy_le hy_le
  have h2 := norm_6prod_pos2_le z x y x z y y y hx_le hz_le hy_le hy_le hy_le
  have h3 := norm_6prod_pos3_le z x y x x y y y hx_le hx_le hy_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * z * z * y * y * y
  set s2 : 𝔸 := x * (z - x) * z * y * y * y
  set s3 : 𝔸 := x * x * (z - x) * y * y * y
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #4 (a·a·b·a·a·b, 4 a-positions). -/
private lemma bch_sextic_word04_diff_le (z x y : 𝔸) :
    ‖z * z * y * z * z * y - x * x * y * x * x * y‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * z * y * z * z * y - x * x * y * x * x * y =
      (z - x) * z * y * z * z * y + x * (z - x) * y * z * z * y +
      x * x * y * (z - x) * z * y + x * x * y * x * (z - x) * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y z y z z y hz_le hy_le hz_le hz_le hy_le
  have h2 := norm_6prod_pos2_le z x y x y z z y hx_le hy_le hz_le hz_le hy_le
  have h4 := norm_6prod_pos4_le z x y x x y z y hx_le hx_le hy_le hz_le hy_le
  have h5 := norm_6prod_pos5_le z x y x x y x y hx_le hx_le hy_le hx_le hy_le
  set s1 : 𝔸 := (z - x) * z * y * z * z * y
  set s2 : 𝔸 := x * (z - x) * y * z * z * y
  set s3 : 𝔸 := x * x * y * (z - x) * z * y
  set s4 : 𝔸 := x * x * y * x * (z - x) * y
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #5 (a·a·b·a·b·b, 3 a-positions). -/
private lemma bch_sextic_word05_diff_le (z x y : 𝔸) :
    ‖z * z * y * z * y * y - x * x * y * x * y * y‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * z * y * z * y * y - x * x * y * x * y * y =
      (z - x) * z * y * z * y * y + x * (z - x) * y * z * y * y +
      x * x * y * (z - x) * y * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y z y z y y hz_le hy_le hz_le hy_le hy_le
  have h2 := norm_6prod_pos2_le z x y x y z y y hx_le hy_le hz_le hy_le hy_le
  have h4 := norm_6prod_pos4_le z x y x x y y y hx_le hx_le hy_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * z * y * z * y * y
  set s2 : 𝔸 := x * (z - x) * y * z * y * y
  set s3 : 𝔸 := x * x * y * (z - x) * y * y
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #6 (a·a·b·b·a·b, 3 a-positions). -/
private lemma bch_sextic_word06_diff_le (z x y : 𝔸) :
    ‖z * z * y * y * z * y - x * x * y * y * x * y‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * z * y * y * z * y - x * x * y * y * x * y =
      (z - x) * z * y * y * z * y + x * (z - x) * y * y * z * y +
      x * x * y * y * (z - x) * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y z y y z y hz_le hy_le hy_le hz_le hy_le
  have h2 := norm_6prod_pos2_le z x y x y y z y hx_le hy_le hy_le hz_le hy_le
  have h5 := norm_6prod_pos5_le z x y x x y y y hx_le hx_le hy_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * z * y * y * z * y
  set s2 : 𝔸 := x * (z - x) * y * y * z * y
  set s3 : 𝔸 := x * x * y * y * (z - x) * y
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #8 (a·b·a·a·a·b, 4 a-positions). -/
private lemma bch_sextic_word08_diff_le (z x y : 𝔸) :
    ‖z * y * z * z * z * y - x * y * x * x * x * y‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * y * z * z * z * y - x * y * x * x * x * y =
      (z - x) * y * z * z * z * y + x * y * (z - x) * z * z * y +
      x * y * x * (z - x) * z * y + x * y * x * x * (z - x) * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y y z z z y hy_le hz_le hz_le hz_le hy_le
  have h3 := norm_6prod_pos3_le z x y x y z z y hx_le hy_le hz_le hz_le hy_le
  have h4 := norm_6prod_pos4_le z x y x y x z y hx_le hy_le hx_le hz_le hy_le
  have h5 := norm_6prod_pos5_le z x y x y x x y hx_le hy_le hx_le hx_le hy_le
  set s1 : 𝔸 := (z - x) * y * z * z * z * y
  set s2 : 𝔸 := x * y * (z - x) * z * z * y
  set s3 : 𝔸 := x * y * x * (z - x) * z * y
  set s4 : 𝔸 := x * y * x * x * (z - x) * y
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #9 (a·b·a·a·b·b, 3 a-positions). -/
private lemma bch_sextic_word09_diff_le (z x y : 𝔸) :
    ‖z * y * z * z * y * y - x * y * x * x * y * y‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * y * z * z * y * y - x * y * x * x * y * y =
      (z - x) * y * z * z * y * y + x * y * (z - x) * z * y * y +
      x * y * x * (z - x) * y * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y y z z y y hy_le hz_le hz_le hy_le hy_le
  have h3 := norm_6prod_pos3_le z x y x y z y y hx_le hy_le hz_le hy_le hy_le
  have h4 := norm_6prod_pos4_le z x y x y x y y hx_le hy_le hx_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * y * z * z * y * y
  set s2 : 𝔸 := x * y * (z - x) * z * y * y
  set s3 : 𝔸 := x * y * x * (z - x) * y * y
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #10 (a·b·a·b·a·b, 3 a-positions). -/
private lemma bch_sextic_word10_diff_le (z x y : 𝔸) :
    ‖z * y * z * y * z * y - x * y * x * y * x * y‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * y * z * y * z * y - x * y * x * y * x * y =
      (z - x) * y * z * y * z * y + x * y * (z - x) * y * z * y +
      x * y * x * y * (z - x) * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y y z y z y hy_le hz_le hy_le hz_le hy_le
  have h3 := norm_6prod_pos3_le z x y x y y z y hx_le hy_le hy_le hz_le hy_le
  have h5 := norm_6prod_pos5_le z x y x y x y y hx_le hy_le hx_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * y * z * y * z * y
  set s2 : 𝔸 := x * y * (z - x) * y * z * y
  set s3 : 𝔸 := x * y * x * y * (z - x) * y
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #11 (a·b·a·b·b·b, 2 a-positions). -/
private lemma bch_sextic_word11_diff_le (z x y : 𝔸) :
    ‖z * y * z * y * y * y - x * y * x * y * y * y‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * y * z * y * y * y - x * y * x * y * y * y =
      (z - x) * y * z * y * y * y + x * y * (z - x) * y * y * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y y z y y y hy_le hz_le hy_le hy_le hy_le
  have h3 := norm_6prod_pos3_le z x y x y y y y hx_le hy_le hy_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * y * z * y * y * y
  set s2 : 𝔸 := x * y * (z - x) * y * y * y
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #12 (a·b·b·a·a·b, 3 a-positions). -/
private lemma bch_sextic_word12_diff_le (z x y : 𝔸) :
    ‖z * y * y * z * z * y - x * y * y * x * x * y‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * y * y * z * z * y - x * y * y * x * x * y =
      (z - x) * y * y * z * z * y + x * y * y * (z - x) * z * y +
      x * y * y * x * (z - x) * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y y y z z y hy_le hy_le hz_le hz_le hy_le
  have h4 := norm_6prod_pos4_le z x y x y y z y hx_le hy_le hy_le hz_le hy_le
  have h5 := norm_6prod_pos5_le z x y x y y x y hx_le hy_le hy_le hx_le hy_le
  set s1 : 𝔸 := (z - x) * y * y * z * z * y
  set s2 : 𝔸 := x * y * y * (z - x) * z * y
  set s3 : 𝔸 := x * y * y * x * (z - x) * y
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #13 (a·b·b·a·b·b, 2 a-positions). -/
private lemma bch_sextic_word13_diff_le (z x y : 𝔸) :
    ‖z * y * y * z * y * y - x * y * y * x * y * y‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * y * y * z * y * y - x * y * y * x * y * y =
      (z - x) * y * y * z * y * y + x * y * y * (z - x) * y * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y y y z y y hy_le hy_le hz_le hy_le hy_le
  have h4 := norm_6prod_pos4_le z x y x y y y y hx_le hy_le hy_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * y * y * z * y * y
  set s2 : 𝔸 := x * y * y * (z - x) * y * y
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #14 (a·b·b·b·a·b, 2 a-positions). -/
private lemma bch_sextic_word14_diff_le (z x y : 𝔸) :
    ‖z * y * y * y * z * y - x * y * y * y * x * y‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : z * y * y * y * z * y - x * y * y * y * x * y =
      (z - x) * y * y * y * z * y + x * y * y * y * (z - x) * y := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h1 := norm_6prod_pos1_le z x y y y y z y hy_le hy_le hy_le hz_le hy_le
  have h5 := norm_6prod_pos5_le z x y x y y y y hx_le hy_le hy_le hy_le hy_le
  set s1 : 𝔸 := (z - x) * y * y * y * z * y
  set s2 : 𝔸 := x * y * y * y * (z - x) * y
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #15 (b·a·a·a·b·a, 4 a-positions). -/
private lemma bch_sextic_word15_diff_le (z x y : 𝔸) :
    ‖y * z * z * z * y * z - y * x * x * x * y * x‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * z * z * z * y * z - y * x * x * x * y * x =
      y * (z - x) * z * z * y * z + y * x * (z - x) * z * y * z +
      y * x * x * (z - x) * y * z + y * x * x * x * y * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h2 := norm_6prod_pos2_le z x y y z z y z hy_le hz_le hz_le hy_le hz_le
  have h3 := norm_6prod_pos3_le z x y y x z y z hy_le hx_le hz_le hy_le hz_le
  have h4 := norm_6prod_pos4_le z x y y x x y z hy_le hx_le hx_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y x x x y hy_le hx_le hx_le hx_le hy_le
  set s1 : 𝔸 := y * (z - x) * z * z * y * z
  set s2 : 𝔸 := y * x * (z - x) * z * y * z
  set s3 : 𝔸 := y * x * x * (z - x) * y * z
  set s4 : 𝔸 := y * x * x * x * y * (z - x)
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #16 (b·a·a·b·a·a, 4 a-positions). -/
private lemma bch_sextic_word16_diff_le (z x y : 𝔸) :
    ‖y * z * z * y * z * z - y * x * x * y * x * x‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * z * z * y * z * z - y * x * x * y * x * x =
      y * (z - x) * z * y * z * z + y * x * (z - x) * y * z * z +
      y * x * x * y * (z - x) * z + y * x * x * y * x * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h2 := norm_6prod_pos2_le z x y y z y z z hy_le hz_le hy_le hz_le hz_le
  have h3 := norm_6prod_pos3_le z x y y x y z z hy_le hx_le hy_le hz_le hz_le
  have h5 := norm_6prod_pos5_le z x y y x x y z hy_le hx_le hx_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y x x y x hy_le hx_le hx_le hy_le hx_le
  set s1 : 𝔸 := y * (z - x) * z * y * z * z
  set s2 : 𝔸 := y * x * (z - x) * y * z * z
  set s3 : 𝔸 := y * x * x * y * (z - x) * z
  set s4 : 𝔸 := y * x * x * y * x * (z - x)
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #17 (b·a·a·b·b·a, 3 a-positions). -/
private lemma bch_sextic_word17_diff_le (z x y : 𝔸) :
    ‖y * z * z * y * y * z - y * x * x * y * y * x‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * z * z * y * y * z - y * x * x * y * y * x =
      y * (z - x) * z * y * y * z + y * x * (z - x) * y * y * z +
      y * x * x * y * y * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h2 := norm_6prod_pos2_le z x y y z y y z hy_le hz_le hy_le hy_le hz_le
  have h3 := norm_6prod_pos3_le z x y y x y y z hy_le hx_le hy_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y x x y y hy_le hx_le hx_le hy_le hy_le
  set s1 : 𝔸 := y * (z - x) * z * y * y * z
  set s2 : 𝔸 := y * x * (z - x) * y * y * z
  set s3 : 𝔸 := y * x * x * y * y * (z - x)
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #18 (b·a·b·a·a·a, 4 a-positions). -/
private lemma bch_sextic_word18_diff_le (z x y : 𝔸) :
    ‖y * z * y * z * z * z - y * x * y * x * x * x‖ ≤
      4 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * z * y * z * z * z - y * x * y * x * x * x =
      y * (z - x) * y * z * z * z + y * x * y * (z - x) * z * z +
      y * x * y * x * (z - x) * z + y * x * y * x * x * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h2 := norm_6prod_pos2_le z x y y y z z z hy_le hy_le hz_le hz_le hz_le
  have h4 := norm_6prod_pos4_le z x y y x y z z hy_le hx_le hy_le hz_le hz_le
  have h5 := norm_6prod_pos5_le z x y y x y x z hy_le hx_le hy_le hx_le hz_le
  have h6 := norm_6prod_pos6_le z x y y x y x x hy_le hx_le hy_le hx_le hx_le
  set s1 : 𝔸 := y * (z - x) * y * z * z * z
  set s2 : 𝔸 := y * x * y * (z - x) * z * z
  set s3 : 𝔸 := y * x * y * x * (z - x) * z
  set s4 : 𝔸 := y * x * y * x * x * (z - x)
  have a3 := norm_add_le (s1 + s2 + s3) s4
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #19 (b·a·b·a·b·a, 3 a-positions, |coef|=24). -/
private lemma bch_sextic_word19_diff_le (z x y : 𝔸) :
    ‖y * z * y * z * y * z - y * x * y * x * y * x‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * z * y * z * y * z - y * x * y * x * y * x =
      y * (z - x) * y * z * y * z + y * x * y * (z - x) * y * z +
      y * x * y * x * y * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h2 := norm_6prod_pos2_le z x y y y z y z hy_le hy_le hz_le hy_le hz_le
  have h4 := norm_6prod_pos4_le z x y y x y y z hy_le hx_le hy_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y x y x y hy_le hx_le hy_le hx_le hy_le
  set s1 : 𝔸 := y * (z - x) * y * z * y * z
  set s2 : 𝔸 := y * x * y * (z - x) * y * z
  set s3 : 𝔸 := y * x * y * x * y * (z - x)
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #20 (b·a·b·b·a·a, 3 a-positions). -/
private lemma bch_sextic_word20_diff_le (z x y : 𝔸) :
    ‖y * z * y * y * z * z - y * x * y * y * x * x‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * z * y * y * z * z - y * x * y * y * x * x =
      y * (z - x) * y * y * z * z + y * x * y * y * (z - x) * z +
      y * x * y * y * x * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h2 := norm_6prod_pos2_le z x y y y y z z hy_le hy_le hy_le hz_le hz_le
  have h5 := norm_6prod_pos5_le z x y y x y y z hy_le hx_le hy_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y x y y x hy_le hx_le hy_le hy_le hx_le
  set s1 : 𝔸 := y * (z - x) * y * y * z * z
  set s2 : 𝔸 := y * x * y * y * (z - x) * z
  set s3 : 𝔸 := y * x * y * y * x * (z - x)
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #21 (b·a·b·b·b·a, 2 a-positions). -/
private lemma bch_sextic_word21_diff_le (z x y : 𝔸) :
    ‖y * z * y * y * y * z - y * x * y * y * y * x‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * z * y * y * y * z - y * x * y * y * y * x =
      y * (z - x) * y * y * y * z + y * x * y * y * y * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h2 := norm_6prod_pos2_le z x y y y y y z hy_le hy_le hy_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y x y y y hy_le hx_le hy_le hy_le hy_le
  set s1 : 𝔸 := y * (z - x) * y * y * y * z
  set s2 : 𝔸 := y * x * y * y * y * (z - x)
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #23 (b·b·a·a·b·a, 3 a-positions). -/
private lemma bch_sextic_word23_diff_le (z x y : 𝔸) :
    ‖y * y * z * z * y * z - y * y * x * x * y * x‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * y * z * z * y * z - y * y * x * x * y * x =
      y * y * (z - x) * z * y * z + y * y * x * (z - x) * y * z +
      y * y * x * x * y * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h3 := norm_6prod_pos3_le z x y y y z y z hy_le hy_le hz_le hy_le hz_le
  have h4 := norm_6prod_pos4_le z x y y y x y z hy_le hy_le hx_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y y x x y hy_le hy_le hx_le hx_le hy_le
  set s1 : 𝔸 := y * y * (z - x) * z * y * z
  set s2 : 𝔸 := y * y * x * (z - x) * y * z
  set s3 : 𝔸 := y * y * x * x * y * (z - x)
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #24 (b·b·a·b·a·a, 3 a-positions). -/
private lemma bch_sextic_word24_diff_le (z x y : 𝔸) :
    ‖y * y * z * y * z * z - y * y * x * y * x * x‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * y * z * y * z * z - y * y * x * y * x * x =
      y * y * (z - x) * y * z * z + y * y * x * y * (z - x) * z +
      y * y * x * y * x * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h3 := norm_6prod_pos3_le z x y y y y z z hy_le hy_le hy_le hz_le hz_le
  have h5 := norm_6prod_pos5_le z x y y y x y z hy_le hy_le hx_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y y x y x hy_le hy_le hx_le hy_le hx_le
  set s1 : 𝔸 := y * y * (z - x) * y * z * z
  set s2 : 𝔸 := y * y * x * y * (z - x) * z
  set s3 : 𝔸 := y * y * x * y * x * (z - x)
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #25 (b·b·a·b·b·a, 2 a-positions). -/
private lemma bch_sextic_word25_diff_le (z x y : 𝔸) :
    ‖y * y * z * y * y * z - y * y * x * y * y * x‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * y * z * y * y * z - y * y * x * y * y * x =
      y * y * (z - x) * y * y * z + y * y * x * y * y * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h3 := norm_6prod_pos3_le z x y y y y y z hy_le hy_le hy_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y y x y y hy_le hy_le hx_le hy_le hy_le
  set s1 : 𝔸 := y * y * (z - x) * y * y * z
  set s2 : 𝔸 := y * y * x * y * y * (z - x)
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #26 (b·b·b·a·a·a, 3 a-positions). -/
private lemma bch_sextic_word26_diff_le (z x y : 𝔸) :
    ‖y * y * y * z * z * z - y * y * y * x * x * x‖ ≤
      3 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * y * y * z * z * z - y * y * y * x * x * x =
      y * y * y * (z - x) * z * z + y * y * y * x * (z - x) * z +
      y * y * y * x * x * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h4 := norm_6prod_pos4_le z x y y y y z z hy_le hy_le hy_le hz_le hz_le
  have h5 := norm_6prod_pos5_le z x y y y y x z hy_le hy_le hy_le hx_le hz_le
  have h6 := norm_6prod_pos6_le z x y y y y x x hy_le hy_le hy_le hx_le hx_le
  set s1 : 𝔸 := y * y * y * (z - x) * z * z
  set s2 : 𝔸 := y * y * y * x * (z - x) * z
  set s3 : 𝔸 := y * y * y * x * x * (z - x)
  have a2 := norm_add_le (s1 + s2) s3
  have a1 := norm_add_le s1 s2
  linarith

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- Word #27 (b·b·b·a·b·a, 2 a-positions). -/
private lemma bch_sextic_word27_diff_le (z x y : 𝔸) :
    ‖y * y * y * z * y * z - y * y * y * x * y * x‖ ≤
      2 * (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have htel : y * y * y * z * y * z - y * y * y * x * y * x =
      y * y * y * (z - x) * y * z + y * y * y * x * y * (z - x) := by
    noncomm_ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖
  have hz_le : ‖z‖ ≤ M := by
    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]
  have hx_le : ‖x‖ ≤ M := by
    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]
  have hy_le : ‖y‖ ≤ M := by
    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]
  have h4 := norm_6prod_pos4_le z x y y y y y z hy_le hy_le hy_le hy_le hz_le
  have h6 := norm_6prod_pos6_le z x y y y y x y hy_le hy_le hy_le hx_le hy_le
  set s1 : 𝔸 := y * y * y * (z - x) * y * z
  set s2 : 𝔸 := y * y * y * x * y * (z - x)
  have a1 := norm_add_le s1 s2
  linarith

set_option maxHeartbeats 16000000 in
include 𝕂 in
/-- **Lipschitz bound for `bch_sextic_term` in its first argument**:
`‖C₆(z, y) − C₆(x, y)‖ ≤ (‖z‖+‖x‖+‖y‖)⁵ · ‖z − x‖`.

Combines all 28 per-word Lipschitz bounds with the (1/1440) scalar factors
weighted by |coefficient|:
`K = (Σ |coef_i| · k_i) / 1440 = 492/1440 = 41/120 < 1`.

This is the analog of `norm_bch_quintic_term_diff_le` at degree 6; with
`z = (a'+b) + W` and `‖W‖ = O(s²)`, gives O(s⁷) bound on
`‖C₆(z, y) − C₆(a'+b, y)‖`. This is the key piece for the parent
T2-F7e discharge: it bounds the deg-6 outer C₆ residual in the extended
hdecomp, completing the "obviously O(s⁷)" piece group. -/
theorem norm_bch_sextic_term_diff_le (z x y : 𝔸) :
    ‖bch_sextic_term 𝕂 z y - bch_sextic_term 𝕂 x y‖ ≤
      (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def
  set d := ‖z - x‖ with hd_def
  have hd_nn : 0 ≤ d := norm_nonneg _
  have hM_nn : 0 ≤ M := by positivity
  have hM5_nn : (0 : ℝ) ≤ M ^ 5 := pow_nonneg hM_nn 5
  -- Per-word bounds.
  have w01 := bch_sextic_word01_diff_le z x y
  have w02 := bch_sextic_word02_diff_le z x y
  have w03 := bch_sextic_word03_diff_le z x y
  have w04 := bch_sextic_word04_diff_le z x y
  have w05 := bch_sextic_word05_diff_le z x y
  have w06 := bch_sextic_word06_diff_le z x y
  have w07 := bch_sextic_word07_diff_le z x y
  have w08 := bch_sextic_word08_diff_le z x y
  have w09 := bch_sextic_word09_diff_le z x y
  have w10 := bch_sextic_word10_diff_le z x y
  have w11 := bch_sextic_word11_diff_le z x y
  have w12 := bch_sextic_word12_diff_le z x y
  have w13 := bch_sextic_word13_diff_le z x y
  have w14 := bch_sextic_word14_diff_le z x y
  have w15 := bch_sextic_word15_diff_le z x y
  have w16 := bch_sextic_word16_diff_le z x y
  have w17 := bch_sextic_word17_diff_le z x y
  have w18 := bch_sextic_word18_diff_le z x y
  have w19 := bch_sextic_word19_diff_le z x y
  have w20 := bch_sextic_word20_diff_le z x y
  have w21 := bch_sextic_word21_diff_le z x y
  have w22 := bch_sextic_word22_diff_le z x y
  have w23 := bch_sextic_word23_diff_le z x y
  have w24 := bch_sextic_word24_diff_le z x y
  have w25 := bch_sextic_word25_diff_le z x y
  have w26 := bch_sextic_word26_diff_le z x y
  have w27 := bch_sextic_word27_diff_le z x y
  have w28 := bch_sextic_word28_diff_le z x y
  -- bch_sextic_term diff = Σ (coef_i / 1440) • (word_i(z, y) − word_i(x, y))
  -- For each i, ‖(coef_i / 1440) • (word_i diff)‖ ≤ |coef_i|/1440 · k_i · M⁵ · d.
  -- Sum: 492/1440 · M⁵ · d ≤ M⁵ · d.
  -- Reduce by direct triangle inequality + scaled-word bounds.
  -- First, scaled per-word bounds (each scaled by |coef_i|/1440)
  -- Norm of 1440 in 𝕂.
  have h1440_norm : ‖(1440 : 𝕂)‖ = 1440 := by
    rw [show ((1440 : 𝕂)) = ((1440 : ℕ) : 𝕂) from by norm_cast, RCLike.norm_natCast]
    norm_num
  -- Generic helper: c'/1440 · k · M⁵ · d bound for a scaled word diff
  -- where c' is a non-negative real (= |coef_i|).
  have hscaled : ∀ (c' k : ℝ) (cK : 𝕂) (Δ : 𝔸)
      (hc_norm : ‖cK‖ = c' / 1440) (hΔ : ‖Δ‖ ≤ k * M ^ 5 * d)
      (hc'_nn : 0 ≤ c') (hk_nn : 0 ≤ k),
      ‖cK • Δ‖ ≤ (c' * k / 1440) * (M ^ 5 * d) := by
    intro c' k cK Δ hc_norm hΔ hc'_nn hk_nn
    calc ‖cK • Δ‖ ≤ ‖cK‖ * ‖Δ‖ := norm_smul_le _ _
      _ = (c' / 1440) * ‖Δ‖ := by rw [hc_norm]
      _ ≤ (c' / 1440) * (k * M ^ 5 * d) := by
          apply mul_le_mul_of_nonneg_left hΔ
          positivity
      _ = (c' * k / 1440) * (M ^ 5 * d) := by ring
  -- Apply hscaled to each of the 28 scaled per-word bounds.
  -- |coef_i|: 1, 4, 4, 6, 6, 6, 1, 4, 6, 24, 4, 6, 6, 4, 4, 6, 6, 4, 24, 6, 4, 1, 6, 6, 6, 4, 4, 1
  -- k_i: 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 2, 4, 4, 3, 4, 3, 3, 2, 4, 3, 3, 2, 3, 2, 2
  -- |coef|·k: 4, 16, 12, 24, 18, 18, 2, 16, 18, 72, 8, 18, 12, 8, 16, 24, 18, 16, 72, 18, 8, 4, 18, 18, 12, 12, 8, 2
  -- Sum = 492.
  have hc01 : ‖((-1 : 𝕂) / 1440)‖ = 1 / 1440 := by
    rw [show ((-1 : 𝕂) / 1440) = -((1 : 𝕂) / 1440) from by ring, norm_neg,
      norm_div, norm_one, h1440_norm]
  have hc02 : ‖((4 : 𝕂) / 1440)‖ = 4 / 1440 := by
    rw [norm_div, h1440_norm, RCLike.norm_ofNat]
  have hc04 : ‖((-6 : 𝕂) / 1440)‖ = 6 / 1440 := by
    rw [show ((-6 : 𝕂) / 1440) = -((6 : 𝕂) / 1440) from by ring, norm_neg,
      norm_div, h1440_norm, RCLike.norm_ofNat]
  have hc10 : ‖((24 : 𝕂) / 1440)‖ = 24 / 1440 := by
    rw [norm_div, h1440_norm, RCLike.norm_ofNat]
  have hc15 : ‖((-4 : 𝕂) / 1440)‖ = 4 / 1440 := by
    rw [show ((-4 : 𝕂) / 1440) = -((4 : 𝕂) / 1440) from by ring, norm_neg,
      norm_div, h1440_norm, RCLike.norm_ofNat]
  have hc16 : ‖((6 : 𝕂) / 1440)‖ = 6 / 1440 := by
    rw [norm_div, h1440_norm, RCLike.norm_ofNat]
  have hc19 : ‖((-24 : 𝕂) / 1440)‖ = 24 / 1440 := by
    rw [show ((-24 : 𝕂) / 1440) = -((24 : 𝕂) / 1440) from by ring, norm_neg,
      norm_div, h1440_norm, RCLike.norm_ofNat]
  have hc22 : ‖((1 : 𝕂) / 1440)‖ = 1 / 1440 := by
    rw [norm_div, norm_one, h1440_norm]
  -- Scaled per-word bounds
  have hs01 : ‖((-1 : 𝕂) / 1440) • (z*z*z*z*y*y - x*x*x*x*y*y)‖ ≤ (4 / 1440) * (M^5 * d) := by
    have := hscaled 1 4 _ _ hc01 w01 (by norm_num) (by norm_num); linarith
  have hs02 : ‖((4 : 𝕂) / 1440) • (z*z*z*y*z*y - x*x*x*y*x*y)‖ ≤ (16 / 1440) * (M^5 * d) := by
    have := hscaled 4 4 _ _ hc02 w02 (by norm_num) (by norm_num); linarith
  have hs03 : ‖((4 : 𝕂) / 1440) • (z*z*z*y*y*y - x*x*x*y*y*y)‖ ≤ (12 / 1440) * (M^5 * d) := by
    have := hscaled 4 3 _ _ hc02 w03 (by norm_num) (by norm_num); linarith
  have hs04 : ‖((-6 : 𝕂) / 1440) • (z*z*y*z*z*y - x*x*y*x*x*y)‖ ≤ (24 / 1440) * (M^5 * d) := by
    have := hscaled 6 4 _ _ hc04 w04 (by norm_num) (by norm_num); linarith
  have hs05 : ‖((-6 : 𝕂) / 1440) • (z*z*y*z*y*y - x*x*y*x*y*y)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc04 w05 (by norm_num) (by norm_num); linarith
  have hs06 : ‖((-6 : 𝕂) / 1440) • (z*z*y*y*z*y - x*x*y*y*x*y)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc04 w06 (by norm_num) (by norm_num); linarith
  have hs07 : ‖((-1 : 𝕂) / 1440) • (z*z*y*y*y*y - x*x*y*y*y*y)‖ ≤ (2 / 1440) * (M^5 * d) := by
    have := hscaled 1 2 _ _ hc01 w07 (by norm_num) (by norm_num); linarith
  have hs08 : ‖((4 : 𝕂) / 1440) • (z*y*z*z*z*y - x*y*x*x*x*y)‖ ≤ (16 / 1440) * (M^5 * d) := by
    have := hscaled 4 4 _ _ hc02 w08 (by norm_num) (by norm_num); linarith
  have hs09 : ‖((-6 : 𝕂) / 1440) • (z*y*z*z*y*y - x*y*x*x*y*y)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc04 w09 (by norm_num) (by norm_num); linarith
  have hs10 : ‖((24 : 𝕂) / 1440) • (z*y*z*y*z*y - x*y*x*y*x*y)‖ ≤ (72 / 1440) * (M^5 * d) := by
    have := hscaled 24 3 _ _ hc10 w10 (by norm_num) (by norm_num); linarith
  have hs11 : ‖((4 : 𝕂) / 1440) • (z*y*z*y*y*y - x*y*x*y*y*y)‖ ≤ (8 / 1440) * (M^5 * d) := by
    have := hscaled 4 2 _ _ hc02 w11 (by norm_num) (by norm_num); linarith
  have hs12 : ‖((-6 : 𝕂) / 1440) • (z*y*y*z*z*y - x*y*y*x*x*y)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc04 w12 (by norm_num) (by norm_num); linarith
  have hs13 : ‖((-6 : 𝕂) / 1440) • (z*y*y*z*y*y - x*y*y*x*y*y)‖ ≤ (12 / 1440) * (M^5 * d) := by
    have := hscaled 6 2 _ _ hc04 w13 (by norm_num) (by norm_num); linarith
  have hs14 : ‖((4 : 𝕂) / 1440) • (z*y*y*y*z*y - x*y*y*y*x*y)‖ ≤ (8 / 1440) * (M^5 * d) := by
    have := hscaled 4 2 _ _ hc02 w14 (by norm_num) (by norm_num); linarith
  have hs15 : ‖((-4 : 𝕂) / 1440) • (y*z*z*z*y*z - y*x*x*x*y*x)‖ ≤ (16 / 1440) * (M^5 * d) := by
    have := hscaled 4 4 _ _ hc15 w15 (by norm_num) (by norm_num); linarith
  have hs16 : ‖((6 : 𝕂) / 1440) • (y*z*z*y*z*z - y*x*x*y*x*x)‖ ≤ (24 / 1440) * (M^5 * d) := by
    have := hscaled 6 4 _ _ hc16 w16 (by norm_num) (by norm_num); linarith
  have hs17 : ‖((6 : 𝕂) / 1440) • (y*z*z*y*y*z - y*x*x*y*y*x)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc16 w17 (by norm_num) (by norm_num); linarith
  have hs18 : ‖((-4 : 𝕂) / 1440) • (y*z*y*z*z*z - y*x*y*x*x*x)‖ ≤ (16 / 1440) * (M^5 * d) := by
    have := hscaled 4 4 _ _ hc15 w18 (by norm_num) (by norm_num); linarith
  have hs19 : ‖((-24 : 𝕂) / 1440) • (y*z*y*z*y*z - y*x*y*x*y*x)‖ ≤ (72 / 1440) * (M^5 * d) := by
    have := hscaled 24 3 _ _ hc19 w19 (by norm_num) (by norm_num); linarith
  have hs20 : ‖((6 : 𝕂) / 1440) • (y*z*y*y*z*z - y*x*y*y*x*x)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc16 w20 (by norm_num) (by norm_num); linarith
  have hs21 : ‖((-4 : 𝕂) / 1440) • (y*z*y*y*y*z - y*x*y*y*y*x)‖ ≤ (8 / 1440) * (M^5 * d) := by
    have := hscaled 4 2 _ _ hc15 w21 (by norm_num) (by norm_num); linarith
  have hs22 : ‖((1 : 𝕂) / 1440) • (y*y*z*z*z*z - y*y*x*x*x*x)‖ ≤ (4 / 1440) * (M^5 * d) := by
    have := hscaled 1 4 _ _ hc22 w22 (by norm_num) (by norm_num); linarith
  have hs23 : ‖((6 : 𝕂) / 1440) • (y*y*z*z*y*z - y*y*x*x*y*x)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc16 w23 (by norm_num) (by norm_num); linarith
  have hs24 : ‖((6 : 𝕂) / 1440) • (y*y*z*y*z*z - y*y*x*y*x*x)‖ ≤ (18 / 1440) * (M^5 * d) := by
    have := hscaled 6 3 _ _ hc16 w24 (by norm_num) (by norm_num); linarith
  have hs25 : ‖((6 : 𝕂) / 1440) • (y*y*z*y*y*z - y*y*x*y*y*x)‖ ≤ (12 / 1440) * (M^5 * d) := by
    have := hscaled 6 2 _ _ hc16 w25 (by norm_num) (by norm_num); linarith
  have hs26 : ‖((-4 : 𝕂) / 1440) • (y*y*y*z*z*z - y*y*y*x*x*x)‖ ≤ (12 / 1440) * (M^5 * d) := by
    have := hscaled 4 3 _ _ hc15 w26 (by norm_num) (by norm_num); linarith
  have hs27 : ‖((-4 : 𝕂) / 1440) • (y*y*y*z*y*z - y*y*y*x*y*x)‖ ≤ (8 / 1440) * (M^5 * d) := by
    have := hscaled 4 2 _ _ hc15 w27 (by norm_num) (by norm_num); linarith
  have hs28 : ‖((1 : 𝕂) / 1440) • (y*y*y*y*z*z - y*y*y*y*x*x)‖ ≤ (2 / 1440) * (M^5 * d) := by
    have := hscaled 1 2 _ _ hc22 w28 (by norm_num) (by norm_num); linarith
  -- Algebraic identity: bch_sextic_term diff = sum of 28 scaled per-word diffs.
  have hsplit : bch_sextic_term 𝕂 z y - bch_sextic_term 𝕂 x y =
        ((-1 : 𝕂) / 1440) • (z*z*z*z*y*y - x*x*x*x*y*y)
      + ((4 : 𝕂) / 1440) • (z*z*z*y*z*y - x*x*x*y*x*y)
      + ((4 : 𝕂) / 1440) • (z*z*z*y*y*y - x*x*x*y*y*y)
      + ((-6 : 𝕂) / 1440) • (z*z*y*z*z*y - x*x*y*x*x*y)
      + ((-6 : 𝕂) / 1440) • (z*z*y*z*y*y - x*x*y*x*y*y)
      + ((-6 : 𝕂) / 1440) • (z*z*y*y*z*y - x*x*y*y*x*y)
      + ((-1 : 𝕂) / 1440) • (z*z*y*y*y*y - x*x*y*y*y*y)
      + ((4 : 𝕂) / 1440) • (z*y*z*z*z*y - x*y*x*x*x*y)
      + ((-6 : 𝕂) / 1440) • (z*y*z*z*y*y - x*y*x*x*y*y)
      + ((24 : 𝕂) / 1440) • (z*y*z*y*z*y - x*y*x*y*x*y)
      + ((4 : 𝕂) / 1440) • (z*y*z*y*y*y - x*y*x*y*y*y)
      + ((-6 : 𝕂) / 1440) • (z*y*y*z*z*y - x*y*y*x*x*y)
      + ((-6 : 𝕂) / 1440) • (z*y*y*z*y*y - x*y*y*x*y*y)
      + ((4 : 𝕂) / 1440) • (z*y*y*y*z*y - x*y*y*y*x*y)
      + ((-4 : 𝕂) / 1440) • (y*z*z*z*y*z - y*x*x*x*y*x)
      + ((6 : 𝕂) / 1440) • (y*z*z*y*z*z - y*x*x*y*x*x)
      + ((6 : 𝕂) / 1440) • (y*z*z*y*y*z - y*x*x*y*y*x)
      + ((-4 : 𝕂) / 1440) • (y*z*y*z*z*z - y*x*y*x*x*x)
      + ((-24 : 𝕂) / 1440) • (y*z*y*z*y*z - y*x*y*x*y*x)
      + ((6 : 𝕂) / 1440) • (y*z*y*y*z*z - y*x*y*y*x*x)
      + ((-4 : 𝕂) / 1440) • (y*z*y*y*y*z - y*x*y*y*y*x)
      + ((1 : 𝕂) / 1440) • (y*y*z*z*z*z - y*y*x*x*x*x)
      + ((6 : 𝕂) / 1440) • (y*y*z*z*y*z - y*y*x*x*y*x)
      + ((6 : 𝕂) / 1440) • (y*y*z*y*z*z - y*y*x*y*x*x)
      + ((6 : 𝕂) / 1440) • (y*y*z*y*y*z - y*y*x*y*y*x)
      + ((-4 : 𝕂) / 1440) • (y*y*y*z*z*z - y*y*y*x*x*x)
      + ((-4 : 𝕂) / 1440) • (y*y*y*z*y*z - y*y*y*x*y*x)
      + ((1 : 𝕂) / 1440) • (y*y*y*y*z*z - y*y*y*y*x*x) := by
    unfold bch_sextic_term
    simp only [smul_sub]
    abel
  rw [hsplit]
  -- Triangle inequality on the 28-term sum.
  set t01 : 𝔸 := ((-1 : 𝕂) / 1440) • (z*z*z*z*y*y - x*x*x*x*y*y)
  set t02 : 𝔸 := ((4 : 𝕂) / 1440) • (z*z*z*y*z*y - x*x*x*y*x*y)
  set t03 : 𝔸 := ((4 : 𝕂) / 1440) • (z*z*z*y*y*y - x*x*x*y*y*y)
  set t04 : 𝔸 := ((-6 : 𝕂) / 1440) • (z*z*y*z*z*y - x*x*y*x*x*y)
  set t05 : 𝔸 := ((-6 : 𝕂) / 1440) • (z*z*y*z*y*y - x*x*y*x*y*y)
  set t06 : 𝔸 := ((-6 : 𝕂) / 1440) • (z*z*y*y*z*y - x*x*y*y*x*y)
  set t07 : 𝔸 := ((-1 : 𝕂) / 1440) • (z*z*y*y*y*y - x*x*y*y*y*y)
  set t08 : 𝔸 := ((4 : 𝕂) / 1440) • (z*y*z*z*z*y - x*y*x*x*x*y)
  set t09 : 𝔸 := ((-6 : 𝕂) / 1440) • (z*y*z*z*y*y - x*y*x*x*y*y)
  set t10 : 𝔸 := ((24 : 𝕂) / 1440) • (z*y*z*y*z*y - x*y*x*y*x*y)
  set t11 : 𝔸 := ((4 : 𝕂) / 1440) • (z*y*z*y*y*y - x*y*x*y*y*y)
  set t12 : 𝔸 := ((-6 : 𝕂) / 1440) • (z*y*y*z*z*y - x*y*y*x*x*y)
  set t13 : 𝔸 := ((-6 : 𝕂) / 1440) • (z*y*y*z*y*y - x*y*y*x*y*y)
  set t14 : 𝔸 := ((4 : 𝕂) / 1440) • (z*y*y*y*z*y - x*y*y*y*x*y)
  set t15 : 𝔸 := ((-4 : 𝕂) / 1440) • (y*z*z*z*y*z - y*x*x*x*y*x)
  set t16 : 𝔸 := ((6 : 𝕂) / 1440) • (y*z*z*y*z*z - y*x*x*y*x*x)
  set t17 : 𝔸 := ((6 : 𝕂) / 1440) • (y*z*z*y*y*z - y*x*x*y*y*x)
  set t18 : 𝔸 := ((-4 : 𝕂) / 1440) • (y*z*y*z*z*z - y*x*y*x*x*x)
  set t19 : 𝔸 := ((-24 : 𝕂) / 1440) • (y*z*y*z*y*z - y*x*y*x*y*x)
  set t20 : 𝔸 := ((6 : 𝕂) / 1440) • (y*z*y*y*z*z - y*x*y*y*x*x)
  set t21 : 𝔸 := ((-4 : 𝕂) / 1440) • (y*z*y*y*y*z - y*x*y*y*y*x)
  set t22 : 𝔸 := ((1 : 𝕂) / 1440) • (y*y*z*z*z*z - y*y*x*x*x*x)
  set t23 : 𝔸 := ((6 : 𝕂) / 1440) • (y*y*z*z*y*z - y*y*x*x*y*x)
  set t24 : 𝔸 := ((6 : 𝕂) / 1440) • (y*y*z*y*z*z - y*y*x*y*x*x)
  set t25 : 𝔸 := ((6 : 𝕂) / 1440) • (y*y*z*y*y*z - y*y*x*y*y*x)
  set t26 : 𝔸 := ((-4 : 𝕂) / 1440) • (y*y*y*z*z*z - y*y*y*x*x*x)
  set t27 : 𝔸 := ((-4 : 𝕂) / 1440) • (y*y*y*z*y*z - y*y*y*x*y*x)
  set t28 : 𝔸 := ((1 : 𝕂) / 1440) • (y*y*y*y*z*z - y*y*y*y*x*x)
  have a27 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26 + t27) t28
  have a26 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25 + t26) t27
  have a25 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24 +
    t25) t26
  have a24 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23 + t24) t25
  have a23 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23) t24
  have a22 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22) t23
  have a21 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21) t22
  have a20 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20) t21
  have a19 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19) t20
  have a18 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18) t19
  have a17 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16 + t17) t18
  have a16 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15 + t16) t17
  have a15 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14 + t15) t16
  have a14 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13 + t14) t15
  have a13 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12 + t13) t14
  have a12 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11 + t12) t13
  have a11 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10 +
    t11) t12
  have a10 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09 + t10) t11
  have a09 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08 + t09) t10
  have a08 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07 + t08) t09
  have a07 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06 + t07) t08
  have a06 := norm_add_le (t01 + t02 + t03 + t04 + t05 + t06) t07
  have a05 := norm_add_le (t01 + t02 + t03 + t04 + t05) t06
  have a04 := norm_add_le (t01 + t02 + t03 + t04) t05
  have a03 := norm_add_le (t01 + t02 + t03) t04
  have a02 := norm_add_le (t01 + t02) t03
  have a01 := norm_add_le t01 t02
  -- 492/1440 ≤ 1, so the total bound is M^5 * d.
  nlinarith [hM5_nn, hd_nn, mul_nonneg hM5_nn hd_nn]

/-! ### Quartic algebraic identity for BCH -/

set_option maxHeartbeats 64000000 in
/-- The quartic algebraic identity: `½W_H1 + ⅓(a+b)³ - bch_cubic_term` equals
a specific combination of quartic+ terms (F₁, F₂, E·b, a·E, D₁D₂, cross, P²).

Proof: clear all scalar denominators by multiplying by 12 (via the injectivity trick
from H1), then verify with `noncomm_ring`. -/
theorem quartic_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ := ea - 1 - a
    let D₂ := eb - 1 - b
    let P := ea * eb - 1 - (a + b)
    let E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let Q := a * D₂ + D₁ * b + D₁ * D₂
    let F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    -- LHS: ½W_H1 + ⅓(a+b)³ - bch_cubic_term
    (2 : 𝕂)⁻¹ • ((2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          (a + b) * P - P * (a + b) - P ^ 2) +
        (3 : 𝕂)⁻¹ • (a + b) ^ 3 - bch_cubic_term 𝕂 a b =
    -- RHS: quartic+ terms
    F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
    (2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)) -
    (2 : 𝕂)⁻¹ • P ^ 2 := by
  -- DECOMPOSITION: reduce to a pure identity in (a,b) that noncomm_ring can handle.
  --
  -- Step 1: ½W = E₁+E₂+aD₂+D₁b+D₁D₂ - ½((a+b)P+P(a+b)+P²)
  -- Step 2: Substitute E=F+⅙x³, aD₂=aE₂+½ab², D₁b=E₁b+½a²b
  -- Step 3: Split (a+b)P using P=ab+D₁+D₂+Q and D=E+½x²
  -- Step 4: After cancellation, a pure identity in a,b remains, provable by noncomm_ring.
  --
  -- The pure identity (verified by hand, all 8 noncomm monomials cancel):
  -- ⅙a³+⅙b³+½ab²+½a²b - ½((a+b)·ab+ab·(a+b))
  --   - ¼((a+b)(a²+b²)+(a²+b²)(a+b)) + ⅓(a+b)³ - bch_cubic_term = 0
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  -- Sub-identity 1: the pure cubic identity (no ea,eb — just a,b)
  -- After multiplying by 12 to clear denominators:
  -- 2a³+2b³+6ab²+6a²b - 6((a+b)ab+ab(a+b)) - 3((a+b)(a²+b²)+(a²+b²)(a+b))
  --   + 4(a+b)³ - [a,[a,b]] - [b,[b,a]] = 0
  have hpure : (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
      (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b) -
      (2 : 𝕂)⁻¹ • ((a + b) * (a * b) + a * b * (a + b)) -
      (2 : 𝕂)⁻¹ • (2 : 𝕂)⁻¹ • ((a + b) * (a ^ 2 + b ^ 2) + (a ^ 2 + b ^ 2) * (a + b)) +
      (3 : 𝕂)⁻¹ • (a + b) ^ 3 - bch_cubic_term 𝕂 a b = 0 := by
    -- Multiply by 12
    have h12ne : (12 : 𝕂) ≠ 0 := by exact_mod_cast (show (12 : ℕ) ≠ 0 by norm_num)
    have hinj : Function.Injective ((12 : 𝕂) • · : 𝔸 → 𝔸) := by
      intro x₀ y₀ hxy
      have := congrArg ((12 : 𝕂)⁻¹ • ·) hxy
      simp only [smul_smul, inv_mul_cancel₀ h12ne, one_smul] at this; exact this
    apply hinj; simp only [smul_zero]
    unfold bch_cubic_term
    simp only [smul_sub, smul_add, smul_smul]
    -- Clear scalar products: 12·(6⁻¹)=2, 12·(2⁻¹)=6, 12·(3⁻¹)=4, 12·(12⁻¹)=1,
    -- 12·(2⁻¹·2⁻¹)=3
    have h12_6 : (12 : 𝕂) * (6 : 𝕂)⁻¹ = 2 := by push_cast; norm_num
    have h12_2 : (12 : 𝕂) * (2 : 𝕂)⁻¹ = 6 := by push_cast; norm_num
    have h12_3 : (12 : 𝕂) * (3 : 𝕂)⁻¹ = 4 := by push_cast; norm_num
    have h12_12 : (12 : 𝕂) * (12 : 𝕂)⁻¹ = 1 := mul_inv_cancel₀ h12ne
    have h12_22 : (12 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 3 := by push_cast; norm_num
    simp only [h12_6, h12_2, h12_3, h12_12, h12_22, one_smul, mul_one]
    -- Now expand n•x to sums
    simp only [two_smul 𝕂, show ∀ x : 𝔸, (3 : 𝕂) • x = x + x + x from by
        intro x; rw [show (3:𝕂) = 2+1 from by push_cast; norm_num, add_smul, two_smul, one_smul],
      show ∀ x : 𝔸, (4 : 𝕂) • x = x + x + x + x from by
        intro x; rw [show (4:𝕂) = 2+2 from by push_cast; norm_num, add_smul, two_smul]; abel,
      show ∀ x : 𝔸, (6 : 𝕂) • x = x + x + x + x + x + x from by
        intro x; rw [show (6:𝕂) = 2+2+2 from by push_cast; norm_num,
          add_smul, add_smul, two_smul]; abel]
    noncomm_ring
  -- Connection: multiply by 24, clear scalar denominators, convert to ℕ-smul, noncomm_ring.
  dsimp only
  unfold bch_cubic_term
  rw [← sub_eq_zero]
  -- Multiply by 24 to clear all denominators (deepest scalar nesting: 2⁻¹·2⁻¹·2⁻¹ = 8⁻¹)
  have h24ne : (24 : 𝕂) ≠ 0 := by exact_mod_cast (show (24 : ℕ) ≠ 0 by norm_num)
  have hinj : Function.Injective ((24 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x₀ y₀ hxy; have := congrArg ((24 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h24ne, one_smul] at this; exact this
  apply hinj; simp only [smul_zero]
  -- Pull all smul out of products and merge nested smuls
  simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  -- Clear scalar products: use mul_assoc to right-associate, then cancel n*n⁻¹ and n⁻¹*n.
  -- The h24_* lemmas handle direct products 24*c⁻¹; mul_assoc + cancel handle deeper nesting.
  simp only [mul_assoc,
    -- n * n⁻¹ = 1 and n⁻¹ * n = 1
    mul_inv_cancel₀ h2ne, inv_mul_cancel₀ h2ne,
    -- 24 * c⁻¹ products (after right-association by mul_assoc)
    show (24 : 𝕂) * (2 : 𝕂)⁻¹ = 12 from by norm_num,
    show (24 : 𝕂) * (3 : 𝕂)⁻¹ = 8 from by norm_num,
    show (24 : 𝕂) * (6 : 𝕂)⁻¹ = 4 from by norm_num,
    show (24 : 𝕂) * (12 : 𝕂)⁻¹ = 2 from by norm_num,
    -- 24 * 2⁻¹ * 2⁻¹ (two-level nesting)
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 6 from by norm_num,
    -- Cleanup
    one_smul, mul_one]
  -- Convert (n : 𝕂) • x to (n : ℕ) • x so noncomm_ring (which uses abel) can close.
  simp only [ofNat_smul_eq_nsmul (R := 𝕂)]
  noncomm_ring

/-! ### Fourth-order BCH expansion -/

-- Fourth-order exp remainder: ‖exp(x)-1-x-½x²-⅙x³‖ ≤ exp(‖x‖)-1-‖x‖-‖x‖²/2-‖x‖³/6
include 𝕂 in
theorem norm_exp_sub_one_sub_sub_sub_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3‖ ≤
      Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 := by
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = x := by simp [f]
  have hf2 : f 2 = (2 : 𝕂)⁻¹ • x ^ 2 := by
    simp only [f, Nat.factorial, Nat.mul_one, Nat.cast_ofNat, pow_succ, pow_zero, one_mul]
    ring
  have hf3 : f 3 = (6 : 𝕂)⁻¹ • x ^ 3 := by
    simp only [f, Nat.factorial, Nat.mul_one, Nat.cast_ofNat, pow_succ, pow_zero, one_mul]
    norm_num
  have h_sub : exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 = ∑' n, f (n + 4) := by
    rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
    have h1 := hf_summ.tsum_eq_zero_add; rw [hf0] at h1
    have h2 := ((summable_nat_add_iff 1).mpr hf_summ).tsum_eq_zero_add
    simp only [hf1] at h2
    have h3 := ((summable_nat_add_iff 2).mpr hf_summ).tsum_eq_zero_add
    simp only [hf2] at h3
    have h4 := ((summable_nat_add_iff 3).mpr hf_summ).tsum_eq_zero_add
    simp only [hf3] at h4
    rw [h1, add_sub_cancel_left, h2, add_sub_cancel_left, h3, add_sub_cancel_left,
        h4, add_sub_cancel_left]
  rw [h_sub]
  have h_rexp := hasSum_real_exp ‖x‖
  have h_summ4 : Summable (fun n => ((n + 4) !⁻¹ : ℝ) * ‖x‖ ^ (n + 4)) :=
    (summable_nat_add_iff 4).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 4) !⁻¹ : ℝ) * ‖x‖ ^ (n + 4))
      (Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6) := by
    rw [h_summ4.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4
    linarith
  exact tsum_of_norm_bounded h_val (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 4))

-- For 0 ≤ s with s < 3/4, the fourth-order Taylor remainder satisfies
-- exp(s)-1-s-s²/2-s³/6 ≤ s⁴.
lemma real_exp_fourth_order_le_quartic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
    Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 ≤ s ^ 4 := by
  have hs_lt1 : s < 1 := by linarith
  -- exp(s)-1-s-s²/2 ≤ s³/(6(1-s)) from real_exp_third_order_le_div
  -- So exp(s)-1-s-s²/2-s³/6 = (exp(s)-1-s-s²/2) - s³/6
  -- The n≥4 tail: Σ_{n≥0} s^(n+4)/(n+4)!
  have h_rexp := hasSum_real_exp s
  have h_summ4 : Summable (fun n => ((n + 4) !⁻¹ : ℝ) * s ^ (n + 4)) :=
    (summable_nat_add_iff 4).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 4) !⁻¹ : ℝ) * s ^ (n + 4))
      (Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6) := by
    rw [h_summ4.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4
    linarith
  -- Comparison: (n+4)!⁻¹ * s^(n+4) ≤ (24)⁻¹ * s^(n+4) since (n+4)! ≥ 4! = 24
  -- So tail ≤ s⁴/(24(1-s)) ≤ s⁴ for s < 23/24
  have h_geom_summ : Summable (fun n => s ^ (n + 4) / 24) := by
    apply Summable.div_const
    exact (summable_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 4) |>.congr fun n => by ring
  have hterm : ∀ n, ((n + 4) !⁻¹ : ℝ) * s ^ (n + 4) ≤ s ^ (n + 4) * (24 : ℝ)⁻¹ := by
    intro n
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (n + 4)!) (by positivity : (0 : ℝ) < 24)]
    have : (4 : ℕ)! ≤ (n + 4)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  have h_geom : HasSum (fun n => s ^ (n + 4) * (24 : ℝ)⁻¹) (s ^ 4 * (1 - s)⁻¹ * (24 : ℝ)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 4)
    have h_eq : (fun n => s ^ 4 * s ^ n) = (fun n => s ^ (n + 4)) := by ext n; ring
    rw [h_eq] at hg
    exact hg.mul_right (24 : ℝ)⁻¹
  calc Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6
      = ∑' n, ((n + 4) !⁻¹ : ℝ) * s ^ (n + 4) := h_val.tsum_eq.symm
    _ ≤ ∑' n, (s ^ (n + 4) * (24 : ℝ)⁻¹) :=
        h_summ4.tsum_le_tsum hterm h_geom.summable
    _ = s ^ 4 * (1 - s)⁻¹ * (24 : ℝ)⁻¹ := h_geom.tsum_eq
    _ = s ^ 4 / (24 * (1 - s)) := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ s ^ 4 := by
        rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 24 * (1 - s))]
        nlinarith [sq_nonneg s, pow_nonneg hs 4]

/-! ### Fifth-order exp helpers -/

-- Fifth-order exp remainder: ‖exp(x)-1-x-½x²-⅙x³-(1/24)x⁴‖ ≤ exp(‖x‖)-1-‖x‖-‖x‖²/2-‖x‖³/6-‖x‖⁴/24
include 𝕂 in
theorem norm_exp_sub_one_sub_sub_sub_sub_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 - (24 : 𝕂)⁻¹ • x ^ 4‖ ≤
      Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 := by
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = x := by simp [f]
  have hf2 : f 2 = (2 : 𝕂)⁻¹ • x ^ 2 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    ring
  have hf3 : f 3 = (6 : 𝕂)⁻¹ • x ^ 3 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf4 : f 4 = (24 : 𝕂)⁻¹ • x ^ 4 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have h_sub : exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 -
      (24 : 𝕂)⁻¹ • x ^ 4 = ∑' n, f (n + 5) := by
    rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
    have h1 := hf_summ.tsum_eq_zero_add; rw [hf0] at h1
    have h2 := ((summable_nat_add_iff 1).mpr hf_summ).tsum_eq_zero_add
    simp only [hf1] at h2
    have h3 := ((summable_nat_add_iff 2).mpr hf_summ).tsum_eq_zero_add
    simp only [hf2] at h3
    have h4 := ((summable_nat_add_iff 3).mpr hf_summ).tsum_eq_zero_add
    simp only [hf3] at h4
    have h5 := ((summable_nat_add_iff 4).mpr hf_summ).tsum_eq_zero_add
    simp only [hf4] at h5
    rw [h1, add_sub_cancel_left, h2, add_sub_cancel_left, h3, add_sub_cancel_left,
        h4, add_sub_cancel_left, h5, add_sub_cancel_left]
  rw [h_sub]
  have h_rexp := hasSum_real_exp ‖x‖
  have h_summ5 : Summable (fun n => ((n + 5) !⁻¹ : ℝ) * ‖x‖ ^ (n + 5)) :=
    (summable_nat_add_iff 5).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 5) !⁻¹ : ℝ) * ‖x‖ ^ (n + 5))
      (Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24) := by
    rw [h_summ5.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5
    linarith
  exact tsum_of_norm_bounded h_val (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 5))

-- For 0 ≤ s with s < 3/4, the fifth-order Taylor remainder satisfies
-- exp(s)-1-s-s²/2-s³/6-s⁴/24 ≤ s⁵.
lemma real_exp_fifth_order_le_quintic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
    Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 ≤ s ^ 5 := by
  have hs_lt1 : s < 1 := by linarith
  have h_rexp := hasSum_real_exp s
  have h_summ5 : Summable (fun n => ((n + 5) !⁻¹ : ℝ) * s ^ (n + 5)) :=
    (summable_nat_add_iff 5).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 5) !⁻¹ : ℝ) * s ^ (n + 5))
      (Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24) := by
    rw [h_summ5.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5
    linarith
  -- Comparison: (n+5)!⁻¹ * s^(n+5) ≤ (120)⁻¹ * s^(n+5) since (n+5)! ≥ 5! = 120
  have h_geom_summ : Summable (fun n => s ^ (n + 5) / 120) := by
    apply Summable.div_const
    exact (summable_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 5) |>.congr fun n => by ring
  have hterm : ∀ n, ((n + 5) !⁻¹ : ℝ) * s ^ (n + 5) ≤ s ^ (n + 5) * (120 : ℝ)⁻¹ := by
    intro n
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (n + 5)!) (by positivity : (0 : ℝ) < 120)]
    have : (5 : ℕ)! ≤ (n + 5)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  have h_geom : HasSum (fun n => s ^ (n + 5) * (120 : ℝ)⁻¹) (s ^ 5 * (1 - s)⁻¹ * (120 : ℝ)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 5)
    have h_eq : (fun n => s ^ 5 * s ^ n) = (fun n => s ^ (n + 5)) := by ext n; ring
    rw [h_eq] at hg
    exact hg.mul_right (120 : ℝ)⁻¹
  calc Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24
      = ∑' n, ((n + 5) !⁻¹ : ℝ) * s ^ (n + 5) := h_val.tsum_eq.symm
    _ ≤ ∑' n, (s ^ (n + 5) * (120 : ℝ)⁻¹) :=
        h_summ5.tsum_le_tsum hterm h_geom.summable
    _ = s ^ 5 * (1 - s)⁻¹ * (120 : ℝ)⁻¹ := h_geom.tsum_eq
    _ = s ^ 5 / (120 * (1 - s)) := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ s ^ 5 := by
        rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 120 * (1 - s))]
        nlinarith [sq_nonneg s, pow_nonneg hs 5]

/-! ### Sixth-order exp helpers -/

-- Sixth-order exp remainder:
--   ‖exp(x) - 1 - x - ½x² - ⅙x³ - (1/24)x⁴ - (1/120)x⁵‖ ≤
--   exp(‖x‖) - 1 - ‖x‖ - ‖x‖²/2 - ‖x‖³/6 - ‖x‖⁴/24 - ‖x‖⁵/120
include 𝕂 in
theorem norm_exp_sub_one_sub_sub_sub_sub_sub_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 - (24 : 𝕂)⁻¹ • x ^ 4 -
        (120 : 𝕂)⁻¹ • x ^ 5‖ ≤
      Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 -
        ‖x‖ ^ 5 / 120 := by
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = x := by simp [f]
  have hf2 : f 2 = (2 : 𝕂)⁻¹ • x ^ 2 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    ring
  have hf3 : f 3 = (6 : 𝕂)⁻¹ • x ^ 3 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf4 : f 4 = (24 : 𝕂)⁻¹ • x ^ 4 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf5 : f 5 = (120 : 𝕂)⁻¹ • x ^ 5 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have h_sub : exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 -
      (24 : 𝕂)⁻¹ • x ^ 4 - (120 : 𝕂)⁻¹ • x ^ 5 = ∑' n, f (n + 6) := by
    rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
    have h1 := hf_summ.tsum_eq_zero_add; rw [hf0] at h1
    have h2 := ((summable_nat_add_iff 1).mpr hf_summ).tsum_eq_zero_add
    simp only [hf1] at h2
    have h3 := ((summable_nat_add_iff 2).mpr hf_summ).tsum_eq_zero_add
    simp only [hf2] at h3
    have h4 := ((summable_nat_add_iff 3).mpr hf_summ).tsum_eq_zero_add
    simp only [hf3] at h4
    have h5 := ((summable_nat_add_iff 4).mpr hf_summ).tsum_eq_zero_add
    simp only [hf4] at h5
    have h6 := ((summable_nat_add_iff 5).mpr hf_summ).tsum_eq_zero_add
    simp only [hf5] at h6
    rw [h1, add_sub_cancel_left, h2, add_sub_cancel_left, h3, add_sub_cancel_left,
        h4, add_sub_cancel_left, h5, add_sub_cancel_left, h6, add_sub_cancel_left]
  rw [h_sub]
  have h_rexp := hasSum_real_exp ‖x‖
  have h_summ6 : Summable (fun n => ((n + 6) !⁻¹ : ℝ) * ‖x‖ ^ (n + 6)) :=
    (summable_nat_add_iff 6).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 6) !⁻¹ : ℝ) * ‖x‖ ^ (n + 6))
      (Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 -
        ‖x‖ ^ 5 / 120) := by
    rw [h_summ6.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split6 := ((summable_nat_add_iff 5).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5 h_split6
    linarith
  exact tsum_of_norm_bounded h_val (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 6))

-- For 0 ≤ s with s < 3/4, the sixth-order Taylor remainder satisfies
-- exp(s) - 1 - s - s²/2 - s³/6 - s⁴/24 - s⁵/120 ≤ s⁶.
lemma real_exp_sixth_order_le_sextic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
    Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120 ≤ s ^ 6 := by
  have hs_lt1 : s < 1 := by linarith
  have h_rexp := hasSum_real_exp s
  have h_summ6 : Summable (fun n => ((n + 6) !⁻¹ : ℝ) * s ^ (n + 6)) :=
    (summable_nat_add_iff 6).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 6) !⁻¹ : ℝ) * s ^ (n + 6))
      (Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120) := by
    rw [h_summ6.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split6 := ((summable_nat_add_iff 5).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5 h_split6
    linarith
  -- Comparison: (n+6)!⁻¹ * s^(n+6) ≤ (720)⁻¹ * s^(n+6) since (n+6)! ≥ 6! = 720
  have h_geom_summ : Summable (fun n => s ^ (n + 6) / 720) := by
    apply Summable.div_const
    exact (summable_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 6) |>.congr fun n => by ring
  have hterm : ∀ n, ((n + 6) !⁻¹ : ℝ) * s ^ (n + 6) ≤ s ^ (n + 6) * (720 : ℝ)⁻¹ := by
    intro n
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (n + 6)!) (by positivity : (0 : ℝ) < 720)]
    have : (6 : ℕ)! ≤ (n + 6)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  have h_geom : HasSum (fun n => s ^ (n + 6) * (720 : ℝ)⁻¹) (s ^ 6 * (1 - s)⁻¹ * (720 : ℝ)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 6)
    have h_eq : (fun n => s ^ 6 * s ^ n) = (fun n => s ^ (n + 6)) := by ext n; ring
    rw [h_eq] at hg
    exact hg.mul_right (720 : ℝ)⁻¹
  calc Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120
      = ∑' n, ((n + 6) !⁻¹ : ℝ) * s ^ (n + 6) := h_val.tsum_eq.symm
    _ ≤ ∑' n, (s ^ (n + 6) * (720 : ℝ)⁻¹) :=
        h_summ6.tsum_le_tsum hterm h_geom.summable
    _ = s ^ 6 * (1 - s)⁻¹ * (720 : ℝ)⁻¹ := h_geom.tsum_eq
    _ = s ^ 6 / (720 * (1 - s)) := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ s ^ 6 := by
        rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 720 * (1 - s))]
        nlinarith [sq_nonneg s, pow_nonneg hs 6]

/-! ### Seventh-order exp helpers -/

-- Seventh-order exp remainder:
--   ‖exp(x) - 1 - x - ½x² - ⅙x³ - (1/24)x⁴ - (1/120)x⁵ - (1/720)x⁶‖ ≤
--   exp(‖x‖) - 1 - ‖x‖ - ‖x‖²/2 - ‖x‖³/6 - ‖x‖⁴/24 - ‖x‖⁵/120 - ‖x‖⁶/720
include 𝕂 in
theorem norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 - (24 : 𝕂)⁻¹ • x ^ 4 -
        (120 : 𝕂)⁻¹ • x ^ 5 - (720 : 𝕂)⁻¹ • x ^ 6‖ ≤
      Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 -
        ‖x‖ ^ 5 / 120 - ‖x‖ ^ 6 / 720 := by
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = x := by simp [f]
  have hf2 : f 2 = (2 : 𝕂)⁻¹ • x ^ 2 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    ring
  have hf3 : f 3 = (6 : 𝕂)⁻¹ • x ^ 3 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf4 : f 4 = (24 : 𝕂)⁻¹ • x ^ 4 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf5 : f 5 = (120 : 𝕂)⁻¹ • x ^ 5 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf6 : f 6 = (720 : 𝕂)⁻¹ • x ^ 6 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have h_sub : exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 -
      (24 : 𝕂)⁻¹ • x ^ 4 - (120 : 𝕂)⁻¹ • x ^ 5 - (720 : 𝕂)⁻¹ • x ^ 6 =
      ∑' n, f (n + 7) := by
    rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
    have h1 := hf_summ.tsum_eq_zero_add; rw [hf0] at h1
    have h2 := ((summable_nat_add_iff 1).mpr hf_summ).tsum_eq_zero_add
    simp only [hf1] at h2
    have h3 := ((summable_nat_add_iff 2).mpr hf_summ).tsum_eq_zero_add
    simp only [hf2] at h3
    have h4 := ((summable_nat_add_iff 3).mpr hf_summ).tsum_eq_zero_add
    simp only [hf3] at h4
    have h5 := ((summable_nat_add_iff 4).mpr hf_summ).tsum_eq_zero_add
    simp only [hf4] at h5
    have h6 := ((summable_nat_add_iff 5).mpr hf_summ).tsum_eq_zero_add
    simp only [hf5] at h6
    have h7 := ((summable_nat_add_iff 6).mpr hf_summ).tsum_eq_zero_add
    simp only [hf6] at h7
    rw [h1, add_sub_cancel_left, h2, add_sub_cancel_left, h3, add_sub_cancel_left,
        h4, add_sub_cancel_left, h5, add_sub_cancel_left, h6, add_sub_cancel_left,
        h7, add_sub_cancel_left]
  rw [h_sub]
  have h_rexp := hasSum_real_exp ‖x‖
  have h_summ7 : Summable (fun n => ((n + 7) !⁻¹ : ℝ) * ‖x‖ ^ (n + 7)) :=
    (summable_nat_add_iff 7).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 7) !⁻¹ : ℝ) * ‖x‖ ^ (n + 7))
      (Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 -
        ‖x‖ ^ 5 / 120 - ‖x‖ ^ 6 / 720) := by
    rw [h_summ7.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split6 := ((summable_nat_add_iff 5).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split7 := ((summable_nat_add_iff 6).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5 h_split6 h_split7
    linarith
  exact tsum_of_norm_bounded h_val (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 7))

-- For 0 ≤ s with s < 3/4, the seventh-order Taylor remainder satisfies
-- exp(s) - 1 - s - s²/2 - s³/6 - s⁴/24 - s⁵/120 - s⁶/720 ≤ s⁷.
lemma real_exp_seventh_order_le_septic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
    Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120 -
        s ^ 6 / 720 ≤ s ^ 7 := by
  have hs_lt1 : s < 1 := by linarith
  have h_rexp := hasSum_real_exp s
  have h_summ7 : Summable (fun n => ((n + 7) !⁻¹ : ℝ) * s ^ (n + 7)) :=
    (summable_nat_add_iff 7).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 7) !⁻¹ : ℝ) * s ^ (n + 7))
      (Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120 -
        s ^ 6 / 720) := by
    rw [h_summ7.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split6 := ((summable_nat_add_iff 5).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split7 := ((summable_nat_add_iff 6).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5 h_split6 h_split7
    linarith
  -- Comparison: (n+7)!⁻¹ * s^(n+7) ≤ (5040)⁻¹ * s^(n+7) since (n+7)! ≥ 7! = 5040
  have h_geom_summ : Summable (fun n => s ^ (n + 7) / 5040) := by
    apply Summable.div_const
    exact (summable_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 7) |>.congr fun n => by ring
  have hterm : ∀ n, ((n + 7) !⁻¹ : ℝ) * s ^ (n + 7) ≤ s ^ (n + 7) * (5040 : ℝ)⁻¹ := by
    intro n
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (n + 7)!) (by positivity : (0 : ℝ) < 5040)]
    have : (7 : ℕ)! ≤ (n + 7)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  have h_geom : HasSum (fun n => s ^ (n + 7) * (5040 : ℝ)⁻¹)
      (s ^ 7 * (1 - s)⁻¹ * (5040 : ℝ)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 7)
    have h_eq : (fun n => s ^ 7 * s ^ n) = (fun n => s ^ (n + 7)) := by ext n; ring
    rw [h_eq] at hg
    exact hg.mul_right (5040 : ℝ)⁻¹
  calc Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120 -
        s ^ 6 / 720
      = ∑' n, ((n + 7) !⁻¹ : ℝ) * s ^ (n + 7) := h_val.tsum_eq.symm
    _ ≤ ∑' n, (s ^ (n + 7) * (5040 : ℝ)⁻¹) :=
        h_summ7.tsum_le_tsum hterm h_geom.summable
    _ = s ^ 7 * (1 - s)⁻¹ * (5040 : ℝ)⁻¹ := h_geom.tsum_eq
    _ = s ^ 7 / (5040 * (1 - s)) := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ s ^ 7 := by
        rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 5040 * (1 - s))]
        nlinarith [sq_nonneg s, pow_nonneg hs 7]

/-- For `0 ≤ s ≤ 1/10`, `(Real.exp s - 1)^7 ≤ 2 · s^7`. Used in the small-s
septic remainder assembly. Analog of the inline `hexp6` calculation for the
sextic case, extended one degree. -/
lemma real_exp_sub_one_pow7_le_small {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_small : s ≤ 1 / 10) :
    (Real.exp s - 1) ^ 7 ≤ 2 * s ^ 7 := by
  have hE1_nn : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
  have hs_lt1 : s < 1 := by linarith
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
      linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
    rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn,
         Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  calc (Real.exp s - 1) ^ 7 ≤ (s + s ^ 2) ^ 7 :=
        pow_le_pow_left₀ hE1_nn (by linarith) 7
    _ = s ^ 7 * (1 + s) ^ 7 := by ring
    _ ≤ s ^ 7 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs_nn 7)
        have h1 : (1 + s) ^ 7 ≤ (1 + 1/10) ^ 7 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 7
        have h2 : (1 + 1/10 : ℝ) ^ 7 ≤ 2 := by norm_num
        linarith
    _ = 2 * s ^ 7 := by ring

/-- For `0 ≤ s ≤ 1/10`, `(Real.exp s - 1)^8 ≤ 3 · s^8`. Used in the small-s
octic remainder assembly. Analog of `real_exp_sub_one_pow7_le_small` at one
degree higher; constant is 3 (not 2) because `(1+1/10)^8 ≈ 2.14`. -/
lemma real_exp_sub_one_pow8_le_small {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_small : s ≤ 1 / 10) :
    (Real.exp s - 1) ^ 8 ≤ 3 * s ^ 8 := by
  have hE1_nn : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
  have hs_lt1 : s < 1 := by linarith
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
      linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
    rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn,
         Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  calc (Real.exp s - 1) ^ 8 ≤ (s + s ^ 2) ^ 8 :=
        pow_le_pow_left₀ hE1_nn (by linarith) 8
    _ = s ^ 8 * (1 + s) ^ 8 := by ring
    _ ≤ s ^ 8 * 3 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs_nn 8)
        have h1 : (1 + s) ^ 8 ≤ (1 + 1/10) ^ 8 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 8
        have h2 : (1 + 1/10 : ℝ) ^ 8 ≤ 3 := by norm_num
        linarith
    _ = 3 * s ^ 8 := by ring

/-- **Eighth-order noncommutative exp tail bound**: norm of the deg-8+ tail
of `exp(x) = ∑ xⁿ/n!` is bounded by the corresponding real tail.

Adds one more level to `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le`. -/
theorem norm_exp_sub_one_sub_sub_sub_sub_sub_sub_sub_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 - (24 : 𝕂)⁻¹ • x ^ 4 -
        (120 : 𝕂)⁻¹ • x ^ 5 - (720 : 𝕂)⁻¹ • x ^ 6 - (5040 : 𝕂)⁻¹ • x ^ 7‖ ≤
      Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 -
        ‖x‖ ^ 5 / 120 - ‖x‖ ^ 6 / 720 - ‖x‖ ^ 7 / 5040 := by
  set f : ℕ → 𝔸 := fun n => (n !⁻¹ : 𝕂) • x ^ n
  have hf_summ : Summable f := NormedSpace.expSeries_summable' (𝕂 := 𝕂) x
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = x := by simp [f]
  have hf2 : f 2 = (2 : 𝕂)⁻¹ • x ^ 2 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    ring
  have hf3 : f 3 = (6 : 𝕂)⁻¹ • x ^ 3 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf4 : f 4 = (24 : 𝕂)⁻¹ • x ^ 4 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf5 : f 5 = (120 : 𝕂)⁻¹ • x ^ 5 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf6 : f 6 = (720 : 𝕂)⁻¹ • x ^ 6 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have hf7 : f 7 = (5040 : 𝕂)⁻¹ • x ^ 7 := by
    simp only [f, Nat.factorial, Nat.mul_one, pow_succ, pow_zero, one_mul]
    norm_num
  have h_sub : exp x - 1 - x - (2 : 𝕂)⁻¹ • x ^ 2 - (6 : 𝕂)⁻¹ • x ^ 3 -
      (24 : 𝕂)⁻¹ • x ^ 4 - (120 : 𝕂)⁻¹ • x ^ 5 - (720 : 𝕂)⁻¹ • x ^ 6 -
      (5040 : 𝕂)⁻¹ • x ^ 7 = ∑' n, f (n + 8) := by
    rw [congr_fun (exp_eq_tsum 𝕂 (𝔸 := 𝔸)) x]
    have h1 := hf_summ.tsum_eq_zero_add; rw [hf0] at h1
    have h2 := ((summable_nat_add_iff 1).mpr hf_summ).tsum_eq_zero_add
    simp only [hf1] at h2
    have h3 := ((summable_nat_add_iff 2).mpr hf_summ).tsum_eq_zero_add
    simp only [hf2] at h3
    have h4 := ((summable_nat_add_iff 3).mpr hf_summ).tsum_eq_zero_add
    simp only [hf3] at h4
    have h5 := ((summable_nat_add_iff 4).mpr hf_summ).tsum_eq_zero_add
    simp only [hf4] at h5
    have h6 := ((summable_nat_add_iff 5).mpr hf_summ).tsum_eq_zero_add
    simp only [hf5] at h6
    have h7 := ((summable_nat_add_iff 6).mpr hf_summ).tsum_eq_zero_add
    simp only [hf6] at h7
    have h8 := ((summable_nat_add_iff 7).mpr hf_summ).tsum_eq_zero_add
    simp only [hf7] at h8
    rw [h1, add_sub_cancel_left, h2, add_sub_cancel_left, h3, add_sub_cancel_left,
        h4, add_sub_cancel_left, h5, add_sub_cancel_left, h6, add_sub_cancel_left,
        h7, add_sub_cancel_left, h8, add_sub_cancel_left]
  rw [h_sub]
  have h_rexp := hasSum_real_exp ‖x‖
  have h_summ8 : Summable (fun n => ((n + 8) !⁻¹ : ℝ) * ‖x‖ ^ (n + 8)) :=
    (summable_nat_add_iff 8).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 8) !⁻¹ : ℝ) * ‖x‖ ^ (n + 8))
      (Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 - ‖x‖ ^ 3 / 6 - ‖x‖ ^ 4 / 24 -
        ‖x‖ ^ 5 / 120 - ‖x‖ ^ 6 / 720 - ‖x‖ ^ 7 / 5040) := by
    rw [h_summ8.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split6 := ((summable_nat_add_iff 5).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split7 := ((summable_nat_add_iff 6).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split8 := ((summable_nat_add_iff 7).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5 h_split6 h_split7 h_split8
    linarith
  exact tsum_of_norm_bounded h_val (fun n => norm_expSeries_term_le' (𝕂 := 𝕂) x (n + 8))

-- For 0 ≤ s with s < 3/4, the eighth-order Taylor remainder satisfies
-- exp(s) - 1 - s - ... - s⁷/5040 ≤ s⁸.
lemma real_exp_eighth_order_le_octic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
    Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120 -
        s ^ 6 / 720 - s ^ 7 / 5040 ≤ s ^ 8 := by
  have hs_lt1 : s < 1 := by linarith
  have h_rexp := hasSum_real_exp s
  have h_summ8 : Summable (fun n => ((n + 8) !⁻¹ : ℝ) * s ^ (n + 8)) :=
    (summable_nat_add_iff 8).mpr h_rexp.summable
  have h_val : HasSum (fun n => ((n + 8) !⁻¹ : ℝ) * s ^ (n + 8))
      (Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120 -
        s ^ 6 / 720 - s ^ 7 / 5040) := by
    rw [h_summ8.hasSum_iff]
    have h_split := h_rexp.summable.tsum_eq_zero_add; rw [h_rexp.tsum_eq] at h_split
    have h_split2 := ((summable_nat_add_iff 1).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split3 := ((summable_nat_add_iff 2).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split4 := ((summable_nat_add_iff 3).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split5 := ((summable_nat_add_iff 4).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split6 := ((summable_nat_add_iff 5).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split7 := ((summable_nat_add_iff 6).mpr h_rexp.summable).tsum_eq_zero_add
    have h_split8 := ((summable_nat_add_iff 7).mpr h_rexp.summable).tsum_eq_zero_add
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
      Nat.factorial_one, pow_one, zero_add] at h_split h_split2 h_split3 h_split4 h_split5 h_split6 h_split7 h_split8
    linarith
  -- Comparison: (n+8)!⁻¹ * s^(n+8) ≤ (40320)⁻¹ * s^(n+8) since (n+8)! ≥ 8! = 40320
  have h_geom_summ : Summable (fun n => s ^ (n + 8) / 40320) := by
    apply Summable.div_const
    exact (summable_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 8) |>.congr fun n => by ring
  have hterm : ∀ n, ((n + 8) !⁻¹ : ℝ) * s ^ (n + 8) ≤ s ^ (n + 8) * (40320 : ℝ)⁻¹ := by
    intro n
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (n + 8)!) (by positivity : (0 : ℝ) < 40320)]
    have : (8 : ℕ)! ≤ (n + 8)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  have h_geom : HasSum (fun n => s ^ (n + 8) * (40320 : ℝ)⁻¹)
      (s ^ 8 * (1 - s)⁻¹ * (40320 : ℝ)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hs hs_lt1).mul_left (s ^ 8)
    have h_eq : (fun n => s ^ 8 * s ^ n) = (fun n => s ^ (n + 8)) := by ext n; ring
    rw [h_eq] at hg
    exact hg.mul_right (40320 : ℝ)⁻¹
  calc Real.exp s - 1 - s - s ^ 2 / 2 - s ^ 3 / 6 - s ^ 4 / 24 - s ^ 5 / 120 -
        s ^ 6 / 720 - s ^ 7 / 5040
      = ∑' n, ((n + 8) !⁻¹ : ℝ) * s ^ (n + 8) := h_val.tsum_eq.symm
    _ ≤ ∑' n, (s ^ (n + 8) * (40320 : ℝ)⁻¹) :=
        h_summ8.tsum_le_tsum hterm h_geom.summable
    _ = s ^ 8 * (1 - s)⁻¹ * (40320 : ℝ)⁻¹ := h_geom.tsum_eq
    _ = s ^ 8 / (40320 * (1 - s)) := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ s ^ 8 := by
        rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 40320 * (1 - s))]
        nlinarith [sq_nonneg s, pow_nonneg hs 8]

set_option maxHeartbeats 32000000 in
include 𝕂 in
/-- **Fourth-order BCH**: `bch(a,b) = (a+b) + ½[a,b] + bch_cubic_term(a,b) + O(s⁴)`.

This extends H1 by identifying the cubic coefficient `(1/12)([a,[a,b]]+[b,[b,a]])`.
The proof extracts the quartic log remainder `logOnePlus(y)-y+½y²-⅓y³` and the
degree-3 algebraic terms, showing they combine to `bch_cubic_term`. -/
theorem norm_bch_quartic_remainder_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b‖ ≤
      200 * (‖a‖ + ‖b‖) ^ 4 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  -- SETUP: same as H1
  set y := exp a * exp b - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖; set β := ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have : y = (exp a - 1) * exp b + (exp b - 1) := by rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [this]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          apply add_le_add
          · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
              (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hs56 : s < 5 / 6 := by
    calc s < Real.log 2 := hab
      _ ≤ 5 / 6 := by
          rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
          calc (2 : ℝ) ≤ 1 + 5 / 6 + (5 / 6) ^ 2 / 2 := by norm_num
            _ ≤ Real.exp (5 / 6) := Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hs34 : s < 3 / 4 := lt_of_lt_of_le hab (by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    calc (2 : ℝ) ≤ 1 + 3 / 4 + (3 / 4) ^ 2 / 2 := by norm_num
      _ ≤ Real.exp (3 / 4) := Real.quadratic_le_exp_of_nonneg (by norm_num))
  have hs1 : s < 1 := by linarith
  -- Auxiliary definitions
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set P := y - (a + b) with hP_def
  set E₁ := exp a - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := exp b - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := exp a - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := exp b - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  -- Decomposition: bch - (a+b) - ½[a,b] - cubic = pieceA' + pieceB'
  -- where pieceA' = logOnePlus(y) - y + ½y² - ⅓y³   (quartic log tail)
  -- and pieceB' = y - (a+b) - ½(ab-ba) + ½y² - ⅓y³ - bch_cubic_term
  -- but we reorganize: bch = logOnePlus(y), so
  -- LHS = logOnePlus(y) - (a+b) - ½(ab-ba) - cubic
  -- = [logOnePlus(y) - y + ½y² - ⅓y³] + [y - (a+b) - ½(ab-ba) - ½y² + ⅓y³ - cubic]
  -- Wait: -½y² + ⅓y³? No, the signs should be:
  -- logOnePlus(y) = y - ½y² + ⅓y³ + (quartic log tail with flipped sign convention)
  -- Actually: logOnePlus(y) - y + ½y² - ⅓y³ = quartic tail
  -- So logOnePlus(y) = y - ½y² + ⅓y³ + [quartic tail]
  -- Then LHS = y - ½y² + ⅓y³ + [quartic tail] - (a+b) - ½(ab-ba) - cubic
  -- = [quartic tail] + [y - (a+b) - ½(ab-ba) - ½y² + ⅓y³ - cubic]
  have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b =
      (logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3) +
      (y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 -
        bch_cubic_term 𝕂 a b) := by
    unfold bch bch_cubic_term; abel
  rw [hdecomp]
  -- Piece A' bound: ‖logOnePlus(y) - y + ½y² - ⅓y³‖ ≤ ‖y‖⁴/(1-‖y‖)
  have hpieceA : ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
      (3 : 𝕂)⁻¹ • y ^ 3‖ ≤
      (Real.exp s - 1) ^ 4 / (2 - Real.exp s) :=
    calc _ ≤ ‖y‖ ^ 4 / (1 - ‖y‖) := norm_logOnePlus_sub_sub_sub_le (𝕂 := 𝕂) y hy_lt
      _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
          (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
  -- PIECE B: Setup
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set P := y - (a + b) with hP_def
  set E₁ := exp a - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := exp b - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := exp a - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := exp b - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
  set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
  have hP_eq : P = a * b + D₁ + D₂ + Q := by
    rw [hQ_def, hP_def, hy_def, hD₁_def, hD₂_def]; noncomm_ring
  -- Norm bounds
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
    have hP_factor : P = (exp a - 1) * (exp b - 1) + D₁ + D₂ := by
      rw [hP_def, hy_def, hD₁_def, hD₂_def]; noncomm_ring
    rw [hP_factor]
    calc ‖(exp a - 1) * (exp b - 1) + D₁ + D₂‖
        ≤ ‖(exp a - 1) * (exp b - 1)‖ + ‖D₁‖ + ‖D₂‖ := by
          calc _ ≤ ‖(exp a - 1) * (exp b - 1) + D₁‖ + ‖D₂‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ (Real.exp α - 1) * (Real.exp β - 1) +
          (Real.exp α - 1 - α) + (Real.exp β - 1 - β) := by
          gcongr
          calc ‖(exp a - 1) * (exp b - 1)‖
              ≤ ‖exp a - 1‖ * ‖exp b - 1‖ := norm_mul_le _ _
            _ ≤ _ := mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a)
                (norm_exp_sub_one_le (𝕂 := 𝕂) b) (norm_nonneg _)
                (by linarith [Real.add_one_le_exp α])
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  -- Real Taylor bounds
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le (by linarith : s < 3 / 4))
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le (by linarith : s < 3 / 4))
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖α‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hα_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDa_nn, Real.norm_eq_abs, abs_of_nonneg hα_nn] at h
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖β‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hβ_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg hDb_nn, Real.norm_eq_abs, abs_of_nonneg hβ_nn] at h
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le
      (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.add_one_le_exp s]),
         Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  have hEa_nn : 0 ≤ Real.exp α - 1 - α - α ^ 2 / 2 := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn]
  have hEb_nn : 0 ≤ Real.exp β - 1 - β - β ^ 2 / 2 := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn]
  -- Scalar utilities
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  have h3ne : (3 : 𝕂) ≠ 0 := by exact_mod_cast (show (3 : ℕ) ≠ 0 by norm_num)
  have h6ne : (6 : 𝕂) ≠ 0 := by exact_mod_cast (show (6 : ℕ) ≠ 0 by norm_num)
  have h12ne : (12 : 𝕂) ≠ 0 := by exact_mod_cast (show (12 : ℕ) ≠ 0 by norm_num)
  -- H1 identity: y-(a+b)-½(ab-ba)-½y² = ½W
  have hpieceB_eq_H1 : y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      (2 : 𝕂)⁻¹ • y ^ 2 = (2 : 𝕂)⁻¹ •
      ((2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
        (a + b) * P - P * (a + b) - P ^ 2) := by
    suffices h : (2 : 𝕂) • (y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2) = (2 : 𝕂) • ((2 : 𝕂)⁻¹ •
        ((2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          (a + b) * P - P * (a + b) - P ^ 2)) by
      have hinj : Function.Injective ((2 : 𝕂) • · : 𝔸 → 𝔸) := by
        intro x₀ y₀ hxy
        have := congrArg ((2 : 𝕂)⁻¹ • ·) hxy
        simp only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] at this; exact this
      exact hinj h
    rw [smul_smul, mul_inv_cancel₀ h2ne, one_smul]
    rw [hE₁_def, hE₂_def, hD₁_def, hD₂_def, hP_def, hy_def]
    simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h2ne, one_smul, two_smul]
    noncomm_ring
  -- Define pieceB and split into I₁ + I₂
  set pieceB := y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
    (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - bch_cubic_term 𝕂 a b with hpieceB_def
  set z := a + b with hz_def
  set I₂ := (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) with hI₂_def
  set I₁ := pieceB - I₂ with hI₁_def
  have hpieceB_split : pieceB = I₁ + I₂ := by rw [hI₁_def]; abel
  -- Bound I₂ = ⅓(y³-z³) where y=z+P
  have hy_eq_zP : y = z + P := by
    simp only [hP_def, hz_def]; abel
  have hz_le : ‖z‖ ≤ s := by
    calc ‖z‖ = ‖a + b‖ := by rw [hz_def]
      _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ = s := by rw [hs_def]
  have hP_le_s2 : ‖P‖ ≤ s ^ 2 := le_trans hP_le hEs2
  have hI₂_bound : ‖I₂‖ ≤ 8 * s ^ 4 := by
    -- y=z+P so y³-z³ has every term with ≥1 factor of P
    -- ‖P‖ ≤ s², ‖y‖ ≤ exp(s)-1 ≤ s+s², ‖z‖ ≤ s
    -- Use: y³-z³ = y²(y-z)+y(y-z)z+(y-z)z² = y²P+yPz+Pz² (telescoping)
    have hy3z3 : y ^ 3 - z ^ 3 = y ^ 2 * P + y * P * z + P * z ^ 2 := by
      rw [hy_eq_zP]; noncomm_ring
    have h3_norm : ‖(3 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
    have hy_le' : ‖y‖ ≤ s + s ^ 2 := by linarith [hy_le, hEs2]
    calc ‖I₂‖ = ‖(3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3)‖ := by rfl
      _ ≤ ‖(3 : 𝕂)⁻¹‖ * ‖y ^ 2 * P + y * P * z + P * z ^ 2‖ := by
          rw [hy3z3]; exact norm_smul_le _ _
      _ ≤ 1 * (‖y ^ 2 * P‖ + ‖y * P * z‖ + ‖P * z ^ 2‖) := by
          gcongr
          calc _ ≤ ‖y ^ 2 * P + y * P * z‖ + ‖P * z ^ 2‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ 1 * (‖y‖ ^ 2 * ‖P‖ + ‖y‖ * ‖P‖ * ‖z‖ + ‖P‖ * ‖z‖ ^ 2) := by
          rw [one_mul, one_mul]; gcongr
          · calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 2
          · calc _ ≤ ‖y * P‖ * ‖z‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_mul_le _ _
          · calc _ ≤ ‖P‖ * ‖z ^ 2‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ (s + s ^ 2) ^ 2 * s ^ 2 + (s + s ^ 2) * s ^ 2 * s + s ^ 2 * s ^ 2 := by
          have h1 : ‖y‖ ^ 2 * ‖P‖ ≤ (s + s ^ 2) ^ 2 * s ^ 2 := by
            apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_le' 2) hP_le_s2
              (norm_nonneg P) (by positivity)
          have h2 : ‖y‖ * ‖P‖ * ‖z‖ ≤ (s + s ^ 2) * s ^ 2 * s := by
            apply mul_le_mul (mul_le_mul hy_le' hP_le_s2 (norm_nonneg P) (by positivity))
              hz_le (norm_nonneg z) (by positivity)
          have h3 : ‖P‖ * ‖z‖ ^ 2 ≤ s ^ 2 * s ^ 2 := by
            apply mul_le_mul hP_le_s2 (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
              (by positivity) (by positivity)
          linarith
      _ ≤ 8 * s ^ 4 := by
          have := pow_nonneg hs_nn 5
          have := pow_nonneg hs_nn 6
          nlinarith [sq_nonneg s, pow_nonneg hs_nn 4]
  -- Use quartic_identity to prove 12·I₁ = quartic terms
  -- Rewrite I₁ using H1's piece B identity
  set W_H1 := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          (a + b) * P - P * (a + b) - P ^ 2 with hW_H1_def
  have hI₁_eq2 : I₁ = (2 : 𝕂)⁻¹ • W_H1 +
      (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b := by
    -- I₁ = pieceB - I₂ and pieceB has the H1 piece replaced
    -- pieceB - I₂ = pieceB - ⅓(y³-z³)
    -- = y-(a+b)-½(ab-ba)-½y²+⅓y³-cubic - ⅓y³ + ⅓z³
    -- = y-(a+b)-½(ab-ba)-½y² + ⅓z³ - cubic
    have h1 : I₁ = (y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2) + (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b := by
      simp only [hI₁_def, hpieceB_def, hI₂_def, hz_def]
      -- Decompose ⅓y³ = ⅓(y³-z³) + ⅓z³ where z = a+b
      rw [show (3 : 𝕂)⁻¹ • y ^ 3 = (3 : 𝕂)⁻¹ • (y ^ 3 - (a + b) ^ 3) +
          (3 : 𝕂)⁻¹ • (a + b) ^ 3 from by rw [smul_sub]; abel]
      abel
    rw [h1, hpieceB_eq_H1]
  -- Use quartic_identity directly: I₁ = quartic terms
  have hI₁_quartic : I₁ =
      F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
      (2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)) -
      (2 : 𝕂)⁻¹ • P ^ 2 := by
    rw [hI₁_eq2]
    exact quartic_identity 𝕂 (exp a) (exp b) a b
  -- Bound ‖I₁‖
  have hI₁_le : ‖I₁‖ ≤ 90 * s ^ 4 := by
    -- Bound each term in hI₁_quartic using triangle inequality + component bounds.
    have h2_le : ‖(2 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
    -- Component bounds (all ≤ s⁴)
    have hF₁_s4 : ‖F₁‖ ≤ s ^ 4 :=
      le_trans hF₁_le (le_trans hFa4 (pow_le_pow_left₀ hα_nn hα_le 4))
    have hF₂_s4 : ‖F₂‖ ≤ s ^ 4 :=
      le_trans hF₂_le (le_trans hFb4 (pow_le_pow_left₀ hβ_nn hβ_le 4))
    have haE₂ : ‖a * E₂‖ ≤ s ^ 4 :=
      calc ‖a * E₂‖ ≤ ‖a‖ * ‖E₂‖ := norm_mul_le _ _
        _ ≤ α * β ^ 3 := mul_le_mul_of_nonneg_left (le_trans hE₂_le hEb3) hα_nn
        _ ≤ s * s ^ 3 := by nlinarith [pow_le_pow_left₀ hβ_nn hβ_le 3]
        _ = s ^ 4 := by ring
    have hE₁b : ‖E₁ * b‖ ≤ s ^ 4 :=
      calc ‖E₁ * b‖ ≤ ‖E₁‖ * ‖b‖ := norm_mul_le _ _
        _ ≤ α ^ 3 * β := mul_le_mul (le_trans hE₁_le hEa3) le_rfl hβ_nn (by positivity)
        _ ≤ s ^ 3 * s := by nlinarith [pow_le_pow_left₀ hα_nn hα_le 3]
        _ = s ^ 4 := by ring
    have hDD : ‖D₁ * D₂‖ ≤ s ^ 4 :=
      calc ‖D₁ * D₂‖ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le _ _
        _ ≤ α ^ 2 * β ^ 2 := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
            (norm_nonneg _) (by positivity)
        _ ≤ s ^ 2 * s ^ 2 := by
            apply mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
              (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
        _ = s ^ 4 := by ring
    -- Cross term: ‖(a+b)‖ ≤ s, ‖E₁+E₂+Q‖ ≤ 5s³
    have hQ_le : ‖Q‖ ≤ 3 * s ^ 3 := by
      calc ‖Q‖ ≤ ‖a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖ := by
            rw [hQ_def]; calc _ ≤ ‖a * D₂ + D₁ * b‖ + _ := norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
        _ ≤ α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 := by
            gcongr
            · calc _ ≤ ‖a‖ * ‖D₂‖ := norm_mul_le _ _
                _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans hD₂_le hDb2) hα_nn
            · calc _ ≤ ‖D₁‖ * ‖b‖ := norm_mul_le _ _
                _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) le_rfl hβ_nn (by positivity)
            · calc _ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le _ _
                _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
                    (norm_nonneg _) (by positivity)
        _ ≤ s * s ^ 2 + s ^ 2 * s + s ^ 2 * s ^ 2 := by
            nlinarith [pow_le_pow_left₀ hα_nn hα_le 2, pow_le_pow_left₀ hβ_nn hβ_le 2]
        _ ≤ 3 * s ^ 3 := by nlinarith [pow_nonneg hs_nn 4]
    have hEQ : ‖E₁ + E₂ + Q‖ ≤ 5 * s ^ 3 :=
      calc ‖E₁ + E₂ + Q‖ ≤ ‖E₁‖ + ‖E₂‖ + ‖Q‖ := by
            calc _ ≤ ‖E₁ + E₂‖ + ‖Q‖ := norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
        _ ≤ α ^ 3 + β ^ 3 + 3 * s ^ 3 := by linarith [le_trans hE₁_le hEa3, le_trans hE₂_le hEb3]
        _ ≤ s ^ 3 + s ^ 3 + 3 * s ^ 3 := by
            nlinarith [pow_le_pow_left₀ hα_nn hα_le 3, pow_le_pow_left₀ hβ_nn hβ_le 3]
        _ = 5 * s ^ 3 := by ring
    -- Cross term bound
    have hcross_inner : ‖(a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)‖ ≤
        10 * s ^ 4 := by
      calc _ ≤ ‖(a + b) * (E₁ + E₂ + Q)‖ + ‖(E₁ + E₂ + Q) * (a + b)‖ := norm_add_le _ _
        _ ≤ s * (5 * s ^ 3) + 5 * s ^ 3 * s := by
            gcongr
            · exact le_trans (norm_mul_le _ _) (mul_le_mul hz_le hEQ (norm_nonneg _) hs_nn)
            · exact le_trans (norm_mul_le _ _) (mul_le_mul hEQ hz_le (norm_nonneg _)
                (by positivity))
        _ = 10 * s ^ 4 := by ring
    have hcross : ‖(2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) +
        (E₁ + E₂ + Q) * (a + b))‖ ≤ 10 * s ^ 4 :=
      calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖(a + b) * (E₁ + E₂ + Q) +
            (E₁ + E₂ + Q) * (a + b)‖ := norm_smul_le _ _
        _ ≤ 1 * (10 * s ^ 4) := by gcongr
        _ = 10 * s ^ 4 := one_mul _
    have hP2 : ‖(2 : 𝕂)⁻¹ • P ^ 2‖ ≤ s ^ 4 := by
      calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖P ^ 2‖ := norm_smul_le _ _
        _ ≤ 1 * ‖P‖ ^ 2 := by
            gcongr
            exact norm_pow_le P 2
        _ ≤ 1 * (s ^ 2) ^ 2 := by
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 2
            · norm_num
        _ = s ^ 4 := by rw [one_mul]; ring
    -- Triangle inequality + combine all bounds
    rw [hI₁_quartic]
    have h1 : ‖F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)) -
        (2 : 𝕂)⁻¹ • P ^ 2‖ ≤
        ‖F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b))‖ +
        ‖(2 : 𝕂)⁻¹ • P ^ 2‖ := by
      rw [show F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)) -
        (2 : 𝕂)⁻¹ • P ^ 2 = (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b))) -
        (2 : 𝕂)⁻¹ • P ^ 2 from by abel]
      exact norm_sub_le _ _
    have h2 : ‖F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b))‖ ≤
        ‖F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂‖ +
        ‖(2 : 𝕂)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b))‖ :=
      norm_sub_le _ _
    have h3 : ‖F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂‖ ≤
        ‖F₁‖ + ‖F₂‖ + ‖a * E₂‖ + ‖E₁ * b‖ + ‖D₁ * D₂‖ := by
      calc _ ≤ ‖F₁ + F₂ + a * E₂ + E₁ * b‖ + ‖D₁ * D₂‖ := norm_add_le _ _
        _ ≤ (‖F₁ + F₂ + a * E₂‖ + ‖E₁ * b‖) + ‖D₁ * D₂‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖F₁ + F₂‖ + ‖a * E₂‖) + ‖E₁ * b‖) + ‖D₁ * D₂‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ (((‖F₁‖ + ‖F₂‖) + ‖a * E₂‖) + ‖E₁ * b‖) + ‖D₁ * D₂‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖F₁‖ + ‖F₂‖ + ‖a * E₂‖ + ‖E₁ * b‖ + ‖D₁ * D₂‖ := by ring
    -- Chain: goal ≤ (h3 bound + hcross) + hP2 via h1,h2
    -- = (5*s⁴ + 10*s⁴) + s⁴ = 16*s⁴ ≤ 90*s⁴
    linarith [h1, h2, h3, hF₁_s4, hF₂_s4, haE₂, hE₁b, hDD, hcross, hP2,
              pow_nonneg hs_nn 4]
  -- (old hI₁_le removed — replaced by the one above using hI₁_quartic)
  -- Combine
  have hpieceB_le : ‖pieceB‖ ≤ 98 * s ^ 4 := by
    rw [hpieceB_split]
    calc ‖I₁ + I₂‖ ≤ ‖I₁‖ + ‖I₂‖ := norm_add_le _ _
      _ ≤ 90 * s ^ 4 + 8 * s ^ 4 := by linarith [hI₁_le, hI₂_bound]
      _ = 98 * s ^ 4 := by ring
  calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3‖ +
        ‖pieceB‖ := norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 4 / (2 - Real.exp s) + 98 * s ^ 4 := by linarith [hpieceA, hpieceB_le]
    _ ≤ 200 * s ^ 4 / (2 - Real.exp s) := by
        rw [div_add' _ _ _ (ne_of_gt hdenom)]
        apply div_le_div_of_nonneg_right _ hdenom.le
        have hE1_nn : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
        have hE1_le : Real.exp s - 1 ≤ s + s ^ 2 := by linarith [hEs2]
        have h1s4 : (1 + s) ^ 4 ≤ 10 := by nlinarith [sq_nonneg s, sq_nonneg (s - 3/4)]
        have hexp4 : (Real.exp s - 1) ^ 4 ≤ 10 * s ^ 4 :=
          calc (Real.exp s - 1) ^ 4 ≤ (s + s ^ 2) ^ 4 := pow_le_pow_left₀ hE1_nn hE1_le 4
            _ = s ^ 4 * (1 + s) ^ 4 := by ring
            _ ≤ s ^ 4 * 10 := by nlinarith [pow_nonneg hs_nn 4]
            _ = 10 * s ^ 4 := by ring
        nlinarith [pow_nonneg hs_nn 4, hdenom.le,
          show 2 - Real.exp s ≤ 1 from by linarith [Real.add_one_le_exp s]]


end

end BCH
