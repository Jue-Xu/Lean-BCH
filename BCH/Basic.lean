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
private lemma continuousOn_logOnePlus {r : ℝ} (hr : r < 1) :
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
private lemma real_exp_third_order_le_cube {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 5 / 6) :
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

/-! ### Fifth-order BCH term (Z₅) -/

/-- **Sign-1 group** of `bch_quintic_term`: the four 5-letter words with
  absolute coefficient 1 (the "almost-pure" pattern AAAAB / ABBBB / BAAAA /
  BBBBA). Each appears with coefficient -1/720 in Z₅.

  Factored separately to keep the proofs of `bch_quintic_term_smul` and
  `norm_bch_quintic_term_le` tractable. -/
private noncomputable def bch_quintic_group_1 {𝔸 : Type*} [NormedRing 𝔸]
    (a b : 𝔸) : 𝔸 :=
  a * a * a * a * b + a * b * b * b * b + b * a * a * a * a + b * b * b * b * a

/-- **Sign-4 group** of `bch_quintic_term`: the ten 5-letter words with
  absolute coefficient 4. Each appears with coefficient +4/720 = 1/180. -/
private noncomputable def bch_quintic_group_4 {𝔸 : Type*} [NormedRing 𝔸]
    (a b : 𝔸) : 𝔸 :=
  a * a * a * b * a + a * a * a * b * b + a * a * b * b * b +
  a * b * a * a * a + a * b * b * b * a + b * a * a * a * b +
  b * a * b * b * b + b * b * a * a * a + b * b * b * a * a +
  b * b * b * a * b

/-- **Sign-6 group** of `bch_quintic_term`: the fourteen 5-letter words
  with absolute coefficient 6. Each appears with coefficient -6/720 = -1/120. -/
private noncomputable def bch_quintic_group_6 {𝔸 : Type*} [NormedRing 𝔸]
    (a b : 𝔸) : 𝔸 :=
  a * a * b * a * a + a * a * b * a * b + a * a * b * b * a +
  a * b * a * a * b + a * b * a * b * b + a * b * b * a * a +
  a * b * b * a * b + b * a * a * b * a + b * a * a * b * b +
  b * a * b * a * a + b * a * b * b * a + b * b * a * a * b +
  b * b * a * b * a + b * b * a * b * b

/-- **Sign-24 group** of `bch_quintic_term`: the two 5-letter palindromic
  words with absolute coefficient 24. Each appears with coefficient
  +24/720 = 1/30. -/
private noncomputable def bch_quintic_group_24 {𝔸 : Type*} [NormedRing 𝔸]
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

/-! ### Quartic algebraic identity for BCH -/

set_option maxHeartbeats 64000000 in
/-- The quartic algebraic identity: `½W_H1 + ⅓(a+b)³ - bch_cubic_term` equals
a specific combination of quartic+ terms (F₁, F₂, E·b, a·E, D₁D₂, cross, P²).

Proof: clear all scalar denominators by multiplying by 12 (via the injectivity trick
from H1), then verify with `noncomm_ring`. -/
private theorem quartic_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
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
private theorem norm_exp_sub_one_sub_sub_sub_le (x : 𝔸) :
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
private lemma real_exp_fourth_order_le_quartic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
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
private theorem norm_exp_sub_one_sub_sub_sub_sub_le (x : 𝔸) :
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
private lemma real_exp_fifth_order_le_quintic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
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
private theorem norm_exp_sub_one_sub_sub_sub_sub_sub_le (x : 𝔸) :
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
private lemma real_exp_sixth_order_le_sextic {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 3 / 4) :
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

/-! ### Quintic algebraic identity for BCH -/

-- The degree-4 pure identity: verified by noncomm_ring at Ring level (no 𝕂 needed).
-- After ×24 clearing: the Y₄-½(Y₁Y₃+Y₂²+Y₃Y₁)+⅓(Y₁²Y₂+...)-¼Y₁⁴+C₄ = 0.
set_option maxHeartbeats 800000000 in
omit [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
theorem quintic_pure_identity_cleared (a b : 𝔸) :
    -- 24×[Y₄-½(Y₁Y₃+Y₂²+Y₃Y₁)+⅓(Y₁²Y₂+Y₁Y₂Y₁+Y₂Y₁²)-¼Y₁⁴+C₄] = 0
    -- z := a+b, U := 2ab+a²+b² (= 2Y₂)
    (a ^ 4 + 4 • (a ^ 3 * b) + 6 • (a ^ 2 * b ^ 2) + 4 • (a * b ^ 3) + b ^ 4) -
    2 • ((a + b) * (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) +
         (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) * (a + b)) -
    3 • ((2 • (a * b) + a ^ 2 + b ^ 2) * (2 • (a * b) + a ^ 2 + b ^ 2)) +
    4 • ((a + b) ^ 2 * (2 • (a * b) + a ^ 2 + b ^ 2) +
         (a + b) * (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) +
         (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) ^ 2) -
    6 • (a + b) ^ 4 +
    (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
     (a * (a * b - b * a) - (a * b - b * a) * a) * b) = 0 := by
  noncomm_ring

-- 𝕂-scalar version of the degree-4 cancellation identity.
-- Same identity as quintic_pure_identity_cleared, but stated with 𝕂-scalars
-- so it can be used in the NormedAlgebra 𝕂 𝔸 context.
-- Proved by ×24 scalar clearing (with triple-nesting lemmas) + noncomm_ring.
set_option maxHeartbeats 800000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem quintic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
    (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
    (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
    (2 : 𝕂)⁻¹ • ((a + b) * ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) +
      ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) * (a + b)) -
    (2 : 𝕂)⁻¹ • (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) ^ 2 +
    (3 : 𝕂)⁻¹ • ((a + b) ^ 2 * (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) +
      (a + b) * (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) * (a + b) +
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) * (a + b) ^ 2) -
    (4 : 𝕂)⁻¹ • (a + b) ^ 4 - bch_quartic_term 𝕂 a b = 0 := by
  have h24ne : (24 : 𝕂) ≠ 0 := by exact_mod_cast (show (24 : ℕ) ≠ 0 by norm_num)
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  have hinj : Function.Injective ((24 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x₀ y₀ hxy; have := congrArg ((24 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h24ne, one_smul] at this; exact this
  apply hinj; simp only [smul_zero]
  unfold bch_quartic_term
  -- Expand powers first so scalar smuls inside (e.g. P₂^2) get distributed
  simp only [pow_succ, pow_zero, one_mul]
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  simp only [mul_assoc,
    mul_inv_cancel₀ h2ne, inv_mul_cancel₀ h2ne,
    mul_inv_cancel₀ h24ne,
    show (24 : 𝕂) * (6 : 𝕂)⁻¹ = 4 from by norm_num,
    show (24 : 𝕂) * (4 : 𝕂)⁻¹ = 6 from by norm_num,
    show (24 : 𝕂) * (3 : 𝕂)⁻¹ = 8 from by norm_num,
    show (24 : 𝕂) * (2 : 𝕂)⁻¹ = 12 from by norm_num,
    -- Intermediate products that may arise after partial clearing
    show (12 : 𝕂) * (2 : 𝕂)⁻¹ = 6 from by norm_num,
    show (6 : 𝕂) * (2 : 𝕂)⁻¹ = 3 from by norm_num,
    show (4 : 𝕂) * (2 : 𝕂)⁻¹ = 2 from by norm_num,
    show (8 : 𝕂) * (2 : 𝕂)⁻¹ = 4 from by norm_num,
    -- Two-level nesting
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 6 from by norm_num,
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 2 from by norm_num,
    show (24 : 𝕂) * ((6 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 2 from by norm_num,
    show (24 : 𝕂) * ((3 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 4 from by norm_num,
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹) = 4 from by norm_num,
    -- Intermediate two-level
    show (12 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 3 from by norm_num,
    -- Three-level nesting (from ⅓·P₂² and ½·P₂² where P₂ has ½ coefficients)
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 3 from by norm_num,
    show (24 : 𝕂) * ((3 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 2 from by norm_num,
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * ((3 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 2 from by norm_num,
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹)) = 2 from by norm_num,
    one_smul, mul_one]
  simp only [ofNat_smul_eq_nsmul (R := 𝕂)]
  -- After clearing, the goal is a pure ring/nsmul identity provable by noncomm_ring.
  noncomm_ring

/-! ### Sixth-order BCH: degree-5 cancellation identity (sextic_pure_identity) -/

-- Pure {a, b} ring identity for the degree-5 cancellation of pieceB_sextic.
-- After substituting ea → exp(a), eb → exp(b), the deg-5 part of
--   ½W_H1 + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅
-- vanishes. This identity expresses that vanishing as an explicit pure
-- {a, b} ring identity.
--
-- Notation (for readability):
--   z  = a + b
--   T₂ = ab + ½a² + ½b²        (= y_subst[2])
--   T₃ = ⅙a³ + ½a²b + ½ab² + ⅙b³  (= y_subst[3])
--   T₄ = (1/24)a⁴ + ⅙a³b + ¼a²b² + ⅙ab³ + (1/24)b⁴  (= y_subst[4])
--
--   W5 = (60)⁻¹·a⁵ + (60)⁻¹·b⁵ + (12)⁻¹·ab⁴ + (12)⁻¹·a⁴b
--      + (6)⁻¹·a²b³ + (6)⁻¹·a³b² - (z·T₄ + T₄·z) - (T₂·T₃ + T₃·T₂)
--   y3_5 = z²·T₃ + z·T₃·z + T₃·z² + z·T₂² + T₂·z·T₂ + T₂²·z
--   y4_5 = z³·T₂ + z²·T₂·z + z·T₂·z² + T₂·z³
--   y5_5 = z⁵
--
-- Identity: ½·W5 + ⅓·y3_5 - ¼·y4_5 + ⅕·z⁵ - bch_quintic_term = 0.
-- Verified by Lean-Trotter/scripts/discover_quintic_identity.py rev 6d029b6.
set_option maxHeartbeats 4000000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem sextic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂)
    let y3_5 : 𝔸 := z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z
    let y4_5 : 𝔸 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3
    (2 : 𝕂)⁻¹ • W5 + (3 : 𝕂)⁻¹ • y3_5 - (4 : 𝕂)⁻¹ • y4_5 + (5 : 𝕂)⁻¹ • z ^ 5
      - bch_quintic_term 𝕂 a b = 0 := by
  -- Multiply by 720 (LCM covers all denominators).
  have h720ne : (720 : 𝕂) ≠ 0 := by exact_mod_cast (show (720 : ℕ) ≠ 0 by norm_num)
  have hinj : Function.Injective ((720 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x₀ y₀ hxy; have := congrArg ((720 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h720ne, one_smul] at this; exact this
  apply hinj; simp only [smul_zero]
  unfold bch_quintic_term bch_quintic_group_1 bch_quintic_group_4
    bch_quintic_group_6 bch_quintic_group_24
  -- Expand powers first so scalar smuls inside (e.g. T₂^2) get distributed.
  simp only [pow_succ, pow_zero, one_mul]
  -- Distribute scalars through all algebraic operations.
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  -- Clear scalar products.
  simp only [mul_assoc,
    mul_inv_cancel₀ (show (2 : 𝕂) ≠ 0 from two_ne_zero),
    inv_mul_cancel₀ (show (2 : 𝕂) ≠ 0 from two_ne_zero),
    mul_inv_cancel₀ h720ne,
    show (720 : 𝕂) * (2 : 𝕂)⁻¹ = 360 from by norm_num,
    show (720 : 𝕂) * (3 : 𝕂)⁻¹ = 240 from by norm_num,
    show (720 : 𝕂) * (4 : 𝕂)⁻¹ = 180 from by norm_num,
    show (720 : 𝕂) * (5 : 𝕂)⁻¹ = 144 from by norm_num,
    show (720 : 𝕂) * (6 : 𝕂)⁻¹ = 120 from by norm_num,
    show (720 : 𝕂) * (12 : 𝕂)⁻¹ = 60 from by norm_num,
    show (720 : 𝕂) * (24 : 𝕂)⁻¹ = 30 from by norm_num,
    show (720 : 𝕂) * (60 : 𝕂)⁻¹ = 12 from by norm_num,
    show (720 : 𝕂) * (720 : 𝕂)⁻¹ = 1 from mul_inv_cancel₀ h720ne,
    -- Two-level nesting
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 180 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹) = 120 from by norm_num,
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 120 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (4 : 𝕂)⁻¹) = 90 from by norm_num,
    show (720 : 𝕂) * ((4 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 90 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (24 : 𝕂)⁻¹) = 15 from by norm_num,
    show (720 : 𝕂) * ((24 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 15 from by norm_num,
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 40 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹) = 40 from by norm_num,
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * (4 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((4 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹) = 30 from by norm_num,
    show (720 : 𝕂) * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 30 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (60 : 𝕂)⁻¹) = 6 from by norm_num,
    show (720 : 𝕂) * ((60 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 6 from by norm_num,
    -- Three-level nesting
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 60 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 90 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹)) = 30 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * ((6 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 30 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 30 from by norm_num,
    -- 720·(720⁻¹·N) form (from bch_quintic_term inner factors)
    show (720 : 𝕂) * ((720 : 𝕂)⁻¹ * (4 : 𝕂)) = 4 from by
      rw [← mul_assoc, mul_inv_cancel₀ h720ne, one_mul],
    show (720 : 𝕂) * ((720 : 𝕂)⁻¹ * (6 : 𝕂)) = 6 from by
      rw [← mul_assoc, mul_inv_cancel₀ h720ne, one_mul],
    show (720 : 𝕂) * ((720 : 𝕂)⁻¹ * (24 : 𝕂)) = 24 from by
      rw [← mul_assoc, mul_inv_cancel₀ h720ne, one_mul],
    one_smul, mul_one]
  simp only [ofNat_smul_eq_nsmul (R := 𝕂)]
  noncomm_ring

set_option maxHeartbeats 128000000 in
include 𝕂 in
/-- **Fifth-order BCH**: `bch(a,b) = (a+b) + ½[a,b] + bch_cubic_term(a,b) + bch_quartic_term(a,b) + O(s⁵)`.

This extends the fourth-order result `norm_bch_quartic_remainder_le` by identifying the
quartic coefficient `-(1/24)([a,[a,[a,b]]]+[b,[b,[b,a]]])`. The proof decomposes
`LHS = pieceA' + pieceB'` where pieceA' is the quintic log tail (bounded by `‖y‖⁵/(1-‖y‖)`)
and pieceB' is the algebraic piece (bounded by combining the quartic_identity with
fifth-order exp remainders and the quartic norm bound on the combined degree-4 terms). -/
theorem norm_bch_quintic_remainder_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
      3000 * (‖a‖ + ‖b‖) ^ 5 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  -- SETUP (same as quartic proof)
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
  have hs34 : s < 3 / 4 := lt_of_lt_of_le hab (by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    calc (2 : ℝ) ≤ 1 + 3 / 4 + (3 / 4) ^ 2 / 2 := by norm_num
      _ ≤ Real.exp (3 / 4) := Real.quadratic_le_exp_of_nonneg (by norm_num))
  have hs1 : s < 1 := by linarith
  -- STRATEGY: Use quartic theorem + C₄ bound + case split on s.
  -- R₃ := bch-(a+b)-½[a,b]-C₃ satisfies ‖R₃‖ ≤ 200s⁴/(2-exp(s)).
  -- LHS = R₃-C₄. By triangle: ‖LHS‖ ≤ 201s⁴/(2-exp(s)).
  -- For s ≥ 67/1000: 201/s ≤ 3000, so 201s⁴/(2-exp(s)) ≤ 3000s⁵/(2-exp(s)).
  -- For s < 67/1000: use 5th-order expansion.
  have hR₃ := norm_bch_quartic_remainder_le (𝕂 := 𝕂) a b hab
  have hC₄ : ‖bch_quartic_term 𝕂 a b‖ ≤ s ^ 4 :=
    norm_bch_quartic_term_le a b
  -- ‖LHS‖ ≤ ‖R₃‖ + ‖C₄‖
  have hLHS_s4 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
      200 * s ^ 4 / (2 - Real.exp s) + s ^ 4 := by
    have hsub : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b =
        (bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        bch_cubic_term 𝕂 a b) - bch_quartic_term 𝕂 a b := by abel
    rw [hsub]
    calc _ ≤ ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          bch_cubic_term 𝕂 a b‖ + ‖bch_quartic_term 𝕂 a b‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  -- Tighten: s⁴ ≤ s⁴/(2-exp(s)) since 2-exp(s) ≤ 1
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hLHS_201 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
      201 * s ^ 4 / (2 - Real.exp s) := by
    calc _ ≤ 200 * s ^ 4 / (2 - Real.exp s) + s ^ 4 := hLHS_s4
      _ ≤ 200 * s ^ 4 / (2 - Real.exp s) + s ^ 4 / (2 - Real.exp s) := by
          gcongr
          rw [le_div_iff₀ hdenom]
          nlinarith [pow_nonneg hs_nn 4]
      _ = 201 * s ^ 4 / (2 - Real.exp s) := by ring
  -- Case split
  by_cases hs_large : 67 / 1000 ≤ s
  · -- CASE 1: s ≥ 67/1000 — the crude bound suffices
    have hs_pos : 0 < s := by linarith
    have h201_le : 201 * s ^ 4 ≤ 3000 * s ^ 5 := by
      have : 201 ≤ 3000 * s := by linarith
      nlinarith [pow_nonneg hs_nn 4]
    calc _ ≤ 201 * s ^ 4 / (2 - Real.exp s) := hLHS_201
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) := by
          apply div_le_div_of_nonneg_right h201_le hdenom.le
  · -- CASE 2: s < 67/1000 — use pieceA'/pieceB' decomposition + 5th-order analysis
    push_neg at hs_large  -- hs_large : s < 67/1000
    -- Decompose LHS = pieceA' + pieceB'
    set y := exp a * exp b - 1 with hy_def
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
    have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b =
        (logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
          (4 : 𝕂)⁻¹ • y ^ 4) +
        (y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b) := by
      unfold bch bch_cubic_term bch_quartic_term; abel
    rw [hdecomp]
    -- Bound pieceA' ≤ (exp(s)-1)⁵/(2-exp(s))
    have hpieceA : ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
        (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4‖ ≤
        (Real.exp s - 1) ^ 5 / (2 - Real.exp s) :=
      calc _ ≤ ‖y‖ ^ 5 / (1 - ‖y‖) := norm_logOnePlus_sub_sub_sub_sub_le (𝕂 := 𝕂) y hy_lt
        _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
            (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
    -- Bound pieceB' — this is the main technical step
    -- Uses quartic_identity + G-level refinement + quintic_pure_identity for degree-4 cancellation
    have hpieceB : ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
        2800 * s ^ 5 / (2 - Real.exp s) := by
      -- pieceB' = quartic_pieceB - ¼y⁴ - C₄
      -- Use the quartic_identity + G-level refinement + quintic_pure_identity.
      -- After algebraic decomposition, pieceB' = [quintic terms] (degree-4 = 0).
      -- Each quintic term ≤ Cs⁵. Total ≤ 50s⁵ ≤ 2800s⁵/(2-exp(s)).
      --
      -- Define quintic exp remainders
      set G₁ := exp a - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 - (6 : 𝕂)⁻¹ • a ^ 3 -
          (24 : 𝕂)⁻¹ • a ^ 4
      set G₂ := exp b - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 - (6 : 𝕂)⁻¹ • b ^ 3 -
          (24 : 𝕂)⁻¹ • b ^ 4
      -- Quintic exp remainder bounds: ‖G₁‖ ≤ α⁵, ‖G₂‖ ≤ β⁵
      have hG₁_le : ‖G₁‖ ≤ α ^ 5 := by
        calc ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
              norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
          _ ≤ α ^ 5 := real_exp_fifth_order_le_quintic (norm_nonneg a)
              (lt_of_le_of_lt hα_le hs34)
      have hG₂_le : ‖G₂‖ ≤ β ^ 5 := by
        calc ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
              norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
          _ ≤ β ^ 5 := real_exp_fifth_order_le_quintic (norm_nonneg b)
              (lt_of_le_of_lt hβ_le hs34)
      -- STRATEGY: Reduce to ‖pieceB'‖ ≤ 50s⁵, then use algebraic decomposition.
      -- The degree-4 terms cancel by quintic_pure_identity (corrected sign).
      -- Remaining quintic+ terms are bounded by exp remainder norms.
      --
      -- Step 1: Reduce to showing ≤ 50*s^5
      suffices h_suff : ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤ 50 * s ^ 5 by
        have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
        calc _ ≤ 50 * s ^ 5 := h_suff
          _ ≤ 2800 * s ^ 5 / (2 - Real.exp s) := by
            rw [le_div_iff₀ hdenom]
            nlinarith [pow_nonneg hs_nn 5]
      -- Step 2: Set up exp remainder variables
      set D₁ := exp a - 1 - a with hD₁_def
      set D₂ := exp b - 1 - b with hD₂_def
      set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
      set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
      set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
      set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
      -- G₁ = F₁ - (24)⁻¹a⁴, G₂ = F₂ - (24)⁻¹b⁴ (already set above)
      set P := y - (a + b) with hP_def
      set z := a + b with hz_def
      -- Step 3: Norm bounds on exp remainders
      have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α :=
        norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
      have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β :=
        norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
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
      have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
        linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
      have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
        have h := Real.norm_exp_sub_one_sub_id_le
          (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
        rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn,
             Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
      have hs56 : s < 5 / 6 := by linarith
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
      -- Composite s-power bounds
      have hz_le : ‖z‖ ≤ s := by
        calc ‖z‖ = ‖a + b‖ := by rw [hz_def]
          _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
          _ = s := by rw [hs_def]
      have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
        have hP_split : P = a * (exp b - 1) + D₁ * exp b + D₂ := by
          simp only [hP_def, hy_def, hD₁_def, hD₂_def, hz_def]; noncomm_ring
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
      -- Step 4: Bound ‖y⁴-z⁴‖ ≤ 15s⁵ (quintic+ from y⁴ via telescoping)
      have hy_le2 : ‖y‖ ≤ 2 * s := by
        calc ‖y‖ ≤ Real.exp s - 1 := hy_le
          _ ≤ s + s ^ 2 := by linarith [hEs2]
          _ ≤ 2 * s := by nlinarith [sq_nonneg s]
      have hy4z4 : ‖y ^ 4 - z ^ 4‖ ≤ 15 * s ^ 5 := by
        -- y⁴-z⁴ = y³P+y²Pz+yPz²+Pz³ (non-commutative telescoping)
        have htel : y ^ 4 - z ^ 4 = y ^ 3 * P + y ^ 2 * P * z +
            y * P * z ^ 2 + P * z ^ 3 := by
          simp only [hP_def, hz_def]; noncomm_ring
        -- Bound each term using ‖y‖ ≤ 2s, ‖P‖ ≤ s², ‖z‖ ≤ s
        have h1 : ‖y ^ 3 * P‖ ≤ (2*s)^3 * s^2 := by
          calc _ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ ‖y‖^3 * ‖P‖ := by gcongr; exact norm_pow_le y 3
            _ ≤ (2*s)^3 * s^2 := by
                apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_le2 3) hP_le_s2
                  (norm_nonneg _) (by positivity)
        have h2 : ‖y ^ 2 * P * z‖ ≤ (2*s)^2 * s^2 * s := by
          calc _ ≤ ‖y ^ 2 * P‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ (‖y‖^2 * ‖P‖) * ‖z‖ := by
                gcongr
                calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
                  _ ≤ _ := by gcongr; exact norm_pow_le y 2
            _ ≤ ((2*s)^2 * s^2) * s := by
                apply mul_le_mul _ hz_le (norm_nonneg _) (by positivity)
                apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_le2 2) hP_le_s2
                  (norm_nonneg _) (by positivity)
        have h3 : ‖y * P * z ^ 2‖ ≤ 2*s * s^2 * s^2 := by
          calc _ ≤ ‖y * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ (‖y‖ * ‖P‖) * ‖z‖^2 := by
                gcongr
                · exact norm_mul_le _ _
                · exact norm_pow_le z 2
            _ ≤ (2*s * s^2) * s^2 := by
                apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
                  (by positivity) (by positivity)
                exact mul_le_mul hy_le2 hP_le_s2 (norm_nonneg _) (by positivity)
        have h4 : ‖P * z ^ 3‖ ≤ s^2 * s^3 := by
          calc _ ≤ ‖P‖ * ‖z ^ 3‖ := norm_mul_le _ _
            _ ≤ ‖P‖ * ‖z‖^3 := by gcongr; exact norm_pow_le z 3
            _ ≤ s^2 * s^3 := by
                apply mul_le_mul hP_le_s2 (pow_le_pow_left₀ (norm_nonneg z) hz_le 3)
                  (by positivity) (by positivity)
        calc ‖y ^ 4 - z ^ 4‖ = ‖y ^ 3 * P + y ^ 2 * P * z +
              y * P * z ^ 2 + P * z ^ 3‖ := by rw [htel]
          _ ≤ ‖y ^ 3 * P‖ + ‖y ^ 2 * P * z‖ + ‖y * P * z ^ 2‖ + ‖P * z ^ 3‖ := by
              calc _ ≤ ‖y ^ 3 * P + y ^ 2 * P * z + y * P * z ^ 2‖ + _ := norm_add_le _ _
                _ ≤ (‖y ^ 3 * P + y ^ 2 * P * z‖ + _) + _ := by gcongr; exact norm_add_le _ _
                _ ≤ _ := by linarith [norm_add_le (y ^ 3 * P) (y ^ 2 * P * z)]
          _ ≤ (2*s)^3*s^2 + (2*s)^2*s^2*s + 2*s*s^2*s^2 + s^2*s^3 := by linarith
          _ = 15 * s ^ 5 := by ring
      -- Step 5: Additional norm bounds needed for the quintic+ terms
      have hS_le : ‖P - (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2)‖ ≤
          5 * s ^ 3 := by
        -- S = P - P₂ = E₁+E₂+aD₂+D₁b+D₁D₂ (starts at degree 3)
        have hS_eq : P - (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) =
            E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂ := by
          simp only [hP_def, hy_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hz_def]
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
          _ ≤ 5 * s ^ 3 := by nlinarith [pow_le_pow_left₀ hα_nn hα_le 3,
              pow_le_pow_left₀ hβ_nn hβ_le 3, pow_le_pow_left₀ hα_nn hα_le 2,
              pow_le_pow_left₀ hβ_nn hβ_le 2, pow_nonneg hs_nn 4]
      -- Step 6: Bound using individual quintic+ terms
      -- Each group ≤ Cs⁵ by the bounds proved above.
      have hG₁_s5 : ‖G₁‖ ≤ s ^ 5 :=
        le_trans hG₁_le (pow_le_pow_left₀ hα_nn hα_le 5)
      have hG₂_s5 : ‖G₂‖ ≤ s ^ 5 :=
        le_trans hG₂_le (pow_le_pow_left₀ hβ_nn hβ_le 5)
      have haF₂ : ‖a * F₂‖ ≤ s ^ 5 :=
        calc _ ≤ ‖a‖ * ‖F₂‖ := norm_mul_le _ _
          _ ≤ α * β ^ 4 := mul_le_mul_of_nonneg_left (le_trans hF₂_le hFb4) hα_nn
          _ ≤ s * s ^ 4 :=
              mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) hs_nn
          _ = s ^ 5 := by ring
      have hF₁b : ‖F₁ * b‖ ≤ s ^ 5 :=
        calc _ ≤ ‖F₁‖ * ‖b‖ := norm_mul_le _ _
          _ ≤ α ^ 4 * β := mul_le_mul (le_trans hF₁_le hFa4) le_rfl hβ_nn (by positivity)
          _ ≤ s ^ 4 * s :=
              mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4) hβ_le (by positivity) (by positivity)
          _ = s ^ 5 := by ring
      -- Step 6a: Set up the I₁/I₂ decomposition (same as quartic proof)
      have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
      set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
      set W_H1 := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          z * P - P * z - P ^ 2 with hW_H1_def
      -- H1 identity: y-z-½[a,b]-½y² = ½W
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
      -- I₁ = ½W + ⅓z³ - C₃, I₂ = ⅓(y³-z³)
      set I₁ := (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 -
          bch_cubic_term 𝕂 a b with hI₁_def
      set I₂ := (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) with hI₂_def
      -- pieceB' = I₁ + I₂ - ¼y⁴ - C₄
      have hpB_split : y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b =
          I₁ + I₂ - (4 : 𝕂)⁻¹ • y ^ 4 - bch_quartic_term 𝕂 a b := by
        -- Rewrite y-z-½[a,b]-½y² = ½W by H1 identity
        conv_lhs => rw [show y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
            (2 : 𝕂)⁻¹ • y ^ 2 = (2 : 𝕂)⁻¹ • W_H1 from hH1]
        -- Now LHS = ½W+⅓y³-¼y⁴-C₃-C₄, RHS = I₁+I₂-¼y⁴-C₄
        -- Expand I₁ and I₂ definitions and simplify ⅓(y³-z³) = ⅓y³-⅓z³
        simp only [hI₁_def, hI₂_def, smul_sub]
        abel
      -- Step 6b: Apply quartic_identity to I₁
      have hI₁_eq2 : I₁ = (2 : 𝕂)⁻¹ • W_H1 +
          (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b := rfl
      have hI₁_quartic : I₁ =
          F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
          (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
          (2 : 𝕂)⁻¹ • P ^ 2 := by
        rw [hI₁_eq2]; exact quartic_identity 𝕂 (exp a) (exp b) a b
      -- Step 6c: Define degree-4 correction terms (matching quintic_pure_identity)
      -- corr₁ = degree-4 of I₁, corr₂ = degree-4 of I₂
      set T₃ := (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)
      set P₂ := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
      -- [A]+[B]+[C]: degree-4 of I₁
      let corr₁ := (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
          (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
          (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
          (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
          (2 : 𝕂)⁻¹ • P₂ ^ 2
      -- [D]: degree-4 of I₂
      let corr₂ := (3 : 𝕂)⁻¹ • (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2)
      -- Step 6d: Show QPI gives corr₁+corr₂-¼z⁴ = C₄
      have hQPI : corr₁ + corr₂ - (4 : 𝕂)⁻¹ • z ^ 4 -
          bch_quartic_term 𝕂 a b = 0 := by
        show (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
            (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
            (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
            (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
            (2 : 𝕂)⁻¹ • P₂ ^ 2 +
            (3 : 𝕂)⁻¹ • (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2) -
            (4 : 𝕂)⁻¹ • z ^ 4 - bch_quartic_term 𝕂 a b = 0
        -- This matches quintic_pure_identity after expanding z = a+b
        -- and the T₃, P₂ definitions.
        convert quintic_pure_identity 𝕂 a b using 2 <;> simp [hz_def] <;> ring
      -- Step 6e: Rearrange pieceB' using degree-4 cancellation
      rw [hpB_split]
      -- Goal: ‖I₁+I₂-¼y⁴-C₄‖ ≤ 50s⁵
      -- Use hQPI to cancel: I₁+I₂-¼y⁴-C₄ = (I₁-corr₁)+(I₂-corr₂)-¼(y⁴-z⁴)
      -- since corr₁+corr₂-¼z⁴ = C₄ by hQPI.
      have hrewrite : I₁ + I₂ - (4 : 𝕂)⁻¹ • y ^ 4 - bch_quartic_term 𝕂 a b =
          (I₁ - corr₁) + (I₂ - corr₂) - (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4) := by
        -- LHS - RHS = corr₁+corr₂-¼z⁴-C₄ = 0 (by QPI)
        rw [sub_eq_zero.symm]  -- convert goal A=B to A-B=0
        convert hQPI using 1    -- match _ = 0 with _ = 0
        simp only [smul_sub]
        abel
      rw [hrewrite]
      -- Step 6f: Bound each quintic+ group via triangle inequality
      -- Group 1: ‖I₁-corr₁‖ ≤ 20s⁵ (quartic_identity refined to quintic)
      have hGroup1 : ‖I₁ - corr₁‖ ≤ 20 * s ^ 5 := by
        -- Algebraic identity: I₁-corr₁ = quintic+ terms
        -- From quartic_identity: I₁ = F₁+F₂+aE₂+E₁b+D₁D₂-½(z(E₁+E₂+Q)+(E₁+E₂+Q)z)-½P²
        -- Subtract corr₁ = [A]+[B]+[C] (degree-4 pure terms)
        -- Result: G₁+G₂+aF₂+F₁b+½(a²E₂+E₁b²)+E₁E₂ - ½(z·S_rest+S_rest·z) - ½(P₂S+SP₂+S²)
        -- where S_rest = (E₁+E₂+Q)-T₃ and S = P-P₂.
        -- Each of the ~10 terms is bounded by ≤ Cs⁵.
        -- Regroup I₁-corr₁ as sum of small differences, then bound each
        rw [hI₁_quartic]
        -- I₁ = F₁+F₂+aE₂+E₁b+D₁D₂-½(z(E₁+E₂+Q)+(E₁+E₂+Q)z)-½P²
        -- corr₁ (let, transparent) = degree-4 pure terms
        -- Regroup: (I₁ terms) - corr₁ = Σ(quartic term - its degree-4 part)
        have h_regroup :
            F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
              (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
              (2 : 𝕂)⁻¹ • P ^ 2 - corr₁ =
            (F₁ - (24 : 𝕂)⁻¹ • a ^ 4) + (F₂ - (24 : 𝕂)⁻¹ • b ^ 4) +
            (a * E₂ - (6 : 𝕂)⁻¹ • (a * b ^ 3)) +
            (E₁ * b - (6 : 𝕂)⁻¹ • (a ^ 3 * b)) +
            (D₁ * D₂ - (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2)) +
            ((2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
              (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z)) +
            ((2 : 𝕂)⁻¹ • P₂ ^ 2 - (2 : 𝕂)⁻¹ • P ^ 2) := by
          -- Expand corr₁ (let binding) explicitly so abel can see all atoms
          change F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
              (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
              (2 : 𝕂)⁻¹ • P ^ 2 -
              ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
               (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
               (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
               (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
               (2 : 𝕂)⁻¹ • P₂ ^ 2) = _
          abel
        -- After h_regroup, bound 7 groups by triangle inequality.
        -- Each group ≤ Cs⁵ from proved bounds (G_i≤s⁵, aF₂≤s⁵, F₁b≤s⁵, etc.).
        -- Total: ≤ 20s⁵.
        rw [h_regroup]
        -- Simplify each group using definitional identities
        have hA : F₁ - (24 : 𝕂)⁻¹ • a ^ 4 = G₁ := by dsimp only
        have hB : F₂ - (24 : 𝕂)⁻¹ • b ^ 4 = G₂ := by dsimp only
        have hC : a * E₂ - (6 : 𝕂)⁻¹ • (a * b ^ 3) = a * F₂ := by
          have : E₂ = F₂ + (6 : 𝕂)⁻¹ • b ^ 3 := by rw [hF₂_def]; abel
          rw [this, mul_add, mul_smul_comm]; abel
        have hDt : E₁ * b - (6 : 𝕂)⁻¹ • (a ^ 3 * b) = F₁ * b := by
          have : E₁ = F₁ + (6 : 𝕂)⁻¹ • a ^ 3 := by rw [hF₁_def]; abel
          rw [this, add_mul, smul_mul_assoc]; abel
        have hEt : D₁ * D₂ - (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) =
            E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂) + (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) := by
          have hd1 : D₁ = E₁ + (2 : 𝕂)⁻¹ • a ^ 2 := by rw [hE₁_def]; abel
          have hd2 : D₂ = E₂ + (2 : 𝕂)⁻¹ • b ^ 2 := by rw [hE₂_def]; abel
          rw [hd1, hd2]; simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            smul_smul, show (2:𝕂)⁻¹*(2:𝕂)⁻¹=(4:𝕂)⁻¹ from by norm_num, smul_add]; abel
        have hFt : (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
            (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) =
            (2 : 𝕂)⁻¹ • (z * (T₃ - E₁ - E₂ - Q) + (T₃ - E₁ - E₂ - Q) * z) := by
          rw [← smul_sub]; congr 1; noncomm_ring
        have hGt : (2 : 𝕂)⁻¹ • P₂ ^ 2 - (2 : 𝕂)⁻¹ • P ^ 2 =
            (2 : 𝕂)⁻¹ • (P₂ ^ 2 - P ^ 2) := (smul_sub _ _ _).symm
        rw [hA, hB, hC, hDt, hEt, hFt, hGt]
        have hT₃_exp : T₃ = (6:𝕂)⁻¹ • a^3 + (6:𝕂)⁻¹ • b^3 + (2:𝕂)⁻¹ • (a*b^2) +
            (2:𝕂)⁻¹ • (a^2*b) := by dsimp only
        have hSrest_eq : T₃ - E₁ - E₂ - Q = -(F₁+F₂+a*E₂+E₁*b+D₁*D₂) := by
          simp only [hT₃_exp, hQ_def, hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def,
            mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub,
            smul_add]; abel
        -- Component s⁴ bounds
        have hF₁s : ‖F₁‖ ≤ s^4 := le_trans (le_trans hF₁_le hFa4) (pow_le_pow_left₀ hα_nn hα_le 4)
        have hF₂s : ‖F₂‖ ≤ s^4 := le_trans (le_trans hF₂_le hFb4) (pow_le_pow_left₀ hβ_nn hβ_le 4)
        have haEs : ‖a*E₂‖ ≤ s^4 :=
          calc _ ≤ ‖a‖*‖E₂‖ := norm_mul_le _ _
            _ ≤ α*(β^3) := mul_le_mul_of_nonneg_left (le_trans hE₂_le hEb3) hα_nn
            _ ≤ s*s^3 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) hs_nn
            _ = s^4 := by ring
        have hEbs : ‖E₁*b‖ ≤ s^4 :=
          calc _ ≤ ‖E₁‖*‖b‖ := norm_mul_le _ _
            _ ≤ (α^3)*β := mul_le_mul (le_trans hE₁_le hEa3) le_rfl hβ_nn (by positivity)
            _ ≤ s^3*s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3) hβ_le (by positivity) (by positivity)
            _ = s^4 := by ring
        have hDDs : ‖D₁*D₂‖ ≤ s^4 :=
          calc _ ≤ ‖D₁‖*‖D₂‖ := norm_mul_le _ _
            _ ≤ (α^2)*(β^2) := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
                (norm_nonneg _) (by positivity)
            _ ≤ s^2*s^2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
                (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
            _ = s^4 := by ring
        have hSrest_le : ‖T₃-E₁-E₂-Q‖ ≤ 5*s^4 := by
          rw [hSrest_eq, norm_neg]; linarith [norm_add_le F₁ F₂,
            norm_add_le (F₁+F₂) (a*E₂), norm_add_le (F₁+F₂+a*E₂) (E₁*b),
            norm_add_le (F₁+F₂+a*E₂+E₁*b) (D₁*D₂)]
        have h2_le : ‖(2:𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
        have h2eq : ‖(2:𝕂)⁻¹‖ = (2:ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
        have hP₂_le : ‖P₂‖ ≤ s^2 := by
          have h1 : ‖a*b‖ ≤ α*β := norm_mul_le _ _
          have h2 : ‖(2:𝕂)⁻¹•a^2‖ ≤ α^2 :=
            calc _ ≤ 1*‖a‖^2 := by
                  exact (norm_smul_le _ _).trans (mul_le_mul h2_le (norm_pow_le a 2)
                    (norm_nonneg _) (by norm_num))
              _ = α^2 := one_mul _
          have h3 : ‖(2:𝕂)⁻¹•b^2‖ ≤ β^2 :=
            calc _ ≤ 1*‖b‖^2 := by
                  exact (norm_smul_le _ _).trans (mul_le_mul h2_le (norm_pow_le b 2)
                    (norm_nonneg _) (by norm_num))
              _ = β^2 := one_mul _
          have hP₂_triangle : ‖P₂‖ ≤ ‖a*b‖ + ‖(2:𝕂)⁻¹•a^2‖ + ‖(2:𝕂)⁻¹•b^2‖ := by
            show ‖(a * b + (2 : 𝕂)⁻¹ • a ^ 2) + (2 : 𝕂)⁻¹ • b ^ 2‖ ≤ _
            have n1 := norm_add_le (a * b + (2 : 𝕂)⁻¹ • a ^ 2) ((2 : 𝕂)⁻¹ • b ^ 2)
            have n2 := norm_add_le (a * b) ((2 : 𝕂)⁻¹ • a ^ 2)
            linarith
          have hs2 : s^2 = α^2 + 2*α*β + β^2 := by rw [hs_def]; ring
          have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
          linarith
        -- Group 5: ‖E₁E₂+½a²E₂+½E₁b²‖ ≤ 3s⁵
        have b5 : ‖E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2)‖ ≤ 3*s^5 := by
          have t1 : ‖E₁*E₂‖ ≤ s^5 :=
            calc _ ≤ (α^3)*(β^3) :=
                  (norm_mul_le _ _).trans (mul_le_mul (le_trans hE₁_le hEa3) (le_trans hE₂_le hEb3)
                    (norm_nonneg _) (by positivity))
              _ ≤ s^3*s^3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
                  (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
              _ = s^6 := by ring
              _ ≤ s^5 := by nlinarith [pow_nonneg hs_nn 5]
          have t2 : ‖(2:𝕂)⁻¹•(a^2*E₂)‖ ≤ s^5 := by
            have ha2e : ‖a^2*E₂‖ ≤ α^2*β^3 :=
              calc _ ≤ ‖a^2‖*‖E₂‖ := norm_mul_le _ _
                _ ≤ (‖a‖^2)*(β^3) := mul_le_mul (norm_pow_le a 2)
                    (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
            calc _ ≤ 1*(α^2*β^3) :=
                  (norm_smul_le _ _).trans (mul_le_mul h2_le ha2e (norm_nonneg _) (by norm_num))
              _ ≤ s^2*s^3 := by
                  rw [one_mul]
                  exact mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
                    (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
              _ = s^5 := by ring
          have t3 : ‖(2:𝕂)⁻¹•(E₁*b^2)‖ ≤ s^5 := by
            have he1b : ‖E₁*b^2‖ ≤ α^3*β^2 :=
              calc _ ≤ ‖E₁‖*‖b^2‖ := norm_mul_le _ _
                _ ≤ (α^3)*(‖b‖^2) := mul_le_mul (le_trans hE₁_le hEa3)
                    (norm_pow_le b 2) (norm_nonneg _) (by positivity)
            calc _ ≤ 1*(α^3*β^2) :=
                  (norm_smul_le _ _).trans (mul_le_mul h2_le he1b (norm_nonneg _) (by norm_num))
              _ ≤ s^3*s^2 := by
                  rw [one_mul]
                  exact mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
                    (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
              _ = s^5 := by ring
          linarith [norm_add_le (E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)) ((2:𝕂)⁻¹•(E₁*b^2)),
            norm_add_le (E₁*E₂) ((2:𝕂)⁻¹•(a^2*E₂))]
        -- Group 6: ‖½(z·Δ+Δ·z)‖ ≤ 5s⁵ where Δ=T₃-E₁-E₂-Q
        have b6 : ‖(2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z)‖ ≤ 5*s^5 := by
          have h1 : ‖z*(T₃-E₁-E₂-Q)‖ ≤ s*(5*s^4) :=
            (norm_mul_le _ _).trans (mul_le_mul hz_le hSrest_le (norm_nonneg _) hs_nn)
          have h2 : ‖(T₃-E₁-E₂-Q)*z‖ ≤ (5*s^4)*s :=
            (norm_mul_le _ _).trans (mul_le_mul hSrest_le hz_le (norm_nonneg _) (by positivity))
          have htri := norm_add_le (z*(T₃-E₁-E₂-Q)) ((T₃-E₁-E₂-Q)*z)
          have hsum : ‖z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z‖ ≤ 2*s*(5*s^4) := by linarith
          calc ‖(2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z)‖
              ≤ ‖(2:𝕂)⁻¹‖ * ‖z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z‖ := norm_smul_le _ _
            _ ≤ (2:ℝ)⁻¹ * (2*s*(5*s^4)) := by
                rw [h2eq]; exact mul_le_mul_of_nonneg_left hsum (by norm_num)
            _ = 5*s^5 := by ring
        -- Group 7: ‖½(P₂²-P²)‖ ≤ 6s⁵
        have b7 : ‖(2:𝕂)⁻¹•(P₂^2-P^2)‖ ≤ 6*s^5 := by
          have hPd : P₂^2-P^2 = -(P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2) := by
            have hp : P = P₂+(P-P₂) := by abel
            rw [hp]; noncomm_ring
          have hp1 : ‖P₂*(P-P₂)‖ ≤ s^2*(5*s^3) :=
            (norm_mul_le _ _).trans (mul_le_mul hP₂_le hS_le (norm_nonneg _) (by positivity))
          have hp2 : ‖(P-P₂)*P₂‖ ≤ (5*s^3)*s^2 :=
            (norm_mul_le _ _).trans (mul_le_mul hS_le hP₂_le (norm_nonneg _) (by positivity))
          have hp3 : ‖(P-P₂)^2‖ ≤ (5*s^3)^2 :=
            (norm_pow_le _ 2).trans (pow_le_pow_left₀ (norm_nonneg _) hS_le 2)
          rw [hPd, smul_neg, norm_neg]
          have ht1 := norm_add_le (P₂*(P-P₂)+(P-P₂)*P₂) ((P-P₂)^2)
          have ht2 := norm_add_le (P₂*(P-P₂)) ((P-P₂)*P₂)
          have hsum : ‖P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2‖ ≤ 2*s^2*(5*s^3)+(5*s^3)^2 := by
            linarith
          calc ‖(2:𝕂)⁻¹•(P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2)‖
              ≤ ‖(2:𝕂)⁻¹‖ * ‖P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2‖ := norm_smul_le _ _
            _ ≤ (2:ℝ)⁻¹ * (2*s^2*(5*s^3)+(5*s^3)^2) := by
                rw [h2eq]; exact mul_le_mul_of_nonneg_left hsum (by norm_num)
            _ ≤ 6*s^5 := by nlinarith [pow_nonneg hs_nn 5, pow_nonneg hs_nn 6]
        -- Final triangle inequality: 1+1+1+1+3+5+6 = 18 ≤ 20
        have n1 := norm_add_le G₁ G₂
        have n2 := norm_add_le (G₁+G₂) (a*F₂)
        have n3 := norm_add_le (G₁+G₂+a*F₂) (F₁*b)
        have n4 := norm_add_le (G₁+G₂+a*F₂+F₁*b) (E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2))
        have n5 := norm_add_le
          (G₁+G₂+a*F₂+F₁*b+(E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2)))
          ((2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z))
        have n6 := norm_add_le
          (G₁+G₂+a*F₂+F₁*b+(E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2))+
            (2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z))
          ((2:𝕂)⁻¹•(P₂^2-P^2))
        have hcomp_sum : ‖G₁‖+‖G₂‖+‖a*F₂‖+‖F₁*b‖+
              ‖E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2)‖+
              ‖(2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z)‖+
              ‖(2:𝕂)⁻¹•(P₂^2-P^2)‖ ≤ 18 * s^5 := by
          linarith [hG₁_s5, hG₂_s5, haF₂, hF₁b, b5, b6, b7]
        linarith [hcomp_sum, pow_nonneg hs_nn 5]
      -- Group 2: ‖I₂-corr₂‖ ≤ 8s⁵ (I₂ refined by P→P₂+S)
      have hGroup2 : ‖I₂ - corr₂‖ ≤ 8 * s ^ 5 := by
        -- Factor out ⅓: I₂-corr₂ = ⅓•((y³-z³)-(z²P₂+zP₂z+P₂z²))
        -- Inner ring identity: using y=z+P, the inner expr equals
        -- z²(P-P₂)+z(P-P₂)z+(P-P₂)z²+zP²+PzP+P²z+P³
        have hy_zP : y = z + P := by simp only [hP_def, hz_def]; abel
        have hinner : y ^ 3 - z ^ 3 - (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2) =
            z ^ 2 * (P - P₂) + z * (P - P₂) * z + (P - P₂) * z ^ 2 +
            z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3 := by
          rw [hy_zP]; noncomm_ring
        have hI₂_alg : I₂ - corr₂ = (3 : 𝕂)⁻¹ •
            (z ^ 2 * (P - P₂) + z * (P - P₂) * z + (P - P₂) * z ^ 2 +
             z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3) := by
          -- Factor ⅓ from I₂-corr₂. Since y = P + z definitionally (by set defs),
          -- the ring identity hinner is verified by Lean's kernel.
          rw [hI₂_def, ← smul_sub, hinner]
        rw [hI₂_alg]
        -- Bound each of 7 terms using ‖P-P₂‖ ≤ 5s³, ‖P‖ ≤ s², ‖z‖ ≤ s
        have hSn : ‖P - P₂‖ ≤ 5 * s ^ 3 := hS_le
        -- Triangle inequality: ‖⅓•(sum)‖ ≤ ‖⅓‖·(sum of norms) ≤ 1·(sum of norms)
        have h3le : ‖(3 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
        -- Each term: z²S ≤ s²·5s³ = 5s⁵, zP² ≤ s·s⁴ = s⁵, P³ ≤ s⁶
        -- 7 terms: 3×5s⁵ + 3×s⁵ + s⁶ = 18s⁵+s⁶ ≤ 19s⁵
        -- With ‖⅓‖ ≤ 1: total ≤ 19s⁵ ≤ 8s⁵? NO — need tighter.
        -- Actually ‖⅓‖ = 1/3, so total ≤ ⅓·19s⁵ ≈ 6.3s⁵ ≤ 8s⁵ ✓
        -- But using ‖⅓‖ ≤ 1 gives 19s⁵ which is > 8s⁵.
        -- Use exact value: ‖⅓‖ = 1/3.
        have h3eq : ‖(3 : 𝕂)⁻¹‖ = (3 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
        calc _ ≤ ‖(3 : 𝕂)⁻¹‖ * ‖z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                (P - P₂) * z ^ 2 + z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3‖ :=
              norm_smul_le _ _
          _ ≤ (3 : ℝ)⁻¹ * (19 * s ^ 5) := by
              rw [h3eq]; gcongr
              -- Bound inner sum by 19s⁵ via triangle inequality
              have t1 : ‖z ^ 2 * (P - P₂)‖ ≤ 5 * s ^ 5 := by
                calc _ ≤ ‖z‖^2 * ‖P - P₂‖ := by
                      calc _ ≤ ‖z ^ 2‖ * _ := norm_mul_le _ _
                        _ ≤ _ := by gcongr; exact norm_pow_le z 2
                  _ ≤ s^2 * (5*s^3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
                      hSn (norm_nonneg _) (by positivity)
                  _ = _ := by ring
              have t2 : ‖z * (P - P₂) * z‖ ≤ 5 * s ^ 5 := by
                calc _ ≤ ‖z‖ * ‖P - P₂‖ * ‖z‖ := by
                      calc _ ≤ ‖z * (P - P₂)‖ * ‖z‖ := norm_mul_le _ _
                        _ ≤ _ := by gcongr; exact norm_mul_le _ _
                  _ ≤ s * (5*s^3) * s := mul_le_mul (mul_le_mul hz_le hSn (norm_nonneg _)
                      (by positivity)) hz_le (norm_nonneg _) (by positivity)
                  _ = _ := by ring
              have t3 : ‖(P - P₂) * z ^ 2‖ ≤ 5 * s ^ 5 := by
                calc _ ≤ ‖P - P₂‖ * ‖z‖^2 := by
                      calc _ ≤ _ * ‖z ^ 2‖ := norm_mul_le _ _
                        _ ≤ _ := by gcongr; exact norm_pow_le z 2
                  _ ≤ (5*s^3) * s^2 := mul_le_mul hSn (pow_le_pow_left₀ (norm_nonneg z)
                      hz_le 2) (by positivity) (by positivity)
                  _ = 5 * s ^ 5 := by ring
              have t4 : ‖z * P ^ 2‖ ≤ s ^ 5 := by
                calc _ ≤ ‖z‖ * ‖P ^ 2‖ := norm_mul_le _ _
                  _ ≤ ‖z‖ * ‖P‖ ^ 2 := by gcongr; exact norm_pow_le P 2
                  _ ≤ s * (s ^ 2) ^ 2 := by
                      exact mul_le_mul hz_le (pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 2)
                        (by positivity) hs_nn
                  _ = s ^ 5 := by ring
              have t5 : ‖P * z * P‖ ≤ s ^ 5 := by
                calc _ ≤ ‖P * z‖ * ‖P‖ := norm_mul_le _ _
                  _ ≤ (‖P‖ * ‖z‖) * ‖P‖ := by gcongr; exact norm_mul_le _ _
                  _ ≤ (s ^ 2 * s) * s ^ 2 := by
                      exact mul_le_mul (mul_le_mul hP_le_s2 hz_le (norm_nonneg _)
                        (by positivity)) hP_le_s2 (norm_nonneg _) (by positivity)
                  _ = s ^ 5 := by ring
              have t6 : ‖P ^ 2 * z‖ ≤ s ^ 5 := by
                calc _ ≤ ‖P ^ 2‖ * ‖z‖ := norm_mul_le _ _
                  _ ≤ ‖P‖ ^ 2 * ‖z‖ := by gcongr; exact norm_pow_le P 2
                  _ ≤ (s ^ 2) ^ 2 * s := by
                      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 2)
                        hz_le (norm_nonneg _) (by positivity)
                  _ = s ^ 5 := by ring
              have t7 : ‖P ^ 3‖ ≤ s ^ 5 := by
                calc _ ≤ ‖P‖^3 := norm_pow_le P 3
                  _ ≤ (s^2)^3 := pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 3
                  _ = s ^ 6 := by ring
                  _ ≤ s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
              -- Total via triangle inequality
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2 + z * P ^ 2 + P * z * P + P ^ 2 * z) (P ^ 3)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2 + z * P ^ 2 + P * z * P) (P ^ 2 * z)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2 + z * P ^ 2) (P * z * P)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2) (z * P ^ 2)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z) ((P - P₂) * z ^ 2)
              have := norm_add_le (z ^ 2 * (P - P₂)) (z * (P - P₂) * z)
              nlinarith
          _ ≤ 8 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
      -- Group 3: ¼‖y⁴-z⁴‖ ≤ ¼·15s⁵
      have hGroup3 : ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖ ≤ 4 * s ^ 5 :=
        calc _ ≤ ‖(4 : 𝕂)⁻¹‖ * ‖y ^ 4 - z ^ 4‖ := norm_smul_le _ _
          _ ≤ (4 : ℝ)⁻¹ * (15 * s ^ 5) := by
              have : ‖(4 : 𝕂)⁻¹‖ = (4 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
              rw [this]; exact mul_le_mul_of_nonneg_left hy4z4 (by norm_num)
          _ ≤ 4 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
      -- Combine via triangle inequality
      calc ‖(I₁ - corr₁) + (I₂ - corr₂) - (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖
          ≤ ‖(I₁ - corr₁) + (I₂ - corr₂)‖ + ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖ :=
            norm_sub_le _ _
        _ ≤ (‖I₁ - corr₁‖ + ‖I₂ - corr₂‖) + ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ (20 * s ^ 5 + 8 * s ^ 5) + 4 * s ^ 5 := by linarith
        _ = 32 * s ^ 5 := by ring
        _ ≤ 50 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
    -- Combine pieceA' + pieceB'
    have hE1_nn : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
    have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
      linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
    have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
      have h := Real.norm_exp_sub_one_sub_id_le
        (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
      rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn, Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
    have hexp5 : (Real.exp s - 1) ^ 5 ≤ 200 * s ^ 5 :=
      calc (Real.exp s - 1) ^ 5 ≤ (s + s ^ 2) ^ 5 := pow_le_pow_left₀ hE1_nn (by linarith) 5
        _ = s ^ 5 * (1 + s) ^ 5 := by ring
        _ ≤ s ^ 5 * 200 := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs_nn 5)
            have : (1 + s) ^ 5 ≤ (1 + 1) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
            linarith
        _ = 200 * s ^ 5 := by ring
    calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
            (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4‖ +
          ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
            (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
            bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ := norm_add_le _ _
      _ ≤ (Real.exp s - 1) ^ 5 / (2 - Real.exp s) +
          2800 * s ^ 5 / (2 - Real.exp s) := by linarith [hpieceA, hpieceB]
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) := by
          calc _ = ((Real.exp s - 1) ^ 5 + 2800 * s ^ 5) / (2 - Real.exp s) := by rw [add_div]
            _ ≤ (200 * s ^ 5 + 2800 * s ^ 5) / (2 - Real.exp s) := by
                apply div_le_div_of_nonneg_right _ hdenom.le; linarith
            _ = 3000 * s ^ 5 / (2 - Real.exp s) := by ring_nf

include 𝕂 in
/-- **Sixth-order BCH remainder, large-s case** (private helper for the future
`norm_bch_sextic_remainder_le`).

Crude bound for `‖a‖+‖b‖ ≥ 1/10`: combines `norm_bch_quintic_remainder_le`
with `‖C₅‖ ≤ s⁵` to give

  `‖LHS_sextic‖ ≤ 3001·s⁵/(2-exp(s)) ≤ 100000·s⁶/(2-exp(s))`

(since `3001 ≤ 100000·s` when `s ≥ 1/10`).

This is the crude case of the full sextic remainder theorem. The full
theorem requires the small-s analytic case (`s < 1/10`), which uses
`sextic_pure_identity` for the deg-5 cancellation (~700 lines, deferred to
future session). See `claude/sextic_remainder_strategy.md`. -/
private theorem norm_bch_sextic_remainder_large_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_large : 1 / 10 ≤ ‖a‖ + ‖b‖) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b‖ ≤
      100000 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hR₄ := norm_bch_quintic_remainder_le (𝕂 := 𝕂) a b hab
  have hC₅ : ‖bch_quintic_term 𝕂 a b‖ ≤ s ^ 5 := norm_bch_quintic_term_le a b
  -- Algebraic split: LHS_sextic = LHS_quintic - C₅
  have hLHS_eq : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b - bch_quintic_term 𝕂 a b =
      (bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
       bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b) - bch_quintic_term 𝕂 a b := by abel
  -- ‖LHS‖ ≤ 3000s⁵/(2-exp(s)) + s⁵ ≤ 3001 s⁵/(2-exp(s))
  have hLHS_3001 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b - bch_quintic_term 𝕂 a b‖ ≤
      3001 * s ^ 5 / (2 - Real.exp s) := by
    rw [hLHS_eq]
    calc _ ≤ ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ + ‖bch_quintic_term 𝕂 a b‖ :=
        norm_sub_le _ _
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) + s ^ 5 := by linarith
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) + s ^ 5 / (2 - Real.exp s) := by
          gcongr; rw [le_div_iff₀ hdenom]
          nlinarith [pow_nonneg hs_nn 5]
      _ = 3001 * s ^ 5 / (2 - Real.exp s) := by ring
  -- Bound 3001·s⁵ ≤ 100000·s⁶ via 3001 ≤ 100000·s (using s ≥ 1/10)
  have h_le : 3001 * s ^ 5 ≤ 100000 * s ^ 6 := by
    have h3001 : 3001 ≤ 100000 * s := by linarith
    nlinarith [pow_nonneg hs_nn 5]
  calc _ ≤ 3001 * s ^ 5 / (2 - Real.exp s) := hLHS_3001
    _ ≤ 100000 * s ^ 6 / (2 - Real.exp s) :=
        div_le_div_of_nonneg_right h_le hdenom.le

/-! ### Sextic remainder small-s case helpers

These are building blocks for the (future) `norm_bch_sextic_remainder_small_s_le`
which handles `s < 1/10` via the deg-5 cancellation in `sextic_pure_identity`.

Each helper is a self-contained lemma about non-commutative algebra,
provable by `noncomm_ring` after scalar clearing.
-/

/-- 5-fold non-commutative telescoping: `y⁵ - (y - P)⁵` expands as a sum of
five 5-letter words, each with one `P` factor and four `y`/`(y-P)` factors. -/
private theorem pow5_sub_zpow5_telescope (y P : 𝔸) :
    y ^ 5 - (y - P) ^ 5 =
      y ^ 4 * P + y ^ 3 * P * (y - P) + y ^ 2 * P * (y - P) ^ 2 +
        y * P * (y - P) ^ 3 + P * (y - P) ^ 4 := by
  noncomm_ring

/-- 4-fold non-commutative telescoping: `y⁴ - (y - P)⁴` expands as a sum of
four 4-letter words, each with one `P` factor and three `y`/`(y-P)` factors. -/
private theorem pow4_sub_zpow4_telescope (y P : 𝔸) :
    y ^ 4 - (y - P) ^ 4 =
      y ^ 3 * P + y ^ 2 * P * (y - P) + y * P * (y - P) ^ 2 + P * (y - P) ^ 3 := by
  noncomm_ring

/-- 3-fold non-commutative telescoping: `y³ - (y - P)³`. -/
private theorem pow3_sub_zpow3_telescope (y P : 𝔸) :
    y ^ 3 - (y - P) ^ 3 =
      y ^ 2 * P + y * P * (y - P) + P * (y - P) ^ 2 := by
  noncomm_ring

/-- Algebraic decomposition of `y⁴ - z⁴ - y4_5` where `z = y - P` and
`y4_5 = z³T₂ + z²T₂z + zT₂z² + T₂z³` is the deg-5 contribution from
`y⁴ = (z + T₂ + ...)⁴`. Expresses the difference as a sum of 7 deg-6+
terms in the BCH context where `‖y‖ ≤ 2s`, `‖P‖ ≤ s²`, `‖z‖ ≤ s`,
`‖P-T₂‖ ≤ 5s³`. -/
private theorem y4_sub_z4_sub_y4_5_decomp (y P T₂ : 𝔸) :
    y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) =
      (y - P) ^ 3 * (P - T₂) + (y - P) ^ 2 * (P - T₂) * (y - P) +
        (y - P) * (P - T₂) * (y - P) ^ 2 + (P - T₂) * (y - P) ^ 3 +
      (y ^ 3 - (y - P) ^ 3) * P + (y ^ 2 - (y - P) ^ 2) * P * (y - P) +
      P * P * (y - P) ^ 2 := by
  noncomm_ring

/-- Norm bound for the 5-fold telescoping: given `‖y‖ ≤ 2s`, `‖z‖ ≤ s`,
`‖P‖ ≤ s²`, `‖y⁵ - z⁵‖ ≤ 31·s⁶`. Used in the small-s case of the sextic
remainder bound. -/
private theorem norm_pow5_sub_zpow5_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 5 - (y - P) ^ 5‖ ≤ 31 * s ^ 6 := by
  rw [pow5_sub_zpow5_telescope]
  -- 5 terms: y⁴P + y³P(y-P) + y²P(y-P)² + yP(y-P)³ + P(y-P)⁴
  -- Bounds: 16s⁶ + 8s⁶ + 4s⁶ + 2s⁶ + s⁶ = 31s⁶
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have h_y4P : ‖y ^ 4 * P‖ ≤ (2 * s) ^ 4 * s ^ 2 :=
    calc ‖y ^ 4 * P‖ ≤ ‖y ^ 4‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 4 * ‖P‖ := by gcongr; exact norm_pow_le y 4
      _ ≤ (2 * s) ^ 4 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 4) hP (by positivity) (by positivity)
  have h_y3Pz : ‖y ^ 3 * P * z‖ ≤ (2 * s) ^ 3 * s ^ 2 * s :=
    calc ‖y ^ 3 * P * z‖ ≤ ‖y ^ 3 * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 3 * ‖P‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le y 3
      _ ≤ ((2 * s) ^ 3 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 3) hP
            (norm_nonneg _) (by positivity)
  have h_y2Pz2 : ‖y ^ 2 * P * z ^ 2‖ ≤ (2 * s) ^ 2 * s ^ 2 * s ^ 2 :=
    calc ‖y ^ 2 * P * z ^ 2‖ ≤ ‖y ^ 2 * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 2 * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 2
          · exact norm_pow_le z 2
      _ ≤ ((2 * s) ^ 2 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (norm_nonneg _) (by positivity)
  have h_yPz3 : ‖y * P * z ^ 3‖ ≤ 2 * s * s ^ 2 * s ^ 3 :=
    calc ‖y * P * z ^ 3‖ ≤ ‖y * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ (2 * s * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz4 : ‖P * z ^ 4‖ ≤ s ^ 2 * s ^ 4 :=
    calc ‖P * z ^ 4‖ ≤ ‖P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 4 := by gcongr; exact norm_pow_le z 4
      _ ≤ s ^ 2 * s ^ 4 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
          (by positivity) (by positivity)
  -- Sum via triangle inequality
  have ht1 := norm_add_le (y ^ 4 * P + y ^ 3 * P * z + y ^ 2 * P * z ^ 2 + y * P * z ^ 3)
    (P * z ^ 4)
  have ht2 := norm_add_le (y ^ 4 * P + y ^ 3 * P * z + y ^ 2 * P * z ^ 2) (y * P * z ^ 3)
  have ht3 := norm_add_le (y ^ 4 * P + y ^ 3 * P * z) (y ^ 2 * P * z ^ 2)
  have ht4 := norm_add_le (y ^ 4 * P) (y ^ 3 * P * z)
  nlinarith [pow_nonneg hs_nn 6]

/-- Norm bound for `y² - z²` (2-fold telescoping) where `z = y - P`,
given `‖y‖ ≤ 2s`, `‖P‖ ≤ s²`, `‖z‖ ≤ s`. -/
private theorem norm_pow2_sub_zpow2_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 2 - (y - P) ^ 2‖ ≤ 3 * s ^ 3 := by
  have hY2_eq : y ^ 2 - (y - P) ^ 2 = y * P + P * (y - P) := by noncomm_ring
  rw [hY2_eq]
  have h_yP : ‖y * P‖ ≤ 2 * s * s ^ 2 :=
    calc ‖y * P‖ ≤ ‖y‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ 2 * s * s ^ 2 := mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz : ‖P * (y - P)‖ ≤ s ^ 2 * s :=
    calc ‖P * (y - P)‖ ≤ ‖P‖ * ‖y - P‖ := norm_mul_le _ _
      _ ≤ s ^ 2 * s := mul_le_mul hP hz (norm_nonneg _) (by positivity)
  calc ‖y * P + P * (y - P)‖ ≤ ‖y * P‖ + ‖P * (y - P)‖ := norm_add_le _ _
    _ ≤ 2 * s * s ^ 2 + s ^ 2 * s := by linarith
    _ = 3 * s ^ 3 := by ring

/-- Norm bound for `y³ - z³` (3-fold telescoping). -/
private theorem norm_pow3_sub_zpow3_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 3 - (y - P) ^ 3‖ ≤ 7 * s ^ 4 := by
  rw [pow3_sub_zpow3_telescope]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have h_y2P : ‖y ^ 2 * P‖ ≤ (2 * s) ^ 2 * s ^ 2 :=
    calc ‖y ^ 2 * P‖ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 2 * ‖P‖ := by gcongr; exact norm_pow_le y 2
      _ ≤ (2 * s) ^ 2 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (by positivity) (by positivity)
  have h_yPz : ‖y * P * z‖ ≤ 2 * s * s ^ 2 * s :=
    calc ‖y * P * z‖ ≤ ‖y * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (2 * s * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz2 : ‖P * z ^ 2‖ ≤ s ^ 2 * s ^ 2 :=
    calc ‖P * z ^ 2‖ ≤ ‖P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * s ^ 2 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
          (by positivity) (by positivity)
  have ht1 := norm_add_le (y ^ 2 * P + y * P * z) (P * z ^ 2)
  have ht2 := norm_add_le (y ^ 2 * P) (y * P * z)
  nlinarith

/-- Norm bound for `y⁴ - z⁴ - y4_5` where `y4_5 = z³T₂ + z²T₂z + zT₂z² + T₂z³`,
given the BCH-context norm bounds. The bound is `31·s⁶`. -/
private theorem norm_y4_sub_z4_sub_y4_5_le (y P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3)‖ ≤ 31 * s ^ 6 := by
  rw [y4_sub_z4_sub_y4_5_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- 7 terms to bound
  -- (y-P)^3 (P-T₂) etc.: ≤ s^3 * 5s^3 = 5s^6, four of these = 20s^6
  have h_z3PT : ‖z ^ 3 * (P - T₂)‖ ≤ s ^ 3 * (5 * s ^ 3) :=
    calc ‖z ^ 3 * (P - T₂)‖ ≤ ‖z ^ 3‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 3 * ‖P - T₂‖ := by gcongr; exact norm_pow_le z 3
      _ ≤ s ^ 3 * (5 * s ^ 3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
          hPmT₂ (norm_nonneg _) (by positivity)
  have h_z2PTz : ‖z ^ 2 * (P - T₂) * z‖ ≤ s ^ 2 * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z ^ 2 * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ (s ^ 2 * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂
            (norm_nonneg _) (by positivity)
  have h_zPTz2 : ‖z * (P - T₂) * z ^ 2‖ ≤ s * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖z * (P - T₂)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (s * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  have h_PTz3 : ‖(P - T₂) * z ^ 3‖ ≤ (5 * s ^ 3) * s ^ 3 :=
    calc _ ≤ ‖P - T₂‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ * ‖z‖ ^ 3 := by gcongr; exact norm_pow_le z 3
      _ ≤ (5 * s ^ 3) * s ^ 3 := mul_le_mul hPmT₂
          (pow_le_pow_left₀ (norm_nonneg _) hzn 3) (by positivity) (by positivity)
  -- (y³ - z³) P term
  have hy3z3 := norm_pow3_sub_zpow3_le y P hs_nn hy hz hP
  have h_y3z3P : ‖(y ^ 3 - z ^ 3) * P‖ ≤ (7 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖y ^ 3 - z ^ 3‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (7 * s ^ 4) * s ^ 2 :=
          mul_le_mul hy3z3 hP (norm_nonneg _) (by positivity)
  -- (y² - z²) P z term
  have hy2z2 := norm_pow2_sub_zpow2_le y P hs_nn hy hz hP
  have h_y2z2Pz : ‖(y ^ 2 - z ^ 2) * P * z‖ ≤ (3 * s ^ 3) * s ^ 2 * s :=
    calc _ ≤ ‖(y ^ 2 - z ^ 2) * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 2 - z ^ 2‖ * ‖P‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((3 * s ^ 3) * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy2z2 hP (norm_nonneg _) (by positivity)
  -- P · P · z² term (note: P*P*z² in the decomp formula)
  have h_PPz2 : ‖P * P * z ^ 2‖ ≤ s ^ 2 * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖P * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖P‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (s ^ 2 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hP hP (norm_nonneg _) (by positivity)
  -- Sum via triangle inequality (7 terms)
  have ht := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2 + (P - T₂) * z ^ 3 +
      (y ^ 3 - z ^ 3) * P + (y ^ 2 - z ^ 2) * P * z) (P * P * z ^ 2)
  have ht2 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2 + (P - T₂) * z ^ 3 +
      (y ^ 3 - z ^ 3) * P) ((y ^ 2 - z ^ 2) * P * z)
  have ht3 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2 + (P - T₂) * z ^ 3)
    ((y ^ 3 - z ^ 3) * P)
  have ht4 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2)
    ((P - T₂) * z ^ 3)
  have ht5 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z) (z * (P - T₂) * z ^ 2)
  have ht6 := norm_add_le (z ^ 3 * (P - T₂)) (z ^ 2 * (P - T₂) * z)
  nlinarith [pow_nonneg hs_nn 6]

/-- **I₂ residual decomposition**: pure ring identity in `(z, P, T₂, T₃)` for
`(z+P)³ - z³ - (z²T₂+zT₂z+T₂z²) - (z²T₃+zT₃z+T₃z²+zT₂²+T₂zT₂+T₂²z)`,
which when multiplied by `(3:𝕂)⁻¹` becomes `I₂ - corr₂ - corr₂_5`.

Each summand on the RHS has deg-6+ structure (since `P-T₂-T₃` has deg-4+,
`P²-T₂²` has deg-5+, `PzP-T₂zT₂` has deg-6+, `P³` has deg-6). -/
private theorem I2_residual_decomp_eq (z P T₂ T₃ : 𝔸) :
    (z + P) ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
      (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) =
    z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z + (P - T₂ - T₃) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) +
    (P ^ 2 - T₂ ^ 2) * z + P ^ 3 := by
  noncomm_ring

set_option maxHeartbeats 4000000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **I₁ residual decomposition** (pure algebraic identity in (ea, eb, a, b)):
expresses `(I₁ in quartic_id form) - corr₁ - corr₁_5` as a sum of 7 deg-6+ terms.

Proof: ×720 scalar clearing + dsimp (unfold let-bindings) + simp distribution
+ noncomm_ring. Mirrors the pattern of `quartic_identity` and
`sextic_pure_identity`. -/
private theorem I1_residual_decomp_eq (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
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
    let P : 𝔸 := ea * eb - 1 - (a + b)
    let z : 𝔸 := a + b
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂)
    let R : 𝔸 := T₃ - E₁ - E₂ - Q + T₄
    -- LHS: I₁ (quartic_identity form) - corr₁ - corr₁_5
    (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
        (2 : 𝕂)⁻¹ • P ^ 2) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
      (2 : 𝕂)⁻¹ • W5 =
    -- RHS: 7 deg-6+ terms
    H₁ + H₂ + a * G₂ + G₁ * b +
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
    (2 : 𝕂)⁻¹ • (z * R + R * z) +
    (2 : 𝕂)⁻¹ • (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) := by
  -- KEY: dsimp only unfolds the let-bindings (transparent reduction)
  dsimp only
  rw [← sub_eq_zero]
  -- Multiply by 720 to clear denominators (LCM)
  have h720ne : (720 : 𝕂) ≠ 0 := by exact_mod_cast (show (720 : ℕ) ≠ 0 by norm_num)
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  have hinj : Function.Injective ((720 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x₀ y₀ hxy; have := congrArg ((720 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h720ne, one_smul] at this; exact this
  apply hinj; simp only [smul_zero]
  simp only [pow_succ, pow_zero, one_mul]
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  simp only [mul_assoc, mul_inv_cancel₀ h2ne, inv_mul_cancel₀ h2ne,
    show (720 : 𝕂) * (2 : 𝕂)⁻¹ = 360 from by norm_num,
    show (720 : 𝕂) * (3 : 𝕂)⁻¹ = 240 from by norm_num,
    show (720 : 𝕂) * (4 : 𝕂)⁻¹ = 180 from by norm_num,
    show (720 : 𝕂) * (6 : 𝕂)⁻¹ = 120 from by norm_num,
    show (720 : 𝕂) * (12 : 𝕂)⁻¹ = 60 from by norm_num,
    show (720 : 𝕂) * (24 : 𝕂)⁻¹ = 30 from by norm_num,
    show (720 : 𝕂) * (60 : 𝕂)⁻¹ = 12 from by norm_num,
    show (720 : 𝕂) * (120 : 𝕂)⁻¹ = 6 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 180 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (24 : 𝕂)⁻¹) = 15 from by norm_num,
    show (720 : 𝕂) * ((24 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 15 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (4 : 𝕂)⁻¹) = 90 from by norm_num,
    show (720 : 𝕂) * ((4 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 90 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹) = 30 from by norm_num,
    show (720 : 𝕂) * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 30 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (60 : 𝕂)⁻¹) = 6 from by norm_num,
    show (720 : 𝕂) * ((60 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 6 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (120 : 𝕂)⁻¹) = 3 from by norm_num,
    show (720 : 𝕂) * ((120 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 3 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 20 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 90 from by norm_num,
    one_smul, mul_one]
  simp only [ofNat_smul_eq_nsmul (R := 𝕂)]
  noncomm_ring

set_option maxHeartbeats 800000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **R algebraic identity** for the I₁ residual bound.
Expresses `R = T₃ - E₁ - E₂ - Q + T₄` (the deg-5+ part of `-(E_i+Q) + T₃ + T₄`)
as `R = -(G₁ + G₂ + a·F₂ + F₁·b + E₁·E₂ + ½·E₁·b² + ½·a²·E₂)`. -/
private theorem R_eq_neg_deg5_residual (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    T₃ - E₁ - E₂ - Q + T₄ =
    -(G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂)) := by
  dsimp only
  rw [← sub_eq_zero]
  have h24ne : (24 : 𝕂) ≠ 0 := by exact_mod_cast (show (24 : ℕ) ≠ 0 by norm_num)
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  have hinj : Function.Injective ((24 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x₀ y₀ hxy; have := congrArg ((24 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h24ne, one_smul] at this; exact this
  apply hinj; simp only [smul_zero]
  simp only [pow_succ, pow_zero, one_mul]
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  simp only [mul_assoc, mul_inv_cancel₀ h2ne, inv_mul_cancel₀ h2ne,
    show (24 : 𝕂) * (2 : 𝕂)⁻¹ = 12 from by norm_num,
    show (24 : 𝕂) * (3 : 𝕂)⁻¹ = 8 from by norm_num,
    show (24 : 𝕂) * (4 : 𝕂)⁻¹ = 6 from by norm_num,
    show (24 : 𝕂) * (6 : 𝕂)⁻¹ = 4 from by norm_num,
    show (24 : 𝕂) * (24 : 𝕂)⁻¹ = 1 from mul_inv_cancel₀ h24ne,
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 6 from by norm_num,
    show (24 : 𝕂) * ((2 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 2 from by norm_num,
    show (24 : 𝕂) * ((6 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 2 from by norm_num,
    one_smul, mul_one]
  simp only [ofNat_smul_eq_nsmul (R := 𝕂)]
  noncomm_ring

/-- Norm bound `‖I₁ residual (RHS form)‖ ≤ 20·s⁶` from precomputed component bounds.
This is the I₁ residual bound from precomputed individual norm bounds.
Combined with I1_residual_decomp_eq (commit 2fccfa8), gives
`‖I₁ - corr₁ - corr₁_5‖ ≤ 20·s⁶` where `s ≤ 1/10`.

The decomp RHS: H₁+H₂+a·G₂+G₁·b+(E₁E₂+½a²F₂+½F₁b²)+½(z·R+R·z)+½(T₂²-P²+T₂T₃+T₃T₂).
Per-term: 1+1+1+1+1+½+½+6+7.5 = 19.5 ≤ 20. -/
private theorem norm_I1_residual_RHS_le (a b z H₁ H₂ G₁ G₂ F₁ F₂ E₁ E₂ R T22 : 𝔸)
    {s : ℝ} (hs_nn : 0 ≤ s)
    (hH₁_le : ‖H₁‖ ≤ s ^ 6) (hH₂_le : ‖H₂‖ ≤ s ^ 6)
    (h_aG₂_le : ‖a * G₂‖ ≤ s ^ 6) (h_G₁b_le : ‖G₁ * b‖ ≤ s ^ 6)
    (h_E₁E₂_le : ‖E₁ * E₂‖ ≤ s ^ 6)
    (h_a2F₂_le : ‖a ^ 2 * F₂‖ ≤ s ^ 6) (h_F₁b2_le : ‖F₁ * b ^ 2‖ ≤ s ^ 6)
    (h_zRpRz_le : ‖z * R + R * z‖ ≤ 12 * s ^ 6)
    (h_T22_le : ‖T22‖ ≤ 15 * s ^ 6) :
    ‖H₁ + H₂ + a * G₂ + G₁ * b +
      (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
      (2 : 𝕂)⁻¹ • (z * R + R * z) +
      (2 : 𝕂)⁻¹ • T22‖ ≤ 20 * s ^ 6 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_a2F2_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * F₂)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * F₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2F₂_le (by norm_num)
      _ = s ^ 6 / 2 := by ring
  have h_F1b2_smul : ‖(2 : 𝕂)⁻¹ • (F₁ * b ^ 2)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖F₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_F₁b2_le (by norm_num)
      _ = s ^ 6 / 2 := by ring
  have h_zRpRz_smul : ‖(2 : 𝕂)⁻¹ • (z * R + R * z)‖ ≤ 6 * s ^ 6 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖z * R + R * z‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (12 * s ^ 6) := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_zRpRz_le (by norm_num)
      _ = 6 * s ^ 6 := by ring
  have h_T22_smul : ‖(2 : 𝕂)⁻¹ • T22‖ ≤ 15 * s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖T22‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (15 * s ^ 6) := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_T22_le (by norm_num)
      _ = 15 * s ^ 6 / 2 := by ring
  -- Triangle inequality on the 9-term sum
  -- Outer: (H₁+H₂+a*G₂+G₁*b) + inner_3 + ½(zR+Rz) + ½T22
  -- Inner_3 = E₁*E₂ + ½(a²*F₂) + ½(F₁*b²)
  have h_inner3 : ‖E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) +
      (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)‖ ≤ s ^ 6 + s ^ 6 / 2 + s ^ 6 / 2 := by
    have hi1 := norm_add_le (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂))
      ((2 : 𝕂)⁻¹ • (F₁ * b ^ 2))
    have hi2 := norm_add_le (E₁ * E₂) ((2 : 𝕂)⁻¹ • (a ^ 2 * F₂))
    linarith
  -- Outer chain: 4 + inner + 2 = 7 norm_add_le applications
  have ha1 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b +
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
    (2 : 𝕂)⁻¹ • (z * R + R * z)) ((2 : 𝕂)⁻¹ • T22)
  have ha2 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b +
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)))
    ((2 : 𝕂)⁻¹ • (z * R + R * z))
  have ha3 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b)
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2))
  have ha4 := norm_add_le (H₁ + H₂ + a * G₂) (G₁ * b)
  have ha5 := norm_add_le (H₁ + H₂) (a * G₂)
  have ha6 := norm_add_le H₁ H₂
  -- Sum: 1+1+1+1 + (1+½+½) + 6 + 7.5 = 19.5 ≤ 20
  linarith [pow_nonneg hs_nn 6]

/-- Norm bound `‖T₂² - P² + T₂T₃ + T₃T₂‖ ≤ 15·s⁶`. Decomposition uses
`P² - T₂² - T₂T₃ - T₃T₂ = (P-T₂-T₃)·P + T₂·(P-T₂-T₃) + T₃·(P-T₂)`. -/
private theorem norm_T22_sub_P2_etc_le (P T₂ T₃ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂‖ ≤ 15 * s ^ 6 := by
  have heq : T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂ =
      -((P - T₂ - T₃) * P + T₂ * (P - T₂ - T₃) + T₃ * (P - T₂)) := by noncomm_ring
  rw [heq, norm_neg]
  have h1 : ‖(P - T₂ - T₃) * P‖ ≤ (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (5 * s ^ 4) * s ^ 2 := mul_le_mul hPmT₂mT₃ hP (norm_nonneg _) (by positivity)
  have h2 : ‖T₂ * (P - T₂ - T₃)‖ ≤ s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖T₂‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ s ^ 2 * (5 * s ^ 4) := mul_le_mul hT₂ hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have h3 : ‖T₃ * (P - T₂)‖ ≤ s ^ 3 * (5 * s ^ 3) :=
    calc _ ≤ ‖T₃‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ s ^ 3 * (5 * s ^ 3) := mul_le_mul hT₃ hPmT₂ (norm_nonneg _) (by positivity)
  have ha1 := norm_add_le ((P - T₂ - T₃) * P + T₂ * (P - T₂ - T₃)) (T₃ * (P - T₂))
  have ha2 := norm_add_le ((P - T₂ - T₃) * P) (T₂ * (P - T₂ - T₃))
  linarith [pow_nonneg hs_nn 6]

/-- Norm bound `‖R-residual sum‖ ≤ 6·s⁵` from precomputed component bounds.
The 7 terms come from R_eq_neg_deg5_residual: G₁+G₂+a·F₂+F₁·b+E₁·E₂+½E₁b²+½a²E₂. -/
private theorem norm_R_residual_sum_le (G₁ G₂ F₁ F₂ E₁ E₂ a b : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hG₁_le : ‖G₁‖ ≤ s ^ 5) (hG₂_le : ‖G₂‖ ≤ s ^ 5)
    (h_aF₂_le : ‖a * F₂‖ ≤ s ^ 5) (h_F₁b_le : ‖F₁ * b‖ ≤ s ^ 5)
    (h_E₁E₂_le : ‖E₁ * E₂‖ ≤ s ^ 6)
    (h_E₁b2_le : ‖E₁ * b ^ 2‖ ≤ s ^ 5)
    (h_a2E₂_le : ‖a ^ 2 * E₂‖ ≤ s ^ 5) :
    ‖G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂)‖ ≤ 6 * s ^ 5 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_smul1 : ‖(2 : 𝕂)⁻¹ • (E₁ * b ^ 2)‖ ≤ s ^ 5 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖E₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 5 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_E₁b2_le (by norm_num)
      _ = s ^ 5 / 2 := by ring
  have h_smul2 : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * E₂)‖ ≤ s ^ 5 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * E₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 5 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2E₂_le (by norm_num)
      _ = s ^ 5 / 2 := by ring
  have hs6 : s ^ 6 ≤ s ^ 5 / 10 := by
    have h_eq : s ^ 6 = s ^ 5 * s := by ring
    rw [h_eq]
    have : s ^ 5 * s ≤ s ^ 5 * (1 / 10) := by
      apply mul_le_mul_of_nonneg_left hs_small (pow_nonneg hs_nn 5)
    linarith
  have ha1 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
    (2 : 𝕂)⁻¹ • (E₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * E₂))
  have ha2 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂)
    ((2 : 𝕂)⁻¹ • (E₁ * b ^ 2))
  have ha3 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b) (E₁ * E₂)
  have ha4 := norm_add_le (G₁ + G₂ + a * F₂) (F₁ * b)
  have ha5 := norm_add_le (G₁ + G₂) (a * F₂)
  have ha6 := norm_add_le G₁ G₂
  linarith [pow_nonneg hs_nn 5, pow_nonneg hs_nn 6]

/-- Norm bound for `‖PzP - T₂zT₂‖ ≤ 13·s⁶` for small s (`s < 1/10`).
Splits via `P = T₂ + (P-T₂)` into 3 terms each bounded by Cs⁶. -/
private theorem norm_PzP_sub_T2zT2_le (z P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_small : s ≤ 1 / 10) (hz : ‖z‖ ≤ s) (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖P * z * P - T₂ * z * T₂‖ ≤ 13 * s ^ 6 := by
  have heq : P * z * P - T₂ * z * T₂ =
      T₂ * z * (P - T₂) + (P - T₂) * z * T₂ + (P - T₂) * z * (P - T₂) := by
    have hP : P = T₂ + (P - T₂) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  have ht1 : ‖T₂ * z * (P - T₂)‖ ≤ s ^ 2 * s * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hz (norm_nonneg _) (by positivity)
  have ht2 : ‖(P - T₂) * z * T₂‖ ≤ (5 * s ^ 3) * s * s ^ 2 :=
    calc _ ≤ ‖(P - T₂) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ hz (norm_nonneg _) (by positivity)
  have ht3 : ‖(P - T₂) * z * (P - T₂)‖ ≤ (5 * s ^ 3) * s * (5 * s ^ 3) :=
    calc _ ≤ ‖(P - T₂) * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ hz (norm_nonneg _) (by positivity)
  have hadd1 := norm_add_le (T₂ * z * (P - T₂) + (P - T₂) * z * T₂)
    ((P - T₂) * z * (P - T₂))
  have hadd2 := norm_add_le (T₂ * z * (P - T₂)) ((P - T₂) * z * T₂)
  -- Total: 5s⁶ + 5s⁶ + 25s⁷ ≤ 5 + 5 + 25·(1/10)·s⁶ = 12.5s⁶ ≤ 13s⁶
  nlinarith [pow_nonneg hs_nn 6, pow_nonneg hs_nn 7]

/-- Norm bound for `‖P² - T₂²‖ ≤ 10·s⁵` via `P² - T₂² = (P-T₂)P + T₂(P-T₂)`. -/
private theorem norm_P2_sub_T22_le (P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖P ^ 2 - T₂ ^ 2‖ ≤ 10 * s ^ 5 := by
  have heq : P ^ 2 - T₂ ^ 2 = (P - T₂) * P + T₂ * (P - T₂) := by noncomm_ring
  rw [heq]
  have ht1 : ‖(P - T₂) * P‖ ≤ (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖P - T₂‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (5 * s ^ 3) * s ^ 2 := mul_le_mul hPmT₂ hP (norm_nonneg _) (by positivity)
  have ht2 : ‖T₂ * (P - T₂)‖ ≤ s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ s ^ 2 * (5 * s ^ 3) := mul_le_mul hT₂ hPmT₂ (norm_nonneg _) (by positivity)
  have hadd := norm_add_le ((P - T₂) * P) (T₂ * (P - T₂))
  nlinarith [pow_nonneg hs_nn 5]

/-- Norm bound for `I₂ residual` (post `(3:𝕂)⁻¹` scalar factor):
inner sum ≤ 50·s⁶ for `s < 1/10`. -/
private theorem norm_I2_residual_inner_le (z P T₂ T₃ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_small : s ≤ 1 / 10)
    (hz : ‖z‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z + (P - T₂ - T₃) * z ^ 2 +
     z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) +
     (P ^ 2 - T₂ ^ 2) * z + P ^ 3‖ ≤ 50 * s ^ 6 := by
  -- Helper bounds
  have hP2T22 := norm_P2_sub_T22_le P T₂ hs_nn hP hT₂ hPmT₂
  have hPzP := norm_PzP_sub_T2zT2_le z P T₂ hs_nn hs_small hz hT₂ hPmT₂
  -- Term 1: z² · (P-T₂-T₃) ≤ s²·5s⁴ = 5s⁶
  have h1 : ‖z ^ 2 * (P - T₂ - T₃)‖ ≤ s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P - T₂ - T₃‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (5 * s ^ 4) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz 2)
          hPmT₂mT₃ (norm_nonneg _) (by positivity)
  -- Term 2: z · (P-T₂-T₃) · z ≤ s·5s⁴·s = 5s⁶
  have h2 : ‖z * (P - T₂ - T₃) * z‖ ≤ s * (5 * s ^ 4) * s :=
    calc _ ≤ ‖z * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (5 * s ^ 4)) * s := by
          apply mul_le_mul _ hz (norm_nonneg _) (by positivity)
          exact mul_le_mul hz hPmT₂mT₃ (norm_nonneg _) (by positivity)
  -- Term 3: (P-T₂-T₃) · z² ≤ 5s⁴·s² = 5s⁶
  have h3 : ‖(P - T₂ - T₃) * z ^ 2‖ ≤ (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (5 * s ^ 4) * s ^ 2 := mul_le_mul hPmT₂mT₃
          (pow_le_pow_left₀ (norm_nonneg _) hz 2) (by positivity) (by positivity)
  -- Term 4: z · (P²-T₂²) ≤ s·10s⁵ = 10s⁶
  have h4 : ‖z * (P ^ 2 - T₂ ^ 2)‖ ≤ s * (10 * s ^ 5) :=
    calc _ ≤ ‖z‖ * ‖P ^ 2 - T₂ ^ 2‖ := norm_mul_le _ _
      _ ≤ s * (10 * s ^ 5) := mul_le_mul hz hP2T22 (norm_nonneg _) hs_nn
  -- Term 5: PzP - T₂zT₂ ≤ 13s⁶
  -- (already have hPzP)
  -- Term 6: (P²-T₂²) · z ≤ 10s⁵·s = 10s⁶
  have h6 : ‖(P ^ 2 - T₂ ^ 2) * z‖ ≤ (10 * s ^ 5) * s :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (10 * s ^ 5) * s := mul_le_mul hP2T22 hz (norm_nonneg _) (by positivity)
  -- Term 7: P³ ≤ s⁶
  have h7 : ‖P ^ 3‖ ≤ (s ^ 2) ^ 3 :=
    calc _ ≤ ‖P‖ ^ 3 := norm_pow_le P 3
      _ ≤ (s ^ 2) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hP 3
  -- Sum 7 terms via norm_add_le chain
  have ha1 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) +
    (P ^ 2 - T₂ ^ 2) * z) (P ^ 3)
  have ha2 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂))
    ((P ^ 2 - T₂ ^ 2) * z)
  have ha3 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + z * (P ^ 2 - T₂ ^ 2)) (P * z * P - T₂ * z * T₂)
  have ha4 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2) (z * (P ^ 2 - T₂ ^ 2))
  have ha5 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z)
    ((P - T₂ - T₃) * z ^ 2)
  have ha6 := norm_add_le (z ^ 2 * (P - T₂ - T₃)) (z * (P - T₂ - T₃) * z)
  -- Sum: 5+5+5+10+13+10+1 = 49 ≤ 50
  nlinarith [pow_nonneg hs_nn 6]

set_option maxHeartbeats 1024000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Algebraic decomposition of `pieceB''` for the sextic remainder small-s case.**

States that pieceB'' (the algebraic part of the sextic remainder, with H1
NOT applied — keeping the `y - z - ½[a,b] - ½y²` form) decomposes as:

```
pieceB'' = (I₁ - corr₁ - corr₁_5) + (I₂ - corr₂ - corr₂_5)
           - ¼(y⁴ - z⁴ - y4_5) + ⅕(y⁵ - z⁵)
```

where:
- `I₁ = y - z - ½[a,b] - ½y² + ⅓z³ - C₃` (== ½W + ⅓z³ - C₃ via H1)
- `I₂ = ⅓(y³ - z³)`
- `corr₁`, `corr₂` from `quintic_pure_identity` (deg-4 corrections)
- `corr₁_5 = ½·W5`, `corr₂_5 = ⅓·y3_5` from `sextic_pure_identity` (deg-5)

Proof: `pieceB'' - RHS = (LHS_QPI) + (LHS_SPI) = 0 + 0 = 0` via QPI + SPI. -/
private theorem pieceB_sextic_decomp (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃_QPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)
    let T₃_SPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃_SPI + T₃_SPI * T₂)
    let y3_5 : 𝔸 := z ^ 2 * T₃_SPI + z * T₃_SPI * z + T₃_SPI * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z
    let y4_5 : 𝔸 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3
    let y : 𝔸 := exp a * exp b - 1
    let corr₁ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃_QPI + T₃_QPI * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2
    let corr₂ : 𝔸 := (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)
    let corr₁_5 : 𝔸 := (2 : 𝕂)⁻¹ • W5
    let corr₂_5 : 𝔸 := (3 : 𝕂)⁻¹ • y3_5
    -- pieceB''
    y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
      (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b =
    -- RHS
    ((y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
        (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b) - corr₁ - corr₁_5) +
    ((3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) - corr₂ - corr₂_5) -
    (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4 - y4_5) +
    (5 : 𝕂)⁻¹ • (y ^ 5 - z ^ 5) := by
  intro z T₂ T₃_QPI T₃_SPI T₄ W5 y3_5 y4_5 y corr₁ corr₂ corr₁_5 corr₂_5
  -- Use QPI + SPI
  have hQPI := quintic_pure_identity 𝕂 a b
  have hSPI := sextic_pure_identity 𝕂 a b
  -- Try linear_combination with module as norm
  linear_combination (norm := module) hQPI + hSPI

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
private theorem symmetric_bch_cubic_poly_alt_form (a b : 𝔸) :
    symmetric_bch_cubic_poly 𝕂 a b =
      bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
      bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) -
      (16 : 𝕂)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a) := by
  have h48ne : (48 : 𝕂) ≠ 0 := by exact_mod_cast (show (48 : ℕ) ≠ 0 by norm_num)
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  have hinj : Function.Injective ((48 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x y hxy
    have := congrArg ((48 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h48ne, one_smul] at this; exact this
  apply hinj
  unfold symmetric_bch_cubic_poly bch_cubic_term
  -- Distribute scalars (matching pattern of symmetric_bch_quartic_identity)
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  -- Clear scalar products
  simp only [mul_assoc,
    inv_mul_cancel₀ h2ne, mul_inv_cancel₀ h48ne,
    show (48 : 𝕂) * (12 : 𝕂)⁻¹ = 4 from by norm_num,
    show (48 : 𝕂) * (16 : 𝕂)⁻¹ = 3 from by norm_num,
    show (48 : 𝕂) * (24 : 𝕂)⁻¹ = 2 from by norm_num,
    -- Two-level
    show (48 : 𝕂) * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹) = 2 from by norm_num,
    show (48 : 𝕂) * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 2 from by norm_num,
    -- Three-level (a'·a'·... patterns from C₃(½a, b))
    show (48 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹)) = 1 from by norm_num,
    show (48 : 𝕂) * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 1 from by norm_num,
    show (48 : 𝕂) * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 1 from by norm_num,
    one_smul, mul_one]
  -- Convert ofNat 𝕂-smul to ℕ-smul so subsequent simp/noncomm_ring see uniform form
  simp only [ofNat_smul_eq_nsmul (R := 𝕂)]
  -- Pure ring identity (with nested nsmul/zsmul), provable by noncomm_ring.
  noncomm_ring

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
private theorem symmetric_bch_quartic_identity (a b : 𝔸) :
    (2 : 𝕂)⁻¹ • (bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b * ((2 : 𝕂)⁻¹ • a) -
                  ((2 : 𝕂)⁻¹ • a) * bch_cubic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b) +
      bch_quartic_term 𝕂 ((2 : 𝕂)⁻¹ • a) b +
      -((96 : 𝕂)⁻¹ • (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
                       (a * (a * b - b * a) - (a * b - b * a) * a) * b)) +
      bch_quartic_term 𝕂 ((2 : 𝕂)⁻¹ • a + b) ((2 : 𝕂)⁻¹ • a) = 0 := by
  -- Multiply through by 96 and verify by noncomm_ring after scalar clearing.
  have h192ne : (192 : 𝕂) ≠ 0 := by exact_mod_cast (show (192 : ℕ) ≠ 0 by norm_num)
  have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
  have hinj : Function.Injective ((192 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x y hxy
    have := congrArg ((192 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h192ne, one_smul] at this; exact this
  apply hinj; simp only [smul_zero]
  unfold bch_cubic_term bch_quartic_term
  -- Distribute scalars through the algebraic expression
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  -- Clear scalar products (192 * various c⁻¹ combinations)
  simp only [mul_assoc,
    inv_mul_cancel₀ h2ne, mul_inv_cancel₀ h192ne,
    show (192 : 𝕂) * (2 : 𝕂)⁻¹ = 96 from by norm_num,
    show (192 : 𝕂) * (12 : 𝕂)⁻¹ = 16 from by norm_num,
    show (192 : 𝕂) * (24 : 𝕂)⁻¹ = 8 from by norm_num,
    show (192 : 𝕂) * (96 : 𝕂)⁻¹ = 2 from by norm_num,
    -- Two-level
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 48 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹) = 8 from by norm_num,
    show (192 : 𝕂) * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 8 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * (24 : 𝕂)⁻¹) = 4 from by norm_num,
    show (192 : 𝕂) * ((24 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 4 from by norm_num,
    -- Three-level
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹)) = 4 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 4 from by norm_num,
    show (192 : 𝕂) * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 4 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (24 : 𝕂)⁻¹)) = 2 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((24 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 2 from by norm_num,
    show (192 : 𝕂) * ((24 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 2 from by norm_num,
    -- Four-level (for C₄(a',b) and C₄(a'+b,a') nested scaling)
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (24 : 𝕂)⁻¹))) = 1 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 2 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 2 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹))) = 2 from by norm_num,
    show (192 : 𝕂) * ((24 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 1 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((24 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 1 from by norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((24 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 1 from by norm_num,
    -- Five-level (four 2⁻¹ and one 12⁻¹ → product = 1/192)
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by
      norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by
      norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by
      norm_num,
    show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹)))) = 1 from by
      norm_num,
    show (192 : 𝕂) * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by
      norm_num,
    one_smul, mul_one]
  -- After clearing, the goal is a pure ring identity provable by noncomm_ring.
  noncomm_ring

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
    have h12ne : (12 : 𝕂) ≠ 0 := by exact_mod_cast (show (12:ℕ) ≠ 0 by norm_num)
    have hinj : Function.Injective ((12 : 𝕂) • · : 𝔸 → 𝔸) := by
      intro x y hxy
      have := congrArg ((12 : 𝕂)⁻¹ • ·) hxy
      simp only [smul_smul, inv_mul_cancel₀ h12ne, one_smul] at this; exact this
    apply hinj
    simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h12ne, one_smul]
    noncomm_ring
  -- Identity 3: L_W = L_Wrest + L_W2 (linearity in ξ)
  have hId3 : L_W = L_Wrest + L_W2 := by
    rw [hL_W_def, hL_Wrest_def, hL_W2_def, hWrest_def]
    noncomm_ring
  -- Identity 2 (cancellation): (12)⁻¹•L_W2 + (96)⁻¹•(b·DC_a - DC_a·b) = 0
  have hId2 : (12 : 𝕂)⁻¹ • L_W2 + (96 : 𝕂)⁻¹ • (b * DC_a - DC_a * b) = 0 := by
    rw [hL_W2_def, hW₂_def, hDC_a_def, ha'_def]
    have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
    have h192ne : (192 : 𝕂) ≠ 0 := by exact_mod_cast (show (192:ℕ) ≠ 0 by norm_num)
    have hinj : Function.Injective ((192 : 𝕂) • · : 𝔸 → 𝔸) := by
      intro x y hxy
      have := congrArg ((192 : 𝕂)⁻¹ • ·) hxy
      simp only [smul_smul, inv_mul_cancel₀ h192ne, one_smul] at this; exact this
    apply hinj
    simp only [smul_zero, smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
      smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul]
    simp only [mul_assoc, inv_mul_cancel₀ h2ne, mul_inv_cancel₀ h192ne,
      show (192 : 𝕂) * (2 : 𝕂)⁻¹ = 96 from by norm_num,
      show (192 : 𝕂) * (12 : 𝕂)⁻¹ = 16 from by norm_num,
      show (192 : 𝕂) * (96 : 𝕂)⁻¹ = 2 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 48 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹) = 8 from by norm_num,
      show (192 : 𝕂) * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 8 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹)) = 4 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 4 from by norm_num,
      show (192 : 𝕂) * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 4 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹))) = 2 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 2 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 2 from by norm_num,
      show (192 : 𝕂) * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹))) = 2 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹)))) = 1 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by norm_num,
      show (192 : 𝕂) * ((2 : 𝕂)⁻¹ * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by norm_num,
      show (192 : 𝕂) * ((12 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)))) = 1 from by norm_num,
      one_smul, mul_one]
    noncomm_ring
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
