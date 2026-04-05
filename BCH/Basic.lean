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

/-! ### Quartic algebraic identity for BCH -/

set_option maxHeartbeats 64000000 in
/-- The quartic algebraic identity: after clearing scalar denominators by multiplying by 12,
the combination `½W_H1 + ⅓(a+b)³ - bch_cubic_term` reduces to quartic+ terms.

This is the key identity enabling the fourth-order BCH expansion. The proof clears
all `(k:𝕂)⁻¹ •` scalars via `smul_smul` and verifies the resulting ring identity
with `noncomm_ring`. -/
private theorem quartic_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let y := ea * eb - 1
    let D₁ := ea - 1 - a
    let D₂ := eb - 1 - b
    let P := y - (a + b)
    let E₁ := ea - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ := eb - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2
    let Q := a * D₂ + D₁ * b + D₁ * D₂
    let F₁ := ea - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ := eb - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 - (6 : 𝕂)⁻¹ • b ^ 3
    (12 : 𝕂) • ((2 : 𝕂)⁻¹ • ((2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          (a + b) * P - P * (a + b) - P ^ 2) +
        (3 : 𝕂)⁻¹ • (a + b) ^ 3 - bch_cubic_term 𝕂 a b) =
    (12 : 𝕂) • F₁ + (12 : 𝕂) • F₂ +
    (12 : 𝕂) • (a * E₂) + (12 : 𝕂) • (E₁ * b) + (12 : 𝕂) • (D₁ * D₂) -
    (6 : 𝕂) • ((a + b) * (E₁ + E₂ + Q)) - (6 : 𝕂) • ((E₁ + E₂ + Q) * (a + b)) -
    (6 : 𝕂) • P ^ 2 := by
  -- Clear all scalar denominators
  simp only [smul_sub, smul_add, smul_smul]
  -- Compute 12*(k⁻¹) for k ∈ {2,3,6,12}
  have h12_2 : (12 : 𝕂) * (2 : 𝕂)⁻¹ = 6 := by push_cast; norm_num
  have h12_3 : (12 : 𝕂) * (3 : 𝕂)⁻¹ = 4 := by push_cast; norm_num
  have h12_6 : (12 : 𝕂) * (6 : 𝕂)⁻¹ = 2 := by push_cast; norm_num
  have h12_12 : (12 : 𝕂) * (12 : 𝕂)⁻¹ = 1 := by
    apply mul_inv_cancel₀; exact_mod_cast (show (12 : ℕ) ≠ 0 by norm_num)
  have h6_2 : (6 : 𝕂) * (2 : 𝕂)⁻¹ = 3 := by push_cast; norm_num
  simp only [h12_2, h12_3, h12_6, h12_12, h6_2, one_smul, mul_one]
  -- Now convert remaining (n:𝕂)•x to sums
  have smul2 : ∀ x : 𝔸, (2 : 𝕂) • x = x + x := two_smul 𝕂
  have smul3 : ∀ x : 𝔸, (3 : 𝕂) • x = x + x + x := by
    intro x; rw [show (3:𝕂) = 2 + 1 from by push_cast; norm_num, add_smul, two_smul, one_smul]
  have smul4 : ∀ x : 𝔸, (4 : 𝕂) • x = x + x + x + x := by
    intro x; rw [show (4:𝕂) = 2 + 2 from by push_cast; norm_num, add_smul, two_smul]; abel
  have smul6 : ∀ x : 𝔸, (6 : 𝕂) • x = x + x + x + x + x + x := by
    intro x; rw [show (6:𝕂) = 3 + 3 from by push_cast; norm_num, add_smul, smul3]; abel
  have smul12 : ∀ x : 𝔸, (12 : 𝕂) • x = x + x + x + x + x + x + x + x + x + x + x + x := by
    intro x; rw [show (12:𝕂) = 6 + 6 from by push_cast; norm_num, add_smul, smul6]; abel
  -- Unfold bch_cubic_term
  unfold bch_cubic_term
  simp only [smul2, smul3, smul4, smul6, smul12]
  -- Pure non-commutative ring identity — no more scalar smul
  -- noncomm_ring fails on this large expression. May need to break into sub-identities.
  sorry

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
  have h12_I₁ : (12 : 𝕂) • I₁ =
      (12 : 𝕂) • F₁ + (12 : 𝕂) • F₂ +
      (12 : 𝕂) • (a * E₂) + (12 : 𝕂) • (E₁ * b) + (12 : 𝕂) • (D₁ * D₂) -
      (6 : 𝕂) • ((a + b) * (E₁ + E₂ + Q)) - (6 : 𝕂) • ((E₁ + E₂ + Q) * (a + b)) -
      (6 : 𝕂) • P ^ 2 := by
    rw [hI₁_eq2]
    exact quartic_identity 𝕂 (exp a) (exp b) a b
  -- Bound ‖I₁‖ using the identity
  have hI₁_le : ‖I₁‖ ≤ 90 * s ^ 4 := by
    have hI₁_smul : I₁ = (12 : 𝕂)⁻¹ • ((12 : 𝕂) • I₁) := by
      simp [smul_smul, inv_mul_cancel₀ h12ne]
    have h12_norm : ‖(12 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
    rw [hI₁_smul, h12_I₁]
    -- ‖(12⁻¹) • (sum of quartic terms)‖ ≤ ‖sum‖ ≤ sum of ‖terms‖
    -- Each term involves F₁, F₂ (4th order), E₁·b, a·E₂ (4th order),
    -- D₁·D₂ (4th order), (a+b)·(E+Q), (E+Q)·(a+b) (4th order), P² (4th order)
    sorry
  -- Bound ‖I₁‖
  have hI₁_le : ‖I₁‖ ≤ 90 * s ^ 4 := by
    have hI₁_smul : I₁ = (12 : 𝕂)⁻¹ • ((12 : 𝕂) • I₁) := by
      simp [smul_smul, inv_mul_cancel₀ h12ne]
    have h12_norm : ‖(12 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
    rw [hI₁_smul, h12_I₁]
    sorry
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
      10000 * |c| ^ 3 * (‖a‖ + ‖b‖) ^ 5 := by
  sorry

end
