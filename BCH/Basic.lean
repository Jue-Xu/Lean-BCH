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

/-! ### The log ∘ exp identity -/

include 𝕂 in
/-- `logOnePlus(exp(a) - 1) = a` for `‖a‖ < ln 2`: the logarithm inverts the exponential.

The proof uses the ODE/parameter-trick approach, similar to the proof of `exp_logOnePlus`
in Phase 1. We consider `f(t) = logOnePlus(exp(ta) - 1)` and show `f'(t) = a`,
hence `f(t) = ta` by constancy, giving `f(1) = a`.

**Status**: sorry (requires the same ODE infrastructure as `exp_logOnePlus` but composed
in the reverse order; to be proved in a future phase). -/
theorem logOnePlus_exp_sub_one (a : 𝔸) (ha : ‖a‖ < Real.log 2) :
    logOnePlus (𝕂 := 𝕂) (exp a - 1) = a := by
  sorry

/-! ### Norm estimate for `bch a b - (a + b)` -/

include 𝕂 in
/-- The BCH remainder bound: `‖bch(a,b) - (a+b)‖` is quadratically small.

More precisely: `bch(a,b) = (a+b) + O((‖a‖+‖b‖)² exp(‖a‖+‖b‖))`.

The proof decomposes `bch(a,b) - (a+b) = (logOnePlus(y) - y) + (y - (a+b))`
where `y = exp(a)·exp(b) - 1`, and bounds each piece:
- `‖logOnePlus(y) - y‖ ≤ ‖y‖²/(1-‖y‖)` from the log series remainder
- `‖y - (a+b)‖ = ‖exp(a)·exp(b) - 1 - a - b‖` which is O(‖a‖²+‖a‖‖b‖+‖b‖²)

**Status**: sorry (requires additional exp norm bounds `‖exp(a)-1-a‖ ≤ ‖a‖²/2 exp(‖a‖)`,
to be proved in a future phase). -/
theorem norm_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b)‖ ≤
      2 * (‖a‖ + ‖b‖) ^ 2 * Real.exp (‖a‖ + ‖b‖) := by
  sorry
/-
  set y := exp a * exp b - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hs_lt_one : s < 1 := by linarith
  have hs_lt_ln2 : s < Real.log 2 := by
    have hexp_half : Real.exp (1/2 : ℝ) < 2 := by
      have h_exp := hasSum_real_exp (1/2 : ℝ)
      have h_geom := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
      calc Real.exp (1/2 : ℝ) = ∑' n, (n !⁻¹ : ℝ) * (1/2) ^ n := h_exp.tsum_eq.symm
        _ ≤ ∑' n, (1/2 : ℝ) ^ n := h_exp.summable.tsum_le_tsum
            (fun n => by
              calc (n !⁻¹ : ℝ) * (1/2) ^ n ≤ 1 * (1/2) ^ n := by
                    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) n)
                    exact inv_le_one_of_one_le₀
                      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
                _ = (1/2) ^ n := one_mul _) h_geom.summable
        _ = (1 - 1/2)⁻¹ := h_geom.tsum_eq
        _ = 2 := by norm_num
    calc s ≤ 1/2 := hab
      _ < Real.log 2 := by rw [show (1:ℝ)/2 = Real.log (Real.exp (1/2)) from (Real.log_exp _).symm]
                          ; exact Real.log_lt_log (Real.exp_pos _).le hexp_half
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hs_lt_ln2
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have : y = (exp a - 1) * exp b + (exp b - 1) := by rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [this]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp ‖a‖ - 1) * Real.exp ‖b‖ + (Real.exp ‖b‖ - 1) := by
          gcongr; · exact norm_exp_sub_one_le (𝕂 := 𝕂) a
                  ; · linarith [Real.add_one_le_exp ‖a‖]
                  ; · exact norm_exp_le (𝕂 := 𝕂) b; · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hs_lt_ln2
      _ = 2 := Real.exp_log (by norm_num)
  have h_denom_pos : 0 < 2 - Real.exp s := by linarith
  have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) =
      (logOnePlus (𝕂 := 𝕂) y - y) + (y - (a + b)) := by unfold bch; abel
  have hpart1 : ‖logOnePlus (𝕂 := 𝕂) y - y‖ ≤ (Real.exp s - 1) ^ 2 / (2 - Real.exp s) := by
    calc _ ≤ ‖y‖ ^ 2 / (1 - ‖y‖) := norm_logOnePlus_sub_le (𝕂 := 𝕂) y hy_lt
      _ ≤ (Real.exp s - 1) ^ 2 / (1 - (Real.exp s - 1)) := by
          gcongr; · exact pow_le_pow_left (norm_nonneg _) hy_le 2; · linarith
      _ = _ := by congr 1; ring
  have hpart2 : ‖y - (a + b)‖ ≤ Real.exp s - 1 - s := by
    have hident : y - (a + b) = (exp a - 1) * (exp b - 1) + (exp a - 1 - a) + (exp b - 1 - b) := by
      rw [hy_def]; ring
    rw [hident]
    calc _ ≤ ‖(exp a - 1) * (exp b - 1)‖ + ‖exp a - 1 - a‖ + ‖exp b - 1 - b‖ := by
          calc _ ≤ ‖(exp a - 1) * (exp b - 1) + (exp a - 1 - a)‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) +
          (Real.exp ‖a‖ - 1 - ‖a‖) + (Real.exp ‖b‖ - 1 - ‖b‖) := by
          gcongr
          · calc _ ≤ ‖exp a - 1‖ * ‖exp b - 1‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; · exact norm_exp_sub_one_le (𝕂 := 𝕂) a
                         ; · linarith [Real.add_one_le_exp ‖a‖]
                         ; · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
          · exact norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
          · exact norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  -- Cross-multiply to prove: (E-1)^2/(2-E) + (E-1-s) ≤ 10s^2
  -- Equivalent to: E(1+s+10s^2) ≤ 1+2s+20s^2
  -- Using E(1-s^2/2) ≤ 1+s (from exp bound) and polynomial arithmetic for s ≤ 1/2.
  rw [hdecomp]
  calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y‖ + ‖y - (a + b)‖ := norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 2 / (2 - Real.exp s) + (Real.exp s - 1 - s) :=
        add_le_add hpart1 hpart2
    _ ≤ 10 * s ^ 2 := by
        rw [div_add_eq_add_div, div_le_iff₀ h_denom_pos]
        set E := Real.exp s
        -- E(1-s^2/2) ≤ 1+s
        have hE_bound : E * (1 - s ^ 2 / 2) ≤ 1 + s := by
          nlinarith [Real.add_one_le_exp s, sq_nonneg s, Real.exp_pos s]
        nlinarith [sq_nonneg s, sq_nonneg (s * s)]
-/

end
