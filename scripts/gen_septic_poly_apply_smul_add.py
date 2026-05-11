#!/usr/bin/env python3
"""Generate `norm_symmetric_bch_septic_poly_apply_smul_add_smul_add_le`:
the deg-7 Lipschitz bound for sym_E₇ at perturbed scalar•V inputs.

Mathematical statement:
  ‖E₇(α•V + δa, β•V + δb)‖ ≤ K · N⁶ · (‖δa‖ + ‖δb‖)
where N = max(‖α•V‖, ‖β•V‖, ‖α•V+δa‖, ‖β•V+δb‖) and K = 7 (loose).

Tight value: Σ|cᵢ|/967680 · 7 ≈ 0.086·7 = 0.602. Loose: 126·6912/967680·7 ≈ 6.3.
Set bound K = 7 for clean rational. Uses uniform 6912/967680 per-i diff bound.

Approach (Finset.sum-based):
1. Use vanishing `sym_E₇(α•V, β•V) = 0` (just proved).
2. `sym_E₇(fA, fB) - sym_E₇(lA, lB) = ∑ i, (septicTerm fA fB i - septicTerm lA lB i)`.
3. Per-i bound via `septic_smul_word_diff_le` helper + uniform coefficient bound.
4. Sum with Finset.sum_const → 126 · (6912/967680) · 7 · N⁶·D = 6.3·N⁶·D ≤ 7·N⁶·D.

Generator output: ~600 lines.
"""
import sys, os
import sympy as sp
from collections import defaultdict
import math

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..',
                                'Lean-Trotter', 'scripts'))
with open(os.path.join(os.path.dirname(__file__), '..', '..',
                       'Lean-Trotter', 'scripts', 'compute_bch_r7.py')) as fh:
    exec(fh.read().split('def main')[0], globals())


def main():
    sb = strang_block_series(1, 7)
    sb_minus_one = defaultdict(lambda: sp.Integer(0), {w: c for w, c in sb.items() if w != ()})
    ls = ncpoly_log_one_plus(sb_minus_one, 7)
    sept = extract_degree(ls, 7)
    items = sorted(sept.items())
    assert len(items) == 126

    lcm = 967680
    UNIFORM_MAX_NUM = 6912

    entries = []
    for idx, (w, c) in enumerate(items):
        num = c.p if hasattr(c, 'p') else c.as_numer_denom()[0]
        denom = c.q if hasattr(c, 'q') else c.as_numer_denom()[1]
        scaled_num = int(num) * (lcm // int(denom))
        entries.append((idx, w, scaled_num, abs(scaled_num)))

    # ---------- Emit helper lemma: deg7_smul_word_diff_le ----------
    print("-- Helper: `‖c • (x₁·…·x₇) - c • (y₁·…·y₇)‖ ≤ cb · 7·N⁶·D` given")
    print("-- `‖c‖ ≤ cb`, all `‖xᵢ‖, ‖yᵢ‖ ≤ N`, all `‖xᵢ - yᵢ‖ ≤ D`.")
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("private lemma deg7_smul_word_diff_le")
    print("    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)")
    print("    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : 𝔸) (N D : ℝ)")
    print("    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N) (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N)")
    print("    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N) (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N)")
    print("    (hd₁ : ‖x₁ - y₁‖ ≤ D) (hd₂ : ‖x₂ - y₂‖ ≤ D) (hd₃ : ‖x₃ - y₃‖ ≤ D) (hd₄ : ‖x₄ - y₄‖ ≤ D) (hd₅ : ‖x₅ - y₅‖ ≤ D) (hd₆ : ‖x₆ - y₆‖ ≤ D) (hd₇ : ‖x₇ - y₇‖ ≤ D)")
    print("    (hcb : 0 ≤ cb) (hN_nn : 0 ≤ N) (hD_nn : 0 ≤ D) :")
    print("    ‖c • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇) - c • (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇)‖ ≤")
    print("      cb * 7 * N^6 * D := by")
    print("  rw [← smul_sub]")
    print("  have hwd : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ ≤")
    print("             N^6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) :=")
    print("    word_7_diff_le x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ hx₇ hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hy₇ hN_nn")
    print("  have hwd_bound : N^6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) ≤")
    print("             7 * N^6 * D := by")
    print("    have hN6_nn : 0 ≤ N^6 := pow_nonneg hN_nn 6")
    print("    nlinarith [hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇, hN6_nn]")
    print("  have hwd2 : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ ≤ 7 * N^6 * D := le_trans hwd hwd_bound")
    print("  have h_pos : 0 ≤ 7 * N^6 * D := by positivity")
    print("  calc ‖c • (x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇)‖")
    print("      ≤ ‖c‖ * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ := norm_smul_le _ _")
    print("    _ ≤ cb * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)")
    print("    _ ≤ cb * (7 * N^6 * D) := mul_le_mul_of_nonneg_left hwd2 hcb")
    print("    _ = cb * 7 * N^6 * D := by ring")
    print()

    # ---------- Emit per-i diff bound: septicTerm_diff_norm_le ----------
    print("-- Per-i bound: `‖septicTerm fA fB i - septicTerm lA lB i‖ ≤ (6912/967680) · 7 · N⁶ · D`")
    print("-- uniform over all 126 indices.")
    print("set_option maxHeartbeats 64000000 in")
    print("private lemma septicTerm_diff_norm_le (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) (N : ℝ)")
    print("    (hα_le : ‖α • V‖ ≤ N) (hβ_le : ‖β • V‖ ≤ N)")
    print("    (hα_δa_le : ‖α • V + δa‖ ≤ N) (hβ_δb_le : ‖β • V + δb‖ ≤ N)")
    print("    (hN_nn : 0 ≤ N) :")
    print(f"    ∀ i : Fin 126, ‖septicTerm (𝕂 := 𝕂) (α • V + δa) (β • V + δb) i -")
    print(f"                     septicTerm (𝕂 := 𝕂) (α • V) (β • V) i‖ ≤")
    print(f"      ({UNIFORM_MAX_NUM} / 967680 : ℝ) * 7 * N^6 * (‖δa‖ + ‖δb‖) := by")
    print(f"  intro i")
    print(f"  set D := ‖δa‖ + ‖δb‖ with hD_def")
    print(f"  have hD_nn : 0 ≤ D := by positivity")
    print(f"  have hdA_eq : ‖(α • V + δa) - (α • V)‖ = ‖δa‖ := by congr 1; abel")
    print(f"  have hdB_eq : ‖(β • V + δb) - (β • V)‖ = ‖δb‖ := by congr 1; abel")
    print(f"  have hδa_le_D : ‖δa‖ ≤ D := by rw [hD_def]; linarith [norm_nonneg δb]")
    print(f"  have hδb_le_D : ‖δb‖ ≤ D := by rw [hD_def]; linarith [norm_nonneg δa]")
    print(f"  have hdA_le : ‖(α • V + δa) - (α • V)‖ ≤ D := hdA_eq ▸ hδa_le_D")
    print(f"  have hdB_le : ‖(β • V + δb) - (β • V)‖ ≤ D := hdB_eq ▸ hδb_le_D")
    print(f"  match i with")
    for idx, w, sn, abs_sn in entries:
        word = ' * '.join(f"(α • V + δa)" if x == 0 else f"(β • V + δb)" for x in w)
        word_lin = ' * '.join(f"(α • V)" if x == 0 else f"(β • V)" for x in w)
        x_args = ' '.join(f"(α • V + δa)" if x == 0 else f"(β • V + δb)" for x in w)
        y_args = ' '.join(f"(α • V)" if x == 0 else f"(β • V)" for x in w)
        hx_args = ' '.join("hα_δa_le" if x == 0 else "hβ_δb_le" for x in w)
        hy_args = ' '.join("hα_le" if x == 0 else "hβ_le" for x in w)
        hd_args = ' '.join("hdA_le" if x == 0 else "hdB_le" for x in w)
        print(f"  | ⟨{idx}, _⟩ =>")
        print(f"    show ‖({sn} / 967680 : 𝕂) • ({word}) - ({sn} / 967680 : 𝕂) • ({word_lin})‖ ≤")
        print(f"         ({UNIFORM_MAX_NUM} / 967680 : ℝ) * 7 * N^6 * D")
        print(f"    exact deg7_smul_word_diff_le ({sn} / 967680 : 𝕂) ({UNIFORM_MAX_NUM} / 967680 : ℝ)")
        print(f"        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)")
        print(f"        {x_args}")
        print(f"        {y_args}")
        print(f"        N D")
        print(f"        {hx_args}")
        print(f"        {hy_args}")
        print(f"        {hd_args}")
        print(f"        (by norm_num) hN_nn hD_nn")
    print("  | ⟨_ + 126, h⟩ => exact absurd h (by omega)")
    print()

    # ---------- Emit the final theorem ----------
    print(f"set_option maxHeartbeats 16000000 in")
    print(f"/-- **Lipschitz bound at deg-7** (analog of `norm_symmetric_bch_quintic_poly_apply_smul_add_smul_add_le`):")
    print(f"`‖sym_E₇(α•V + δa, β•V + δb)‖ ≤ 7·N⁶·(‖δa‖+‖δb‖)`.")
    print(f"")
    print(f"Combined with the vanishing on scalar•V inputs (Stage 3.1), this gives")
    print(f"a `O(N⁶·D)` bound rather than the trivial `(2N)⁷`. Used in Stage 2's")
    print(f"5-factor BCH septic remainder decomposition. -/")
    print(f"theorem norm_symmetric_bch_septic_poly_apply_smul_add_smul_add_le")
    print(f"    (V : 𝔸) (α β : 𝕂) (δa δb : 𝔸) (N : ℝ)")
    print(f"    (hα_le : ‖α • V‖ ≤ N) (hβ_le : ‖β • V‖ ≤ N)")
    print(f"    (hα_δa_le : ‖α • V + δa‖ ≤ N) (hβ_δb_le : ‖β • V + δb‖ ≤ N)")
    print(f"    (hN_nn : 0 ≤ N) :")
    print(f"    ‖symmetric_bch_septic_poly 𝕂 (α • V + δa) (β • V + δb)‖ ≤")
    print(f"      7 * N ^ 6 * (‖δa‖ + ‖δb‖) := by")
    print(f"  set D := ‖δa‖ + ‖δb‖ with hD_def")
    print(f"  have hD_nn : 0 ≤ D := by positivity")
    print(f"  have hN6_nn : (0 : ℝ) ≤ N ^ 6 := pow_nonneg hN_nn 6")
    print(f"  have h0 : symmetric_bch_septic_poly 𝕂 (α • V) (β • V) = 0 :=")
    print(f"    symmetric_bch_septic_poly_apply_smul_smul V α β")
    print(f"  have h_diff_eq : symmetric_bch_septic_poly 𝕂 (α • V + δa) (β • V + δb) -")
    print(f"                    symmetric_bch_septic_poly 𝕂 (α • V) (β • V) =")
    print(f"      ∑ i : Fin 126, (septicTerm (𝕂 := 𝕂) (α • V + δa) (β • V + δb) i -")
    print(f"                       septicTerm (𝕂 := 𝕂) (α • V) (β • V) i) := by")
    print(f"    rw [symmetric_bch_septic_poly_eq_sum, symmetric_bch_septic_poly_eq_sum,")
    print(f"        ← Finset.sum_sub_distrib]")
    print(f"  have h_per_i := septicTerm_diff_norm_le (𝕂 := 𝕂) V α β δa δb N hα_le hβ_le hα_δa_le hβ_δb_le hN_nn")
    print(f"  calc ‖symmetric_bch_septic_poly 𝕂 (α • V + δa) (β • V + δb)‖")
    print(f"      = ‖symmetric_bch_septic_poly 𝕂 (α • V + δa) (β • V + δb) - 0‖ := by rw [sub_zero]")
    print(f"    _ = ‖symmetric_bch_septic_poly 𝕂 (α • V + δa) (β • V + δb) -")
    print(f"          symmetric_bch_septic_poly 𝕂 (α • V) (β • V)‖ := by rw [h0]")
    print(f"    _ = ‖∑ i : Fin 126, (septicTerm (𝕂 := 𝕂) (α • V + δa) (β • V + δb) i -")
    print(f"                          septicTerm (𝕂 := 𝕂) (α • V) (β • V) i)‖ := by rw [h_diff_eq]")
    print(f"    _ ≤ ∑ i : Fin 126, ‖septicTerm (𝕂 := 𝕂) (α • V + δa) (β • V + δb) i -")
    print(f"                         septicTerm (𝕂 := 𝕂) (α • V) (β • V) i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin 126, ({UNIFORM_MAX_NUM} / 967680 : ℝ) * 7 * N^6 * D :=")
    print(f"        Finset.sum_le_sum (fun i _ => h_per_i i)")
    print(f"    _ = 126 * (({UNIFORM_MAX_NUM} / 967680 : ℝ) * 7 * N^6 * D) := by")
    print(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ ≤ 7 * N^6 * D := by nlinarith [hN6_nn, hD_nn]")


if __name__ == "__main__":
    main()
