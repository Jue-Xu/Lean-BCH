#!/usr/bin/env python3
"""Generate the Lean code for `norm_symmetric_bch_septic_poly_le`:
the bound `‖symmetric_bch_septic_poly(a, b)‖ ≤ (‖a‖+‖b‖)⁷`.

Uses the session 23 Finset.sum pattern: define `septicTerm : Fin 126 → 𝔸`,
prove per-i norm bound via `deg7_smul_word_le`, sum via `Finset.sum_const`
with uniform max bound (6912/967680, giving 126 · 6912 / 967680 = 870912/967680 ≤ 1).
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
    UNIFORM_MAX_NUM = 6912  # = max(|c| · lcm) over all 126 terms

    # Build entries: (idx, word, scaled_num, abs_num)
    entries = []
    for idx, (w, c) in enumerate(items):
        num = c.p if hasattr(c, 'p') else c.as_numer_denom()[0]
        denom = c.q if hasattr(c, 'q') else c.as_numer_denom()[1]
        scaled_num = int(num) * (lcm // int(denom))
        entries.append((idx, w, scaled_num, abs(scaled_num)))

    # ---------- Emit septicTerm definition ----------
    print("-- Per-index family: 126 terms of `symmetric_bch_septic_poly a b`.")
    print("-- Each is `(scaled_num/967680 : 𝕂) • word_product`. Used in the")
    print("-- Finset.sum form of the norm bound below.")
    print("set_option maxHeartbeats 1600000 in")
    print("private noncomputable def septicTerm (a b : 𝔸) : Fin 126 → 𝔸")
    for idx, w, sn, _ in entries:
        word = ' * '.join('a' if x == 0 else 'b' for x in w)
        print(f'  | ⟨{idx}, _⟩ => ({sn} / 967680 : 𝕂) • ({word})')
    print('  | ⟨_ + 126, h⟩ => absurd h (by omega)')
    print()

    # ---------- Emit polynomial identity ----------
    print("/-- `symmetric_bch_septic_poly` equals the `Finset.sum` over `Fin 126`")
    print("of `septicTerm`. Used in the norm bound via `norm_sum_le`. -/")
    print("set_option maxHeartbeats 8000000 in")
    print("private theorem symmetric_bch_septic_poly_eq_sum (a b : 𝔸) :")
    print("    symmetric_bch_septic_poly 𝕂 a b = ∑ i : Fin 126, septicTerm (𝕂 := 𝕂) a b i := by")
    print("  unfold symmetric_bch_septic_poly")
    print("  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, septicTerm, add_zero]")
    print("  abel")
    print()

    # ---------- Emit per-i norm bound ----------
    print("-- Per-index norm bound: `‖septicTerm i‖ ≤ (6912/967680) · s^7`")
    print("-- (uniform: 6912 is the max `|scaled_num|` over all 126 entries).")
    print("set_option maxHeartbeats 32000000 in")
    print("private lemma septicTerm_norm_le (a b : 𝔸) (s : ℝ) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
    print(f"    ∀ i : Fin 126, ‖septicTerm (𝕂 := 𝕂) a b i‖ ≤ ({UNIFORM_MAX_NUM} / 967680 : ℝ) * s^7 := fun i =>")
    print("  match i with")
    for idx, w, sn, abs_sn in entries:
        word_args = ' '.join('a' if x == 0 else 'b' for x in w)
        h_args = ' '.join(f'h{"a" if x == 0 else "b"}' for x in w)
        # Goal: ‖(sn/lcm) • word‖ ≤ (6912/lcm) · s^7
        # Use deg7_smul_word_le with c = sn/lcm and cb = 6912/lcm.
        # Coefficient bound: ‖sn/lcm‖ = |sn|/lcm ≤ 6912/lcm.
        # Use `by rw [norm_div]; simp [RCLike.norm_intCast]; norm_num` or simpler.
        print(f'  | ⟨{idx}, _⟩ =>')
        print(f'    show ‖({sn} / 967680 : 𝕂) • ({word_args.replace(" ", " * ")})‖ ≤ ({UNIFORM_MAX_NUM} / 967680 : ℝ) * s^7 from')
        print(f'      deg7_smul_word_le ({sn} / 967680 : 𝕂) ({UNIFORM_MAX_NUM} / 967680 : ℝ)')
        print(f'        (by rw [norm_div]; simp [RCLike.norm_intCast]; norm_num)')
        print(f'        {word_args} s {h_args} (by norm_num) hs')
    print('  | ⟨_ + 126, h⟩ => absurd h (by omega)')
    print()

    # ---------- Emit the norm bound theorem ----------
    print(f"/-- **Norm bound for `symmetric_bch_septic_poly`**:")
    print(f"`‖E₇(a, b)‖ ≤ (‖a‖+‖b‖)⁷`.")
    print(f"")
    print(f"The actual Σ|coef|/967680 ≈ 0.086 (tight). The proof uses a uniform")
    print(f"per-i bound `6912/967680` (max |scaled coef|), giving")
    print(f"`Σ ≤ 126·6912/967680 = 870912/967680 ≤ 1`. -/")
    print("set_option maxHeartbeats 800000 in")
    print("theorem norm_symmetric_bch_septic_poly_le (a b : 𝔸) :")
    print("    ‖symmetric_bch_septic_poly 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print("  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
    print("  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
    print("  have hs7_nn : 0 ≤ s ^ 7 := pow_nonneg hs_nn 7")
    print("  rw [symmetric_bch_septic_poly_eq_sum]")
    print(f"  calc ‖∑ i : Fin 126, septicTerm (𝕂 := 𝕂) a b i‖")
    print(f"      ≤ ∑ i : Fin 126, ‖septicTerm (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin 126, ({UNIFORM_MAX_NUM} / 967680 : ℝ) * s^7 :=")
    print(f"        Finset.sum_le_sum (fun i _ => septicTerm_norm_le (𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)")
    print(f"    _ = 126 * (({UNIFORM_MAX_NUM} / 967680 : ℝ) * s^7) := by")
    print(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ ≤ 1 * s^7 := by nlinarith [hs7_nn]")
    print(f"    _ = s ^ 7 := one_mul _")


if __name__ == "__main__":
    main()
