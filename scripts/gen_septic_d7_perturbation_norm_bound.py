#!/usr/bin/env python3
"""
Generate the Lean code for `norm_septic_d7_perturbation_poly_le` using the
Finset.sum approach (mirrors `gen_septic_correction_norm_bound.py`).

Reuses the (numerator, word) pairs from the d7 perturbation poly computation.
116 deg-7 terms, LCM 276480. Uniform per-term bound `MAX_ABS_NUM/LCM · s^7`;
Σ ≤ 116·MAX_ABS_NUM/LCM ≤ 1 if MAX_ABS_NUM is small enough — verified below.

Usage:  python3 gen_septic_d7_perturbation_norm_bound.py > d7_norm.lean
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple
import sys

NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero(): return defaultdict(lambda: sp.Integer(0))
def ncpoly_from_scalar(c):
    r = ncpoly_zero(); c = sp.sympify(c)
    if c != 0: r[()] = c
    return r
def ncpoly_a():
    r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r
def ncpoly_b():
    r = ncpoly_zero(); r[(1,)] = sp.Integer(1); return r
def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items(): r[w] = r[w] + c
    for w, c in q.items(): r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0: return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0), {w: c * v for w, v in p.items()})
def ncpoly_sub(p, q): return ncpoly_add(p, ncpoly_scale(q, -1))
def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_truncate(p, max_degree):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})
def ncpoly_exp(x, max_degree):
    r = ncpoly_from_scalar(1); xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        r = ncpoly_add(r, ncpoly_scale(xp, sp.Rational(1, sp.factorial(k))))
    return r
def ncpoly_log_one_plus(x, max_degree):
    r = ncpoly_zero(); xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign / sp.Integer(k)))
    return r
def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})
def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def compute_terms():
    MAX = 7
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    half_a_plus_b = ncpoly_add(half_a, b)
    z = bch_series(half_a, b, MAX)
    bz = bch_series(z, half_a, MAX)
    sym_E7 = extract_degree(ncpoly_sub(bz, ncpoly_add(a, b)), 7)
    bst_inner = extract_degree(z, 7)
    bst_outer = extract_degree(bch_series(half_a_plus_b, half_a, MAX), 7)
    correction = ncpoly_sub(sym_E7, bst_inner)
    correction = ncpoly_sub(correction, bst_outer)
    C6_inner = extract_degree(z, 6)
    bracket = ncpoly_sub(ncpoly_mul(C6_inner, half_a), ncpoly_mul(half_a, C6_inner))
    half_C6_bracket = ncpoly_scale(bracket, half)
    perturbation = ncpoly_sub(correction, half_C6_bracket)
    items = sorted([(w, c) for w, c in perturbation.items() if c != 0], key=lambda x: x[0])
    return items


def word_lean(w):
    return ' * '.join('a' if x == 0 else 'b' for x in w)
def word_args(w):
    return ' '.join('a' if x == 0 else 'b' for x in w)
def word_hyps(w):
    return ' '.join('ha' if x == 0 else 'hb' for x in w)


def main():
    items = compute_terms()
    N = len(items)
    LCM = 1
    for _, c in items:
        if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    MAX_ABS_NUM = max(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    sys.stderr.write(f"# {N} terms, LCM {LCM}, max|num| = {MAX_ABS_NUM}, Σ|num| = {sum_abs}\n")
    sys.stderr.write(f"# Σ|num|/LCM = {sum_abs}/{LCM} ≈ {sum_abs/LCM:.4f}\n")
    sys.stderr.write(f"# Uniform bound: N · max/LCM = {N}·{MAX_ABS_NUM}/{LCM} = {N*MAX_ABS_NUM}/{LCM} ≈ {N*MAX_ABS_NUM/LCM:.4f}\n")
    if N * MAX_ABS_NUM > LCM:
        sys.stderr.write(f"# WARNING: uniform bound exceeds 1; will need per-term bookkeeping\n")

    print("/-! ## Norm bound: `‖septic_d7_perturbation_poly(a, b)‖ ≤ (‖a‖+‖b‖)⁷`")
    print()
    print(f"{N} explicit deg-7 terms, max |numerator| = {MAX_ABS_NUM}, LCM = {LCM}.")
    print(f"Uniform per-term bound: {MAX_ABS_NUM}/{LCM}·s⁷. Σ ≤ {N}·{MAX_ABS_NUM}/{LCM} =")
    print(f"{N*MAX_ABS_NUM}/{LCM} ≈ {N*MAX_ABS_NUM/LCM:.4f} ≤ 1, so `‖d7_perturbation‖ ≤ s⁷`.")
    print(f"(Actual Σ|num|/{LCM} ≈ {sum_abs/LCM:.4f}.)")
    print()
    print("Uses the `Finset.sum` approach mirroring `norm_symmetric_bch_septic_correction_poly_le`.")
    print("-/")
    print()
    print(f"-- Per-Nat-index family of terms in `septic_d7_perturbation_poly a b`.")
    print("set_option maxHeartbeats 1600000 in")
    print("private noncomputable def septicD7PerturbationTermN (a b : 𝔸) : Nat → 𝔸")
    for idx, (w, c) in enumerate(items):
        n = int(sp.nsimplify(c * LCM))
        print(f"  | {idx} => ({n} / {LCM} : 𝕂) • ({word_lean(w)})")
    print("  | _ => 0")
    print()
    print(f"/-- `Fin {N}`-indexed wrapper around `septicD7PerturbationTermN`. -/")
    print("private noncomputable def septicD7PerturbationTerm (a b : 𝔸) "
          f"(i : Fin {N}) : 𝔸 :=")
    print("  septicD7PerturbationTermN (𝕂 := 𝕂) a b i.val")
    print()
    print(f"-- The {N}-term sum equals `septic_d7_perturbation_poly`.")
    print("set_option maxHeartbeats 16000000 in")
    print("set_option maxRecDepth 2000 in")
    print(f"private theorem septic_d7_perturbation_poly_eq_sum (a b : 𝔸) :")
    print(f"    septic_d7_perturbation_poly 𝕂 a b =")
    print(f"      ∑ i : Fin {N}, septicD7PerturbationTerm (𝕂 := 𝕂) a b i := by")
    print("  unfold septic_d7_perturbation_poly septicD7PerturbationTerm")
    print(f"  rw [Fin.sum_univ_eq_sum_range (fun k => septicD7PerturbationTermN (𝕂 := 𝕂) a b k)]")
    print("  simp only [Finset.sum_range_succ, Finset.sum_range_zero,")
    print("    septicD7PerturbationTermN, zero_add]")
    print()
    print(f"-- Per-index uniform bound: `‖septicD7PerturbationTerm a b i‖ ≤ ({MAX_ABS_NUM}/{LCM}) · s^7`")
    print("set_option maxHeartbeats 4000000 in")
    print(f"private lemma septicD7PerturbationTerm_norm_le (a b : 𝔸) (s : ℝ)")
    print("    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
    print(f"    ∀ i : Fin {N}, ‖septicD7PerturbationTerm (𝕂 := 𝕂) a b i‖ "
          f"≤ ({MAX_ABS_NUM} / {LCM} : ℝ) * s^7 := fun i =>")
    print("  match i with")
    for idx, (w, c) in enumerate(items):
        n = int(sp.nsimplify(c * LCM))
        wargs = word_args(w)
        whyps = word_hyps(w)
        print(f"  | ⟨{idx}, _⟩ =>")
        print(f"    show ‖({n} / {LCM} : 𝕂) • ({word_lean(w)})‖ ≤ ({MAX_ABS_NUM} / {LCM} : ℝ) * s^7 from")
        print(f"      deg7_smul_word_le ({n} / {LCM} : 𝕂) ({MAX_ABS_NUM} / {LCM} : ℝ)")
        print(f"        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)")
        print(f"        {wargs} s {whyps} (by norm_num) hs")
    print(f"  | ⟨_ + {N}, h⟩ => absurd h (by omega)")
    print()
    print("set_option maxHeartbeats 800000 in")
    print(f"/-- **Norm bound for `septic_d7_perturbation_poly`**:")
    print(f"`‖septic_d7_perturbation(a, b)‖ ≤ (‖a‖+‖b‖)⁷`.")
    print()
    print(f"Uniform per-i bound `{MAX_ABS_NUM}/{LCM}` (max |scaled coef|), giving")
    print(f"Σ ≤ {N}·{MAX_ABS_NUM}/{LCM} = {N*MAX_ABS_NUM}/{LCM} ≈ {N*MAX_ABS_NUM/LCM:.4f} ≤ 1.")
    print(f"Actual Σ|num|/{LCM} ≈ {sum_abs/LCM:.4f}.")
    print()
    print(f"Companion to `norm_symmetric_bch_septic_correction_poly_le` (the same")
    print(f"polynomial − ½·[C₆(½a,b), ½a]). -/")
    print(f"theorem norm_septic_d7_perturbation_poly_le (a b : 𝔸) :")
    print(f"    ‖septic_d7_perturbation_poly 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print("  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
    print("  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
    print("  have hs7_nn : 0 ≤ s ^ 7 := pow_nonneg hs_nn 7")
    print("  rw [septic_d7_perturbation_poly_eq_sum]")
    print(f"  calc ‖∑ i : Fin {N}, septicD7PerturbationTerm (𝕂 := 𝕂) a b i‖")
    print(f"      ≤ ∑ i : Fin {N}, ‖septicD7PerturbationTerm (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin {N}, ({MAX_ABS_NUM} / {LCM} : ℝ) * s^7 :=")
    print(f"        Finset.sum_le_sum (fun i _ => septicD7PerturbationTerm_norm_le "
          f"(𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)")
    print(f"    _ = {N} * (({MAX_ABS_NUM} / {LCM} : ℝ) * s^7) := by")
    print("        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ ≤ 1 * s^7 := by nlinarith [hs7_nn]")
    print(f"    _ = s ^ 7 := one_mul _")


if __name__ == "__main__":
    main()
