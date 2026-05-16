#!/usr/bin/env python3
"""
Generate the Lean code for `norm_septic_d8_perturbation_poly_le` using the
SPLIT-HALF Finset.sum approach.

The d8 perturbation poly has 182 terms. A monolithic Finset.sum_range_succ
unfold of 182 cases hits Lean's simp recursion limit (works at ≤124 terms,
fails at 182). Splitting into two 91-term halves avoids this — each half's
proof stays well within the working range.

Structure:
1. `septicD8FirstTermN` / `septicD8SecondTermN` (Nat → 𝔸): 91 cases each.
2. `septicD8FirstTerm` / `septicD8SecondTerm` (Fin 91 → 𝔸) wrappers.
3. `septic_d8_first_eq_sum` / `septic_d8_second_eq_sum`: rewrite lemmas
   (each 91 cases → Finset.sum_range_succ × 91).
4. `septic_d8_perturbation_poly_split`: the original 182-term def equals
   the sum of the two halves' explicit forms (via `abel` on a 182-term
   reassociation).
5. `septicD8FirstTerm_norm_le` / `septicD8SecondTerm_norm_le`: per-i
   uniform bound `≤ MAX/LCM · s^8`.
6. `norm_septicD8FirstSum_le` / `norm_septicD8SecondSum_le`: ‖half‖ ≤
   91·(MAX/LCM)·s^8 = (91·MAX/LCM)·s^8.
7. `norm_septic_d8_perturbation_poly_le`: ‖d8_perturbation‖ ≤
   ‖first‖ + ‖second‖ ≤ 2·91·MAX/LCM·s^8 = 182·MAX/LCM·s^8 ≤ 1·s^8.

Usage:  python3 gen_septic_d8_perturbation_norm_bound.py > d8_norm.lean
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
    """septic_d8_perturbation = − [bch_octic(½a,b) + ½·[C₇(½a,b), ½a] + bch_octic(½a+b, ½a)]."""
    MAX = 8
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    half_a_plus_b = ncpoly_add(half_a, b)
    bch_inner = extract_degree(bch_series(half_a, b, MAX), 8)
    C7_inner = extract_degree(bch_series(half_a, b, MAX), 7)
    bracket = ncpoly_sub(ncpoly_mul(C7_inner, half_a), ncpoly_mul(half_a, C7_inner))
    half_C7_bracket = ncpoly_scale(bracket, half)
    bch_outer = extract_degree(bch_series(half_a_plus_b, half_a, MAX), 8)
    pert = ncpoly_scale(
        ncpoly_add(ncpoly_add(bch_inner, half_C7_bracket), bch_outer), -1)
    items = sorted([(w, c) for w, c in pert.items() if c != 0], key=lambda x: x[0])
    return items


def word_lean(w):
    return ' * '.join('a' if x == 0 else 'b' for x in w)
def word_args(w):
    return ' '.join('a' if x == 0 else 'b' for x in w)
def word_hyps(w):
    return ' '.join('ha' if x == 0 else 'hb' for x in w)


def emit_half_block(half_name, items_half, LCM, MAX_ABS_NUM, prefix):
    """Emit the Lean code for one half (def, eq_sum, per-i bound, sum bound)."""
    N = len(items_half)
    print(f"-- Per-Nat-index family for the {half_name} half of `septic_d8_perturbation_poly`.")
    print("set_option maxHeartbeats 1600000 in")
    print(f"private noncomputable def septicD8{prefix}TermN (a b : 𝔸) : Nat → 𝔸")
    for idx, (w, c) in enumerate(items_half):
        n = int(sp.nsimplify(c * LCM))
        print(f"  | {idx} => ({n} / {LCM} : 𝕂) • ({word_lean(w)})")
    print("  | _ => 0")
    print()
    print(f"/-- `Fin {N}`-indexed wrapper. -/")
    print(f"private noncomputable def septicD8{prefix}Term (a b : 𝔸) (i : Fin {N}) : 𝔸 :=")
    print(f"  septicD8{prefix}TermN (𝕂 := 𝕂) a b i.val")
    print()


def emit_eq_sum(half_name, items_half, prefix):
    """Emit the eq_sum lemma: explicit sum = Finset.sum."""
    N = len(items_half)
    print(f"-- The explicit {half_name}-half sum equals the Finset.sum form.")
    print("set_option maxHeartbeats 16000000 in")
    print("set_option maxRecDepth 2000 in")
    print(f"private theorem septicD8{prefix}_explicit_eq_sum (a b : 𝔸) :")
    # Explicit form on LHS.
    print("    ", end="")
    first = True
    for idx, (w, c) in enumerate(items_half):
        n = int(sp.nsimplify(c * LCM))
        prefix_sign = "" if first else " +\n      "
        first = False
        print(f"{prefix_sign}({n} / {LCM} : 𝕂) • ({word_lean(w)})", end="")
    print(f" =")
    print(f"      ∑ i : Fin {N}, septicD8{prefix}Term (𝕂 := 𝕂) a b i := by")
    print(f"  unfold septicD8{prefix}Term")
    print(f"  rw [Fin.sum_univ_eq_sum_range (fun k => septicD8{prefix}TermN (𝕂 := 𝕂) a b k)]")
    print("  simp only [Finset.sum_range_succ, Finset.sum_range_zero,")
    print(f"    septicD8{prefix}TermN, zero_add]")
    print()


def emit_per_i_bound(half_name, items_half, LCM, MAX_ABS_NUM, prefix):
    """Emit the per-i uniform bound: ‖term‖ ≤ MAX/LCM · s^8."""
    N = len(items_half)
    print(f"-- Per-index uniform bound: `‖septicD8{prefix}Term a b i‖ ≤ ({MAX_ABS_NUM}/{LCM}) · s^8`")
    print("set_option maxHeartbeats 8000000 in")
    print(f"private lemma septicD8{prefix}Term_norm_le (a b : 𝔸) (s : ℝ)")
    print("    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
    print(f"    ∀ i : Fin {N}, ‖septicD8{prefix}Term (𝕂 := 𝕂) a b i‖ "
          f"≤ ({MAX_ABS_NUM} / {LCM} : ℝ) * s^8 := fun i =>")
    print("  match i with")
    for idx, (w, c) in enumerate(items_half):
        n = int(sp.nsimplify(c * LCM))
        wargs = word_args(w)
        whyps = word_hyps(w)
        print(f"  | ⟨{idx}, _⟩ =>")
        print(f"    show ‖({n} / {LCM} : 𝕂) • ({word_lean(w)})‖ ≤ ({MAX_ABS_NUM} / {LCM} : ℝ) * s^8 from")
        print(f"      deg8_smul_word_le ({n} / {LCM} : 𝕂) ({MAX_ABS_NUM} / {LCM} : ℝ)")
        print(f"        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)")
        print(f"        {wargs} s {whyps} (by norm_num) hs")
    print(f"  | ⟨_ + {N}, h⟩ => absurd h (by omega)")
    print()


def emit_half_norm_bound(half_name, items_half, LCM, MAX_ABS_NUM, prefix):
    """Emit ‖Σ Fin N, term‖ ≤ N · MAX/LCM · s^8 (Finset.sum approach)."""
    N = len(items_half)
    print("set_option maxHeartbeats 1600000 in")
    print(f"-- Norm bound on the {half_name} half (Finset.sum form).")
    print(f"private theorem norm_septicD8{prefix}Sum_le (a b : 𝔸) :")
    print(f"    ‖∑ i : Fin {N}, septicD8{prefix}Term (𝕂 := 𝕂) a b i‖ "
          f"≤ ({N} * {MAX_ABS_NUM} / {LCM} : ℝ) * (‖a‖ + ‖b‖) ^ 8 := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print("  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
    print("  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
    print(f"  calc ‖∑ i : Fin {N}, septicD8{prefix}Term (𝕂 := 𝕂) a b i‖")
    print(f"      ≤ ∑ i : Fin {N}, ‖septicD8{prefix}Term (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin {N}, ({MAX_ABS_NUM} / {LCM} : ℝ) * s^8 :=")
    print(f"        Finset.sum_le_sum (fun i _ => septicD8{prefix}Term_norm_le "
          f"(𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)")
    print(f"    _ = {N} * (({MAX_ABS_NUM} / {LCM} : ℝ) * s^8) := by")
    print("        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ = ({N} * {MAX_ABS_NUM} / {LCM} : ℝ) * s^8 := by ring")
    print()


def main():
    items = compute_terms()
    N = len(items)
    assert N == 182, f"Expected 182 terms, got {N}"
    SPLIT = 91  # first half: 0..90, second half: 91..181
    first_items = items[:SPLIT]
    second_items = items[SPLIT:]

    global LCM, MAX_ABS_NUM
    LCM = 1
    for _, c in items:
        if c != 0: LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    MAX_ABS_NUM = max(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    sys.stderr.write(f"# {N} terms (split {SPLIT}/{N-SPLIT}), LCM {LCM}, "
                     f"max|num| = {MAX_ABS_NUM}, Σ|num| = {sum_abs}\n")
    sys.stderr.write(f"# Σ|num|/LCM = {sum_abs}/{LCM} ≈ {sum_abs/LCM:.4f}\n")
    sys.stderr.write(f"# Each half bound: {SPLIT}·{MAX_ABS_NUM}/{LCM} = "
                     f"{SPLIT*MAX_ABS_NUM}/{LCM} ≈ {SPLIT*MAX_ABS_NUM/LCM:.4f}\n")
    sys.stderr.write(f"# Combined bound: {N}·{MAX_ABS_NUM}/{LCM} = "
                     f"{N*MAX_ABS_NUM}/{LCM} ≈ {N*MAX_ABS_NUM/LCM:.4f}\n")

    print("/-! ## Norm bound: `‖septic_d8_perturbation_poly(a, b)‖ ≤ (‖a‖+‖b‖)⁸`")
    print()
    print(f"{N} explicit deg-8 terms, max |numerator| = {MAX_ABS_NUM}, LCM = {LCM}.")
    print("Uses the **split-half** Finset.sum approach: the 182-term def is split")
    print(f"into two {SPLIT}-term halves at definition time, each provable via the")
    print("Finset.sum_range_succ pattern (which works reliably at ≤124 terms but")
    print("hits a simp recursion limit at 182). The two halves are combined via")
    print("`abel` and triangle inequality.")
    print()
    print(f"Combined bound: Σ ≤ {N}·{MAX_ABS_NUM}/{LCM} = {N*MAX_ABS_NUM}/{LCM} "
          f"≈ {N*MAX_ABS_NUM/LCM:.4f} ≤ 1, so `‖d8_perturbation‖ ≤ s⁸`.")
    print(f"(Actual Σ|num|/{LCM} ≈ {sum_abs/LCM:.4f}.)")
    print("-/")
    print()

    # First half infrastructure.
    emit_half_block("first", first_items, LCM, MAX_ABS_NUM, "First")
    emit_eq_sum("first", first_items, "First")
    emit_per_i_bound("first", first_items, LCM, MAX_ABS_NUM, "First")
    emit_half_norm_bound("first", first_items, LCM, MAX_ABS_NUM, "First")

    # Second half infrastructure.
    emit_half_block("second", second_items, LCM, MAX_ABS_NUM, "Second")
    emit_eq_sum("second", second_items, "Second")
    emit_per_i_bound("second", second_items, LCM, MAX_ABS_NUM, "Second")
    emit_half_norm_bound("second", second_items, LCM, MAX_ABS_NUM, "Second")

    # The split theorem: poly = first_explicit + second_explicit.
    print(f"-- The full 182-term def equals the sum of the two halves' explicit forms.")
    print(f"-- Reassociation of a 182-term `+`-tree via `abel` (handles add_assoc/comm).")
    print(f"set_option maxHeartbeats 64000000 in")
    print(f"private theorem septic_d8_perturbation_poly_split (a b : 𝔸) :")
    print(f"    septic_d8_perturbation_poly 𝕂 a b =")
    print(f"      (", end="")
    first = True
    for idx, (w, c) in enumerate(first_items):
        n = int(sp.nsimplify(c * LCM))
        prefix_sign = "" if first else " +\n        "
        first = False
        print(f"{prefix_sign}({n} / {LCM} : 𝕂) • ({word_lean(w)})", end="")
    print(f") +")
    print(f"      (", end="")
    first = True
    for idx, (w, c) in enumerate(second_items):
        n = int(sp.nsimplify(c * LCM))
        prefix_sign = "" if first else " +\n        "
        first = False
        print(f"{prefix_sign}({n} / {LCM} : 𝕂) • ({word_lean(w)})", end="")
    print(f") := by")
    print(f"  unfold septic_d8_perturbation_poly")
    print(f"  abel")
    print()

    # Final norm bound.
    print(f"/-- **Norm bound for `septic_d8_perturbation_poly`**:")
    print(f"`‖septic_d8_perturbation(a, b)‖ ≤ (‖a‖+‖b‖)⁸`.")
    print()
    print(f"Uses the **split-half** approach: ‖poly‖ ≤ ‖first‖ + ‖second‖ ≤")
    print(f"2·{SPLIT}·{MAX_ABS_NUM}/{LCM}·s⁸ = {N*MAX_ABS_NUM}/{LCM}·s⁸ ≈ "
          f"{N*MAX_ABS_NUM/LCM:.4f}·s⁸ ≤ s⁸.")
    print(f"Actual Σ|num|/{LCM} ≈ {sum_abs/LCM:.4f}.")
    print()
    print(f"Companion to `norm_septic_d7_perturbation_poly_le` at one degree higher.")
    print(f"By `septic_d8_cancellation_poly_form`,")
    print(f"`d8_perturbation = -(C₈(½a,b) + ½·[C₇(½a,b), ½a] + C₈(½a+b, ½a))`. -/")
    print(f"theorem norm_septic_d8_perturbation_poly_le (a b : 𝔸) :")
    print(f"    ‖septic_d8_perturbation_poly 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 8 := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print("  have hs8_nn : 0 ≤ s ^ 8 := pow_nonneg hs_nn 8")
    print("  rw [septic_d8_perturbation_poly_split,")
    print("      septicD8First_explicit_eq_sum,")
    print("      septicD8Second_explicit_eq_sum]")
    print(f"  calc ‖(∑ i : Fin {SPLIT}, septicD8FirstTerm (𝕂 := 𝕂) a b i) + "
          f"(∑ i : Fin {SPLIT}, septicD8SecondTerm (𝕂 := 𝕂) a b i)‖")
    print(f"      ≤ ‖∑ i : Fin {SPLIT}, septicD8FirstTerm (𝕂 := 𝕂) a b i‖ +")
    print(f"          ‖∑ i : Fin {SPLIT}, septicD8SecondTerm (𝕂 := 𝕂) a b i‖ := norm_add_le _ _")
    print(f"    _ ≤ ({SPLIT} * {MAX_ABS_NUM} / {LCM} : ℝ) * s^8 +")
    print(f"          ({SPLIT} * {MAX_ABS_NUM} / {LCM} : ℝ) * s^8 :=")
    print(f"        add_le_add (norm_septicD8FirstSum_le a b) (norm_septicD8SecondSum_le a b)")
    print(f"    _ ≤ 1 * s^8 := by nlinarith [hs8_nn]")
    print(f"    _ = s ^ 8 := one_mul _")


if __name__ == "__main__":
    main()
