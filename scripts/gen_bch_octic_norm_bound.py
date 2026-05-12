#!/usr/bin/env python3
"""Generate Lean code for `norm_bch_octic_term_le` (the norm bound on
`bch_octic_term`, the τ⁸ Taylor coefficient of `bch(a, b)`).

Mirrors `gen_bch_septic_norm_bound.py` but at one degree higher:
- Polynomial source: deg-8 part of `bch(a, b) = log(exp(a) · exp(b))`.
- LCM denominator: 120960.
- Max |scaled_num| = 432 → uniform bound 432/120960.
- 124·432/120960 = 53568/120960 = 31/70 ≤ 1, so `‖Z_8(a,b)‖ ≤ s⁸` holds.

Output is a Lean snippet (~700 lines) to paste into `BCH/Basic.lean`
right after `bch_octic_term_smul`. Uses a local `deg8_smul_word_le_basic`
helper.
"""
import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple


NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero():
    return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c):
    r = ncpoly_zero()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_a():
    r = ncpoly_zero()
    r[(0,)] = sp.Integer(1)
    return r


def ncpoly_b():
    r = ncpoly_zero()
    r[(1,)] = sp.Integer(1)
    return r


def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            r[w] = r[w] + c1 * c2
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p, max_degree):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x, max_degree):
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x, max_degree):
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


def main():
    a = ncpoly_a()
    b = ncpoly_b()
    exp_a = ncpoly_exp(a, 8)
    exp_b = ncpoly_exp(b, 8)
    prod = ncpoly_truncate(ncpoly_mul(exp_a, exp_b), 8)
    y = defaultdict(lambda: sp.Integer(0),
                    {w: c for w, c in prod.items() if w != ()})
    bch = ncpoly_log_one_plus(y, 8)
    octic = defaultdict(lambda: sp.Integer(0),
                        {w: c for w, c in bch.items() if len(w) == 8})

    items = sorted(octic.items())
    assert len(items) == 124, f"Expected 124 words, got {len(items)}"

    LCM = 120960
    entries = []
    for idx, (w, c) in enumerate(items):
        num = c.p if hasattr(c, 'p') else c.as_numer_denom()[0]
        denom = c.q if hasattr(c, 'q') else c.as_numer_denom()[1]
        scaled_num = int(num) * (LCM // int(denom))
        entries.append((idx, w, scaled_num, abs(scaled_num)))

    N_WORDS = len(entries)
    UNIFORM_MAX_NUM = max(abs_sn for _, _, _, abs_sn in entries)
    assert N_WORDS * UNIFORM_MAX_NUM <= LCM, \
        f"Uniform bound fails: {N_WORDS}*{UNIFORM_MAX_NUM}={N_WORDS*UNIFORM_MAX_NUM} > {LCM}"

    # ---------- Emit local deg8_smul_word_le helper ----------
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("/-- **Helper (deg-8, local copy)**: `‖c • (l₁·…·l8)‖ ≤ cb · s^8` if `‖c‖ ≤ cb`")
    print("and each `‖lᵢ‖ ≤ s`. -/")
    print("private lemma deg8_smul_word_le_basic")
    print("    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)")
    print("    (l1 l2 l3 l4 l5 l6 l7 l8 : 𝔸) (s : ℝ)")
    print("    (h1 : ‖l1‖ ≤ s) (h2 : ‖l2‖ ≤ s) (h3 : ‖l3‖ ≤ s) (h4 : ‖l4‖ ≤ s)")
    print("    (h5 : ‖l5‖ ≤ s) (h6 : ‖l6‖ ≤ s) (h7 : ‖l7‖ ≤ s) (h8 : ‖l8‖ ≤ s)")
    print("    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :")
    print("    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8)‖ ≤ cb * s ^ 8 := by")
    print("  calc ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8)‖")
    print("      ≤ ‖c‖ * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8‖ := norm_smul_le _ _")
    print("    _ ≤ cb * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7 * l8‖ :=")
    print("        mul_le_mul_of_nonneg_right hc (norm_nonneg _)")
    print("    _ ≤ cb * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖ * ‖l8‖) :=")
    print("        mul_le_mul_of_nonneg_left (norm_8prod_le _ _ _ _ _ _ _ _) hcb")
    print("    _ ≤ cb * (s * s * s * s * s * s * s * s) := by")
    print("        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr")
    print("    _ = cb * s ^ 8 := by ring")
    print()

    # ---------- Emit bchOcticTermN ----------
    print("-- Per-Nat-index family of terms in `bch_octic_term a b`.")
    print("set_option maxHeartbeats 1600000 in")
    print("private noncomputable def bchOcticTermN (a b : 𝔸) : Nat → 𝔸")
    for idx, w, sn, _ in entries:
        word = ' * '.join('a' if x == 0 else 'b' for x in w)
        print(f'  | {idx} => ({sn} / {LCM} : 𝕂) • ({word})')
    print('  | _ => 0')
    print()
    print(f"/-- `Fin {N_WORDS}`-indexed wrapper around `bchOcticTermN`. -/")
    print(f"private noncomputable def bchOcticTerm (a b : 𝔸) (i : Fin {N_WORDS}) : 𝔸 :=")
    print("  bchOcticTermN (𝕂 := 𝕂) a b i.val")
    print()

    # ---------- Emit Finset.sum identity ----------
    print("-- `bch_octic_term` equals the `Finset.sum` over `Fin 124` of `bchOcticTerm`.")
    print("set_option maxHeartbeats 16000000 in")
    print("set_option maxRecDepth 2000 in")
    print("private theorem bch_octic_term_eq_sum (a b : 𝔸) :")
    print(f"    bch_octic_term 𝕂 a b = ∑ i : Fin {N_WORDS}, bchOcticTerm (𝕂 := 𝕂) a b i := by")
    print("  unfold bch_octic_term bchOcticTerm")
    print("  rw [Fin.sum_univ_eq_sum_range (fun k => bchOcticTermN (𝕂 := 𝕂) a b k)]")
    print("  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bchOcticTermN, zero_add]")
    print("  try abel")
    print()

    # ---------- Emit per-i norm bound ----------
    print(f"-- Per-index norm bound: `‖bchOcticTerm a b i‖ ≤ ({UNIFORM_MAX_NUM}/{LCM}) · s^8`")
    print(f"-- (uniform: {UNIFORM_MAX_NUM} is the max `|scaled_num|` over all {N_WORDS} entries).")
    print("set_option maxHeartbeats 32000000 in")
    print("private lemma bchOcticTerm_norm_le (a b : 𝔸) (s : ℝ)")
    print("    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
    print(f"    ∀ i : Fin {N_WORDS}, ‖bchOcticTerm (𝕂 := 𝕂) a b i‖ ≤ ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^8 := fun i =>")
    print("  match i with")
    for idx, w, sn, abs_sn in entries:
        word_args = ' '.join('a' if x == 0 else 'b' for x in w)
        word_prod = ' * '.join('a' if x == 0 else 'b' for x in w)
        h_args = ' '.join(f'h{"a" if x == 0 else "b"}' for x in w)
        print(f'  | ⟨{idx}, _⟩ =>')
        print(f'    show ‖({sn} / {LCM} : 𝕂) • ({word_prod})‖ ≤ ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^8 from')
        print(f'      deg8_smul_word_le_basic ({sn} / {LCM} : 𝕂) ({UNIFORM_MAX_NUM} / {LCM} : ℝ)')
        print(f'        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)')
        print(f'        {word_args} s {h_args} (by norm_num) hs')
    print(f'  | ⟨_ + {N_WORDS}, h⟩ => absurd h (by omega)')
    print()

    # ---------- Final norm bound ----------
    abs_sum = sum(abs_sn for _, _, _, abs_sn in entries)
    print("set_option maxHeartbeats 800000 in")
    print(f"/-- **Norm bound for `bch_octic_term`**: `‖Z₈(a, b)‖ ≤ (‖a‖+‖b‖)⁸`.")
    print(f"")
    print(f"The actual Σ|coef|/{LCM} = {abs_sum}/{LCM} = {sp.Rational(abs_sum, LCM)} ≈ {float(sp.Rational(abs_sum, LCM)):.6f} (tight).")
    print(f"The proof uses a uniform per-i bound `{UNIFORM_MAX_NUM}/{LCM}` (max |scaled coef|),")
    print(f"giving `Σ ≤ {N_WORDS}·{UNIFORM_MAX_NUM}/{LCM} = {N_WORDS*UNIFORM_MAX_NUM}/{LCM} = {sp.Rational(N_WORDS*UNIFORM_MAX_NUM, LCM)} ≤ 1`. -/")
    print("theorem norm_bch_octic_term_le (a b : 𝔸) :")
    print("    ‖bch_octic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 8 := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print("  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
    print("  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
    print("  have hs8_nn : 0 ≤ s ^ 8 := pow_nonneg hs_nn 8")
    print("  rw [bch_octic_term_eq_sum]")
    print(f"  calc ‖∑ i : Fin {N_WORDS}, bchOcticTerm (𝕂 := 𝕂) a b i‖")
    print(f"      ≤ ∑ i : Fin {N_WORDS}, ‖bchOcticTerm (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin {N_WORDS}, ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^8 :=")
    print(f"        Finset.sum_le_sum (fun i _ => bchOcticTerm_norm_le (𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)")
    print(f"    _ = {N_WORDS} * (({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^8) := by")
    print(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ ≤ 1 * s^8 := by nlinarith [hs8_nn]")
    print(f"    _ = s ^ 8 := one_mul _")


if __name__ == "__main__":
    main()
