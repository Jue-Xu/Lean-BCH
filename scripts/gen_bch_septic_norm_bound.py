#!/usr/bin/env python3
"""Generate Lean code for `norm_bch_septic_term_le` (the norm bound on
`bch_septic_term`, the τ⁷ Taylor coefficient of `bch(a, b)`).

Mirrors `gen_septic_poly_norm_bound.py` but:
- Polynomial source: `bch(a, b) = log(exp(a) · exp(b))` (not the strang block).
- LCM denominator: 30240 (not 967680).
- Max |scaled_num| = 216 → uniform bound 216/30240.
- 126·216/30240 = 27216/30240 = 9/10 ≤ 1, so `‖Z_7(a,b)‖ ≤ s⁷` holds.

Output is a Lean snippet (~700 lines) to paste into `BCH/Basic.lean`
right after `bch_septic_term_smul`. Uses a local `deg7_smul_word_le_basic`
helper since `deg7_smul_word_le` (in SymmetricQuintic.lean) is downstream.

Pipeline:
  1. Local NCPoly expansion of `bch(a, b)` to deg 7.
  2. Sort 126 non-zero 7-letter words; assign Nat index 0..125.
  3. Emit: `bchSepticTermN : Nat → 𝔸`, `bchSepticTerm : Fin 126 → 𝔸`,
     `bch_septic_term_eq_sum`, `bchSepticTerm_norm_le`,
     `norm_bch_septic_term_le`.
"""
import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple


NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero() -> NCPoly:
    return defaultdict(lambda: sp.Integer(0))


def ncpoly_from_scalar(c) -> NCPoly:
    r = ncpoly_zero()
    c = sp.sympify(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_a() -> NCPoly:
    r = ncpoly_zero()
    r[(0,)] = sp.Integer(1)
    return r


def ncpoly_b() -> NCPoly:
    r = ncpoly_zero()
    r[(1,)] = sp.Integer(1)
    return r


def ncpoly_add(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] = r[w] + c
    for w, c in q.items():
        r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p: NCPoly, c) -> NCPoly:
    c = sp.sympify(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_mul(p: NCPoly, q: NCPoly) -> NCPoly:
    r = ncpoly_zero()
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            r[w] = r[w] + c1 * c2
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p: NCPoly, max_degree: int) -> NCPoly:
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})


def ncpoly_exp(x: NCPoly, max_degree: int) -> NCPoly:
    result = ncpoly_from_scalar(1)
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        result = ncpoly_add(result, ncpoly_scale(x_power, sp.Rational(1, sp.factorial(k))))
    return result


def ncpoly_log_one_plus(x: NCPoly, max_degree: int) -> NCPoly:
    result = ncpoly_zero()
    x_power = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        x_power = ncpoly_truncate(ncpoly_mul(x_power, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        result = ncpoly_add(result, ncpoly_scale(x_power, sign / sp.Integer(k)))
    return result


def main():
    # Compute bch_septic_term polynomial.
    a = ncpoly_a()
    b = ncpoly_b()
    exp_a = ncpoly_exp(a, 7)
    exp_b = ncpoly_exp(b, 7)
    prod = ncpoly_truncate(ncpoly_mul(exp_a, exp_b), 7)
    y = defaultdict(lambda: sp.Integer(0),
                    {w: c for w, c in prod.items() if w != ()})
    bch = ncpoly_log_one_plus(y, 7)
    septic = defaultdict(lambda: sp.Integer(0),
                         {w: c for w, c in bch.items() if len(w) == 7})

    items = sorted(septic.items())
    assert len(items) == 126, f"Expected 126 words, got {len(items)}"

    LCM = 30240
    entries = []
    for idx, (w, c) in enumerate(items):
        num = c.p if hasattr(c, 'p') else c.as_numer_denom()[0]
        denom = c.q if hasattr(c, 'q') else c.as_numer_denom()[1]
        scaled_num = int(num) * (LCM // int(denom))
        entries.append((idx, w, scaled_num, abs(scaled_num)))

    UNIFORM_MAX_NUM = max(abs_sn for _, _, _, abs_sn in entries)
    # Verify: 126 * UNIFORM_MAX_NUM / LCM ≤ 1.
    assert 126 * UNIFORM_MAX_NUM <= LCM, \
        f"Uniform bound fails: 126*{UNIFORM_MAX_NUM}={126*UNIFORM_MAX_NUM} > {LCM}"

    # ---------- Emit local deg7_smul_word_le helper ----------
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("/-- **Helper (deg-7, local copy)**: `‖c • (l₁·…·l7)‖ ≤ cb · s^7` if `‖c‖ ≤ cb`")
    print("and each `‖lᵢ‖ ≤ s`. Local copy of `SymmetricQuintic.deg7_smul_word_le`")
    print("(unavailable upstream in Basic.lean). -/")
    print("private lemma deg7_smul_word_le_basic")
    print("    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)")
    print("    (l1 l2 l3 l4 l5 l6 l7 : 𝔸) (s : ℝ)")
    print("    (h1 : ‖l1‖ ≤ s) (h2 : ‖l2‖ ≤ s) (h3 : ‖l3‖ ≤ s) (h4 : ‖l4‖ ≤ s) (h5 : ‖l5‖ ≤ s) (h6 : ‖l6‖ ≤ s) (h7 : ‖l7‖ ≤ s)")
    print("    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :")
    print("    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7)‖ ≤ cb * s ^ 7 := by")
    print("  calc ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7)‖")
    print("      ≤ ‖c‖ * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖ := norm_smul_le _ _")
    print("    _ ≤ cb * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖ :=")
    print("        mul_le_mul_of_nonneg_right hc (norm_nonneg _)")
    print("    _ ≤ cb * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖) :=")
    print("        mul_le_mul_of_nonneg_left (norm_7prod_le _ _ _ _ _ _ _) hcb")
    print("    _ ≤ cb * (s * s * s * s * s * s * s) := by")
    print("        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr")
    print("    _ = cb * s ^ 7 := by ring")
    print()

    # ---------- Emit bchSepticTermN ----------
    print("-- Per-Nat-index family of terms in `bch_septic_term a b`.")
    print("-- Defined on Nat (not Fin) so `Finset.range`-based reduction works.")
    print("set_option maxHeartbeats 1600000 in")
    print("private noncomputable def bchSepticTermN (a b : 𝔸) : Nat → 𝔸")
    for idx, w, sn, _ in entries:
        word = ' * '.join('a' if x == 0 else 'b' for x in w)
        print(f'  | {idx} => ({sn} / {LCM} : 𝕂) • ({word})')
    print('  | _ => 0')
    print()
    print("/-- `Fin 126`-indexed wrapper around `bchSepticTermN`. -/")
    print("private noncomputable def bchSepticTerm (a b : 𝔸) (i : Fin 126) : 𝔸 :=")
    print("  bchSepticTermN (𝕂 := 𝕂) a b i.val")
    print()

    # ---------- Emit Finset.sum identity ----------
    print("-- `bch_septic_term` equals the `Finset.sum` over `Fin 126` of")
    print("-- `bchSepticTerm`. Used in the norm bound via `norm_sum_le`.")
    print("set_option maxHeartbeats 16000000 in")
    print("set_option maxRecDepth 2000 in")
    print("private theorem bch_septic_term_eq_sum (a b : 𝔸) :")
    print("    bch_septic_term 𝕂 a b = ∑ i : Fin 126, bchSepticTerm (𝕂 := 𝕂) a b i := by")
    print("  unfold bch_septic_term bchSepticTerm")
    print("  rw [Fin.sum_univ_eq_sum_range (fun k => bchSepticTermN (𝕂 := 𝕂) a b k)]")
    print("  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bchSepticTermN, zero_add]")
    print("  try abel")
    print()

    # ---------- Emit per-i norm bound ----------
    print(f"-- Per-index norm bound: `‖bchSepticTerm a b i‖ ≤ ({UNIFORM_MAX_NUM}/{LCM}) · s^7`")
    print(f"-- (uniform: {UNIFORM_MAX_NUM} is the max `|scaled_num|` over all 126 entries).")
    print("set_option maxHeartbeats 32000000 in")
    print("private lemma bchSepticTerm_norm_le (a b : 𝔸) (s : ℝ)")
    print("    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
    print(f"    ∀ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) a b i‖ ≤ ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^7 := fun i =>")
    print("  match i with")
    for idx, w, sn, abs_sn in entries:
        word_args = ' '.join('a' if x == 0 else 'b' for x in w)
        word_prod = ' * '.join('a' if x == 0 else 'b' for x in w)
        h_args = ' '.join(f'h{"a" if x == 0 else "b"}' for x in w)
        print(f'  | ⟨{idx}, _⟩ =>')
        print(f'    show ‖({sn} / {LCM} : 𝕂) • ({word_prod})‖ ≤ ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^7 from')
        print(f'      deg7_smul_word_le_basic ({sn} / {LCM} : 𝕂) ({UNIFORM_MAX_NUM} / {LCM} : ℝ)')
        print(f'        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)')
        print(f'        {word_args} s {h_args} (by norm_num) hs')
    print('  | ⟨_ + 126, h⟩ => absurd h (by omega)')
    print()

    # ---------- Final norm bound ----------
    abs_sum = sum(abs_sn for _, _, _, abs_sn in entries)
    print("set_option maxHeartbeats 800000 in")
    print(f"/-- **Norm bound for `bch_septic_term`**: `‖Z₇(a, b)‖ ≤ (‖a‖+‖b‖)⁷`.")
    print(f"")
    print(f"The actual Σ|coef|/{LCM} = {abs_sum}/{LCM} = {sp.Rational(abs_sum, LCM)} ≈ {float(sp.Rational(abs_sum, LCM)):.6f} (tight).")
    print(f"The proof uses a uniform per-i bound `{UNIFORM_MAX_NUM}/{LCM}` (max |scaled coef|),")
    print(f"giving `Σ ≤ 126·{UNIFORM_MAX_NUM}/{LCM} = {126*UNIFORM_MAX_NUM}/{LCM} = {sp.Rational(126*UNIFORM_MAX_NUM, LCM)} ≤ 1`. -/")
    print("theorem norm_bch_septic_term_le (a b : 𝔸) :")
    print("    ‖bch_septic_term 𝕂 a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print("  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
    print("  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
    print("  have hs7_nn : 0 ≤ s ^ 7 := pow_nonneg hs_nn 7")
    print("  rw [bch_septic_term_eq_sum]")
    print(f"  calc ‖∑ i : Fin 126, bchSepticTerm (𝕂 := 𝕂) a b i‖")
    print(f"      ≤ ∑ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin 126, ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^7 :=")
    print(f"        Finset.sum_le_sum (fun i _ => bchSepticTerm_norm_le (𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)")
    print(f"    _ = 126 * (({UNIFORM_MAX_NUM} / {LCM} : ℝ) * s^7) := by")
    print(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ ≤ 1 * s^7 := by nlinarith [hs7_nn]")
    print(f"    _ = s ^ 7 := one_mul _")


if __name__ == "__main__":
    main()
