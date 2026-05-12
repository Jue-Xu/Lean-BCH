#!/usr/bin/env python3
"""Generate Lean code for `norm_bch_septic_term_diff_le` (the Lipschitz
bound on `bch_septic_term` in its first argument).

Mirrors `gen_bch_septic_norm_bound.py` but for the difference:
`‖Z₇(z, y) − Z₇(x, y)‖ ≤ 7 · M⁶ · ‖z − x‖` where `M = ‖z‖+‖x‖+‖y‖`.

Bound derivation: For each 7-letter word `letter₁·...·letter₇` with
letters in {a, b}, the difference `word(z, y) - word(x, y)` is bounded
by `k · M^6 · ‖z-x‖` where k is the count of 'a'-positions (uniform
bound ≤ 7). With max |coef_i| = 216 and divisor 30240:
`126 · (216/30240) · 7 = 6.3 ≤ 7`.

Output is a Lean snippet to paste into `BCH/Basic.lean` right after
`norm_bch_septic_term_le`. Adds 3 local helpers (word_7_diff_le_basic,
deg7_smul_word_diff_le_basic, bchSepticTerm_diff_norm_le) and the
final theorem.

Reuses the polynomial-extraction pipeline from gen_bch_septic_norm_bound.py.
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

    # Sanity: uniform-bound K = 126 * UNIFORM_MAX_NUM * 7 / LCM ≤ 7.
    K_uniform = sp.Rational(126 * UNIFORM_MAX_NUM * 7, LCM)
    assert K_uniform <= 7, f"Uniform bound {K_uniform} > 7"

    # ---------- Emit local word_7_diff_le_basic helper ----------
    print("set_option maxHeartbeats 1600000 in")
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("/-- **7-letter product Lipschitz** (local copy):")
    print("`‖x₁·…·x₇ − y₁·…·y₇‖ ≤ N⁶·Σᵢ ‖xᵢ−yᵢ‖` when `‖xᵢ‖, ‖yᵢ‖ ≤ N`.")
    print("Local copy of `SymmetricQuintic.word_7_diff_le` (unavailable upstream). -/")
    print("private lemma word_7_diff_le_basic")
    print("    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : 𝔸) (N : ℝ)")
    print("    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)")
    print("    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N)")
    print("    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)")
    print("    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N) (hN_nn : 0 ≤ N) :")
    print("    ‖x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇‖ ≤")
    print("      N ^ 6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) := by")
    print("  have hid : x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ =")
    print("      (x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ +")
    print("      y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ +")
    print("      y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ +")
    print("      y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ +")
    print("      y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ +")
    print("      y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ +")
    print("      y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) := by noncomm_ring")
    print("  rw [hid]")
    print("  have hN_pow_nn : (0 : ℝ) ≤ N ^ 6 := pow_nonneg hN_nn 6")
    print("  have ht₁ : ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₁ - y₁‖ := by")
    print("    calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇‖")
    print("        ≤ ‖x₁ - y₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _")
    print("      _ ≤ ‖x₁ - y₁‖ * N * N * N * N * N * N := by gcongr")
    print("      _ = N ^ 6 * ‖x₁ - y₁‖ := by ring")
    print("  have ht₂ : ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₂ - y₂‖ := by")
    print("    calc ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇‖")
    print("        ≤ ‖y₁‖ * ‖x₂ - y₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _")
    print("      _ ≤ N * ‖x₂ - y₂‖ * N * N * N * N * N := by gcongr")
    print("      _ = N ^ 6 * ‖x₂ - y₂‖ := by ring")
    print("  have ht₃ : ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₃ - y₃‖ := by")
    print("    calc ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇‖")
    print("        ≤ ‖y₁‖ * ‖y₂‖ * ‖x₃ - y₃‖ * ‖x₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _")
    print("      _ ≤ N * N * ‖x₃ - y₃‖ * N * N * N * N := by gcongr")
    print("      _ = N ^ 6 * ‖x₃ - y₃‖ := by ring")
    print("  have ht₄ : ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇‖ ≤ N ^ 6 * ‖x₄ - y₄‖ := by")
    print("    calc ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇‖")
    print("        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖x₄ - y₄‖ * ‖x₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _")
    print("      _ ≤ N * N * N * ‖x₄ - y₄‖ * N * N * N := by gcongr")
    print("      _ = N ^ 6 * ‖x₄ - y₄‖ := by ring")
    print("  have ht₅ : ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇‖ ≤ N ^ 6 * ‖x₅ - y₅‖ := by")
    print("    calc ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇‖")
    print("        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖x₅ - y₅‖ * ‖x₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _")
    print("      _ ≤ N * N * N * N * ‖x₅ - y₅‖ * N * N := by gcongr")
    print("      _ = N ^ 6 * ‖x₅ - y₅‖ := by ring")
    print("  have ht₆ : ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇‖ ≤ N ^ 6 * ‖x₆ - y₆‖ := by")
    print("    calc ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇‖")
    print("        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖y₅‖ * ‖x₆ - y₆‖ * ‖x₇‖ := norm_7prod_le _ _ _ _ _ _ _")
    print("      _ ≤ N * N * N * N * N * ‖x₆ - y₆‖ * N := by gcongr")
    print("      _ = N ^ 6 * ‖x₆ - y₆‖ := by ring")
    print("  have ht₇ : ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖ ≤ N ^ 6 * ‖x₇ - y₇‖ := by")
    print("    calc ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖")
    print("        ≤ ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖y₄‖ * ‖y₅‖ * ‖y₆‖ * ‖x₇ - y₇‖ := norm_7prod_le _ _ _ _ _ _ _")
    print("      _ ≤ N * N * N * N * N * N * ‖x₇ - y₇‖ := by gcongr")
    print("      _ = N ^ 6 * ‖x₇ - y₇‖ := by ring")
    print("  calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ +")
    print("        y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ +")
    print("        y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ +")
    print("        y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ +")
    print("        y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ +")
    print("        y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ +")
    print("        y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖")
    print("      ≤ ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇‖ +")
    print("          ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇‖ +")
    print("          ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇‖ +")
    print("          ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇‖ +")
    print("          ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇‖ +")
    print("          ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇‖ +")
    print("          ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇)‖ := by")
    print("        have a1 := norm_add_le")
    print("              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ + y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇)")
    print("              (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇))")
    print("        have a2 := norm_add_le")
    print("              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇)")
    print("              (y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇)")
    print("        have a3 := norm_add_le")
    print("              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇)")
    print("              (y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇)")
    print("        have a4 := norm_add_le")
    print("              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇)")
    print("              (y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇)")
    print("        have a5 := norm_add_le")
    print("              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ + y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇)")
    print("              (y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇)")
    print("        have a6 := norm_add_le")
    print("              ((x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇)")
    print("              (y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇)")
    print("        linarith")
    print("    _ ≤ N ^ 6 * ‖x₁ - y₁‖ + N ^ 6 * ‖x₂ - y₂‖ + N ^ 6 * ‖x₃ - y₃‖ + N ^ 6 * ‖x₄ - y₄‖ + N ^ 6 * ‖x₅ - y₅‖ + N ^ 6 * ‖x₆ - y₆‖ + N ^ 6 * ‖x₇ - y₇‖ := by")
    print("        linarith [ht₁, ht₂, ht₃, ht₄, ht₅, ht₆, ht₇]")
    print("    _ = N ^ 6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) := by ring")
    print()

    # ---------- Emit local deg7_smul_word_diff_le_basic helper ----------
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("/-- **Scaled 7-letter Lipschitz** (local copy):")
    print("`‖c•(x₁·…·x₇) − c•(y₁·…·y₇)‖ ≤ cb·7·N⁶·D` when `‖c‖ ≤ cb`,")
    print("`‖xᵢ‖, ‖yᵢ‖ ≤ N`, and `‖xᵢ − yᵢ‖ ≤ D`.")
    print("Local copy of `SymmetricQuintic.deg7_smul_word_diff_le`. -/")
    print("private lemma deg7_smul_word_diff_le_basic")
    print("    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)")
    print("    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : 𝔸) (N D : ℝ)")
    print("    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)")
    print("    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N)")
    print("    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)")
    print("    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N)")
    print("    (hd₁ : ‖x₁ - y₁‖ ≤ D) (hd₂ : ‖x₂ - y₂‖ ≤ D) (hd₃ : ‖x₃ - y₃‖ ≤ D)")
    print("    (hd₄ : ‖x₄ - y₄‖ ≤ D) (hd₅ : ‖x₅ - y₅‖ ≤ D) (hd₆ : ‖x₆ - y₆‖ ≤ D) (hd₇ : ‖x₇ - y₇‖ ≤ D)")
    print("    (hcb : 0 ≤ cb) (hN_nn : 0 ≤ N) (hD_nn : 0 ≤ D) :")
    print("    ‖c • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇) - c • (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇)‖ ≤")
    print("      cb * 7 * N^6 * D := by")
    print("  rw [← smul_sub]")
    print("  have hwd : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇ - y₁*y₂*y₃*y₄*y₅*y₆*y₇‖ ≤")
    print("             N^6 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖) :=")
    print("    word_7_diff_le_basic x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ hx₇ hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hy₇ hN_nn")
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

    # ---------- Emit bchSepticTerm_diff_norm_le (126-case match) ----------
    print(f"-- Per-i diff bound: `‖bchSepticTerm z y i − bchSepticTerm x y i‖ ≤ ({UNIFORM_MAX_NUM}/{LCM}) · 7 · M⁶ · ‖z−x‖`")
    print(f"-- (uniform over all 126 indices, since each word has ≤ 7 'a'-positions).")
    print("set_option maxHeartbeats 64000000 in")
    print("private lemma bchSepticTerm_diff_norm_le (z x y : 𝔸) (M : ℝ)")
    print("    (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM_nn : 0 ≤ M) :")
    print(f"    ∀ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) z y i -")
    print(f"                     bchSepticTerm (𝕂 := 𝕂) x y i‖ ≤")
    print(f"      ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 7 * M^6 * ‖z - x‖ := by")
    print("  intro i")
    print("  set D := ‖z - x‖ with hD_def")
    print("  have hD_nn : 0 ≤ D := norm_nonneg _")
    print("  have hzx_le_D : ‖z - x‖ ≤ D := le_refl _")
    print("  have hyy_le_D : ‖y - y‖ ≤ D := by rw [sub_self, norm_zero]; exact hD_nn")
    print("  match i with")
    for idx, w, sn, abs_sn in entries:
        # For word w = (letter₁, ..., letter₇), substitute z for 'a' (letter=0), y for 'b' (letter=1)
        # in LHS, and x for 'a', y for 'b' in RHS.
        lhs_letters = ['z' if lit == 0 else 'y' for lit in w]
        rhs_letters = ['x' if lit == 0 else 'y' for lit in w]
        lhs_prod = ' * '.join(lhs_letters)
        rhs_prod = ' * '.join(rhs_letters)
        lhs_args = ' '.join(lhs_letters)
        rhs_args = ' '.join(rhs_letters)
        # Per-letter norm bounds: hz at LHS a-positions, hy at LHS b-positions.
        lhs_h = ' '.join(f'h{"z" if lit == 0 else "y"}' for lit in w)
        rhs_h = ' '.join(f'h{"x" if lit == 0 else "y"}' for lit in w)
        # Per-letter diff bounds: hzx_le_D at a-positions (z vs x), hyy_le_D at b-positions (y vs y).
        diff_h = ' '.join('hzx_le_D' if lit == 0 else 'hyy_le_D' for lit in w)
        print(f'  | ⟨{idx}, _⟩ =>')
        print(f'    show ‖({sn} / {LCM} : 𝕂) • ({lhs_prod}) - ({sn} / {LCM} : 𝕂) • ({rhs_prod})‖ ≤')
        print(f'         ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 7 * M^6 * D')
        print(f'    exact deg7_smul_word_diff_le_basic ({sn} / {LCM} : 𝕂) ({UNIFORM_MAX_NUM} / {LCM} : ℝ)')
        print(f'        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)')
        print(f'        {lhs_args}')
        print(f'        {rhs_args}')
        print(f'        M D')
        print(f'        {lhs_h}')
        print(f'        {rhs_h}')
        print(f'        {diff_h}')
        print(f'        (by norm_num) hM_nn hD_nn')
    print('  | ⟨_ + 126, h⟩ => exact absurd h (by omega)')
    print()

    # ---------- Emit final theorem ----------
    print("set_option maxHeartbeats 800000 in")
    print(f"/-- **Lipschitz bound for `bch_septic_term`**: `‖Z₇(z, y) − Z₇(x, y)‖ ≤ 7·M⁶·‖z−x‖`")
    print(f"where `M = ‖z‖+‖x‖+‖y‖`.")
    print(f"")
    print(f"Analog of `norm_bch_sextic_term_diff_le` at one degree higher; with")
    print(f"`z = (a'+b) + W` and `‖W‖ = O(s²)`, gives an O(s⁸·‖W‖) bound on")
    print(f"`‖C₇(z, y) − C₇(a'+b, y)‖`. Foundation for stepping stone 1")
    print(f"(`symmetric_bch_septic_sub_poly_axiom` discharge).")
    print(f"")
    print(f"The proof uses a uniform per-i bound `({UNIFORM_MAX_NUM}/{LCM}) · 7 · M⁶ · ‖z−x‖`,")
    print(f"giving `Σ ≤ 126·{UNIFORM_MAX_NUM}·7/{LCM} = {126*UNIFORM_MAX_NUM*7}/{LCM} = {sp.Rational(126*UNIFORM_MAX_NUM*7, LCM)} ≤ 7`. -/")
    print("theorem norm_bch_septic_term_diff_le (z x y : 𝔸) :")
    print("    ‖bch_septic_term 𝕂 z y - bch_septic_term 𝕂 x y‖ ≤")
    print("      7 * (‖z‖ + ‖x‖ + ‖y‖) ^ 6 * ‖z - x‖ := by")
    print("  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def")
    print("  have hM_nn : 0 ≤ M := by positivity")
    print("  have hz_le : ‖z‖ ≤ M := by")
    print("    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]")
    print("  have hx_le : ‖x‖ ≤ M := by")
    print("    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]")
    print("  have hy_le : ‖y‖ ≤ M := by")
    print("    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]")
    print("  have hM6_nn : 0 ≤ M^6 := pow_nonneg hM_nn 6")
    print("  have hzx_nn : 0 ≤ ‖z - x‖ := norm_nonneg _")
    print("  rw [bch_septic_term_eq_sum, bch_septic_term_eq_sum, ← Finset.sum_sub_distrib]")
    print("  calc ‖∑ i : Fin 126, (bchSepticTerm (𝕂 := 𝕂) z y i - bchSepticTerm (𝕂 := 𝕂) x y i)‖")
    print("      ≤ ∑ i : Fin 126, ‖bchSepticTerm (𝕂 := 𝕂) z y i - bchSepticTerm (𝕂 := 𝕂) x y i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin 126, ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 7 * M^6 * ‖z - x‖ :=")
    print(f"        Finset.sum_le_sum (fun i _ => bchSepticTerm_diff_norm_le (𝕂 := 𝕂) z x y M hz_le hx_le hy_le hM_nn i)")
    print(f"    _ = 126 * (({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 7 * M^6 * ‖z - x‖) := by")
    print(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print("    _ ≤ 7 * M^6 * ‖z - x‖ := by nlinarith [hM6_nn, hzx_nn]")


if __name__ == "__main__":
    main()
