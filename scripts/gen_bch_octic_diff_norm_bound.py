#!/usr/bin/env python3
"""Generate Lean code for `norm_bch_octic_term_diff_le` (the Lipschitz
bound on `bch_octic_term` in its first argument).

Mirrors `gen_bch_septic_diff_norm_bound.py` (session 28) but at one
degree higher: `‖Z₈(z, y) − Z₈(x, y)‖ ≤ 8 · M⁷ · ‖z − x‖` where
`M = ‖z‖+‖x‖+‖y‖`.

Bound derivation: For each 8-letter word `letter₁·...·letter₈` with
letters in {a, b}, the difference `word(z, y) - word(x, y)` is bounded
by `k · M^7 · ‖z-x‖` where k is the count of 'a'-positions (uniform
bound ≤ 8). With max |coef| = 432 and divisor 120960:
`124 · (432/120960) · 8 = 31/35·8 = 31·8/35 = 248/35 ≈ 7.09 ≤ 8`.

Output is a Lean snippet to paste into `BCH/Basic.lean` right after
`norm_bch_octic_term_le` (or after `bch_octic_term_apply_smul_smul`).
Adds 3 local helpers (word_8_diff_le_basic, deg8_smul_word_diff_le_basic,
bchOcticTerm_diff_norm_le) and the final theorem.

Reuses the polynomial-extraction pipeline from gen_bch_septic_diff_norm_bound.py.
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
    # Bound check: N_WORDS·UNIFORM_MAX_NUM·8/LCM ≤ 8.
    K_uniform = sp.Rational(N_WORDS * UNIFORM_MAX_NUM * 8, LCM)
    assert K_uniform <= 8, f"Uniform bound {K_uniform} > 8"

    # ---------- Emit word_8_diff_le_basic ----------
    print("set_option maxHeartbeats 1600000 in")
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("/-- **8-letter product Lipschitz** (local copy, deg-9 analog of `word_7_diff_le_basic`):")
    print("`‖x₁·…·x₈ − y₁·…·y₈‖ ≤ N⁷·Σᵢ ‖xᵢ−yᵢ‖` when `‖xᵢ‖, ‖yᵢ‖ ≤ N`. -/")
    print("private lemma word_8_diff_le_basic")
    print("    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : 𝔸) (N : ℝ)")
    print("    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)")
    print("    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N) (hx₈ : ‖x₈‖ ≤ N)")
    print("    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)")
    print("    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N) (hy₈ : ‖y₈‖ ≤ N) (hN_nn : 0 ≤ N) :")
    print("    ‖x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * y₈‖ ≤")
    print("      N ^ 7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) := by")
    print("  have hid : x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ - y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * y₈ =")
    print("      (x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +")
    print("      y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +")
    print("      y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈ +")
    print("      y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈ +")
    print("      y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈ +")
    print("      y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈ +")
    print("      y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈ +")
    print("      y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈) := by noncomm_ring")
    print("  rw [hid]")
    print("  have hN_pow_nn : (0 : ℝ) ≤ N ^ 7 := pow_nonneg hN_nn 7")
    # 8 per-term bounds, one per position. Use Unicode subscript names for consistency with signature.
    sub_digits = '₀₁₂₃₄₅₆₇₈₉'
    def sub(n):
        return ''.join(sub_digits[int(d)] for d in str(n))
    for i in range(1, 9):
        ys = ' * '.join([f'y{sub(j)}' for j in range(1, i)] + [f'(x{sub(i)} - y{sub(i)})'] + [f'x{sub(j)}' for j in range(i+1, 9)])
        n_factors = ' * '.join(['‖y'+sub(j)+'‖' for j in range(1, i)] + [f'‖x{sub(i)} - y{sub(i)}‖'] + [f'‖x{sub(j)}‖' for j in range(i+1, 9)])
        ns = ' * '.join(['N']*(i-1) + [f'‖x{sub(i)} - y{sub(i)}‖'] + ['N']*(8-i))
        print(f"  have ht{i} : ‖{ys}‖ ≤ N ^ 7 * ‖x{sub(i)} - y{sub(i)}‖ := by")
        print(f"    calc ‖{ys}‖")
        print(f"        ≤ {n_factors} := norm_8prod_le _ _ _ _ _ _ _ _")
        print(f"      _ ≤ {ns} := by gcongr")
        print(f"      _ = N ^ 7 * ‖x{sub(i)} - y{sub(i)}‖ := by ring")
    # Combine via norm_add_le chain.
    print("  calc ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +")
    print("        y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈ +")
    print("        y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈ +")
    print("        y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈ +")
    print("        y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈ +")
    print("        y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈ +")
    print("        y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈ +")
    print("        y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈)‖")
    print("      ≤ ‖(x₁ - y₁) * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖ +")
    print("          ‖y₁ * (x₂ - y₂) * x₃ * x₄ * x₅ * x₆ * x₇ * x₈‖ +")
    print("          ‖y₁ * y₂ * (x₃ - y₃) * x₄ * x₅ * x₆ * x₇ * x₈‖ +")
    print("          ‖y₁ * y₂ * y₃ * (x₄ - y₄) * x₅ * x₆ * x₇ * x₈‖ +")
    print("          ‖y₁ * y₂ * y₃ * y₄ * (x₅ - y₅) * x₆ * x₇ * x₈‖ +")
    print("          ‖y₁ * y₂ * y₃ * y₄ * y₅ * (x₆ - y₆) * x₇ * x₈‖ +")
    print("          ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * (x₇ - y₇) * x₈‖ +")
    print("          ‖y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * (x₈ - y₈)‖ := by")
    # The 7 chained norm_add_le steps.
    terms_so_far = []
    for i in range(1, 9):
        ys = ' * '.join([f'y{sub(j)}' for j in range(1, i)] + [f'(x{sub(i)} - y{sub(i)})'] + [f'x{sub(j)}' for j in range(i+1, 9)])
        terms_so_far.append(f"({ys})")
    # Chain: norm_add_le of (sum of first k terms) + (k+1)-th term, for k=7, 6, ..., 1.
    for k in range(7, 0, -1):
        lhs_sum = ' + '.join(terms_so_far[:k])
        rhs = terms_so_far[k][1:-1]  # strip outer parens
        print(f"        have a{8-k} := norm_add_le")
        print(f"              ({lhs_sum})")
        print(f"              ({rhs})")
    print("        linarith")
    print("    _ ≤ " + " + ".join([f"N ^ 7 * ‖x{sub(i)} - y{sub(i)}‖" for i in range(1, 9)]) + " := by")
    print(f"        linarith [{', '.join('ht'+str(i) for i in range(1, 9))}]")
    print("    _ = N ^ 7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) := by ring")
    print()

    # ---------- Emit deg8_smul_word_diff_le_basic ----------
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("/-- **Scaled 8-letter Lipschitz** (local copy, deg-9 analog of `deg7_smul_word_diff_le_basic`):")
    print("`‖c•(x₁·…·x₈) − c•(y₁·…·y₈)‖ ≤ cb·8·N⁷·D` when `‖c‖ ≤ cb`, all `‖xᵢ‖, ‖yᵢ‖ ≤ N`, all `‖xᵢ-yᵢ‖ ≤ D`. -/")
    print("private lemma deg8_smul_word_diff_le_basic")
    print("    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)")
    print("    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : 𝔸) (N D : ℝ)")
    print("    (hx₁ : ‖x₁‖ ≤ N) (hx₂ : ‖x₂‖ ≤ N) (hx₃ : ‖x₃‖ ≤ N) (hx₄ : ‖x₄‖ ≤ N)")
    print("    (hx₅ : ‖x₅‖ ≤ N) (hx₆ : ‖x₆‖ ≤ N) (hx₇ : ‖x₇‖ ≤ N) (hx₈ : ‖x₈‖ ≤ N)")
    print("    (hy₁ : ‖y₁‖ ≤ N) (hy₂ : ‖y₂‖ ≤ N) (hy₃ : ‖y₃‖ ≤ N) (hy₄ : ‖y₄‖ ≤ N)")
    print("    (hy₅ : ‖y₅‖ ≤ N) (hy₆ : ‖y₆‖ ≤ N) (hy₇ : ‖y₇‖ ≤ N) (hy₈ : ‖y₈‖ ≤ N)")
    print("    (hd₁ : ‖x₁ - y₁‖ ≤ D) (hd₂ : ‖x₂ - y₂‖ ≤ D) (hd₃ : ‖x₃ - y₃‖ ≤ D) (hd₄ : ‖x₄ - y₄‖ ≤ D)")
    print("    (hd₅ : ‖x₅ - y₅‖ ≤ D) (hd₆ : ‖x₆ - y₆‖ ≤ D) (hd₇ : ‖x₇ - y₇‖ ≤ D) (hd₈ : ‖x₈ - y₈‖ ≤ D)")
    print("    (hcb : 0 ≤ cb) (hN_nn : 0 ≤ N) (hD_nn : 0 ≤ D) :")
    print("    ‖c • (x₁ * x₂ * x₃ * x₄ * x₅ * x₆ * x₇ * x₈) - c • (y₁ * y₂ * y₃ * y₄ * y₅ * y₆ * y₇ * y₈)‖ ≤")
    print("      cb * 8 * N^7 * D := by")
    print("  rw [← smul_sub]")
    print("  have hwd : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ ≤")
    print("             N^7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) :=")
    print("    word_8_diff_le_basic x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ hx₇ hx₈ hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hy₇ hy₈ hN_nn")
    print("  have hwd_bound : N^7 * (‖x₁ - y₁‖ + ‖x₂ - y₂‖ + ‖x₃ - y₃‖ + ‖x₄ - y₄‖ + ‖x₅ - y₅‖ + ‖x₆ - y₆‖ + ‖x₇ - y₇‖ + ‖x₈ - y₈‖) ≤")
    print("             8 * N^7 * D := by")
    print("    have hN7_nn : 0 ≤ N^7 := pow_nonneg hN_nn 7")
    print("    nlinarith [hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇, hd₈, hN7_nn]")
    print("  have hwd2 : ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ ≤ 8 * N^7 * D := le_trans hwd hwd_bound")
    print("  have h_pos : 0 ≤ 8 * N^7 * D := by positivity")
    print("  calc ‖c • (x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈)‖")
    print("      ≤ ‖c‖ * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ := norm_smul_le _ _")
    print("    _ ≤ cb * ‖x₁*x₂*x₃*x₄*x₅*x₆*x₇*x₈ - y₁*y₂*y₃*y₄*y₅*y₆*y₇*y₈‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)")
    print("    _ ≤ cb * (8 * N^7 * D) := mul_le_mul_of_nonneg_left hwd2 hcb")
    print("    _ = cb * 8 * N^7 * D := by ring")
    print()

    # ---------- Emit bchOcticTerm_diff_norm_le (124-case match) ----------
    print(f"-- Per-i diff bound: `‖bchOcticTerm z y i − bchOcticTerm x y i‖ ≤ ({UNIFORM_MAX_NUM}/{LCM}) · 8 · M⁷ · ‖z−x‖`")
    print(f"-- (uniform over all {N_WORDS} indices, since each word has ≤ 8 'a'-positions).")
    print("set_option maxHeartbeats 64000000 in")
    print("private lemma bchOcticTerm_diff_norm_le (z x y : 𝔸) (M : ℝ)")
    print("    (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM_nn : 0 ≤ M) :")
    print(f"    ∀ i : Fin {N_WORDS}, ‖bchOcticTerm (𝕂 := 𝕂) z y i -")
    print(f"                     bchOcticTerm (𝕂 := 𝕂) x y i‖ ≤")
    print(f"      ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 8 * M^7 * ‖z - x‖ := by")
    print("  intro i")
    print("  set D := ‖z - x‖ with hD_def")
    print("  have hD_nn : 0 ≤ D := norm_nonneg _")
    print("  have hzx_le_D : ‖z - x‖ ≤ D := le_refl _")
    print("  have hyy_le_D : ‖y - y‖ ≤ D := by rw [sub_self, norm_zero]; exact hD_nn")
    print("  match i with")
    for idx, w, sn, abs_sn in entries:
        lhs_letters = ['z' if lit == 0 else 'y' for lit in w]
        rhs_letters = ['x' if lit == 0 else 'y' for lit in w]
        lhs_prod = ' * '.join(lhs_letters)
        rhs_prod = ' * '.join(rhs_letters)
        lhs_args = ' '.join(lhs_letters)
        rhs_args = ' '.join(rhs_letters)
        lhs_h = ' '.join(f'h{"z" if lit == 0 else "y"}' for lit in w)
        rhs_h = ' '.join(f'h{"x" if lit == 0 else "y"}' for lit in w)
        diff_h = ' '.join('hzx_le_D' if lit == 0 else 'hyy_le_D' for lit in w)
        print(f'  | ⟨{idx}, _⟩ =>')
        print(f'    show ‖({sn} / {LCM} : 𝕂) • ({lhs_prod}) - ({sn} / {LCM} : 𝕂) • ({rhs_prod})‖ ≤')
        print(f'         ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 8 * M^7 * D')
        print(f'    exact deg8_smul_word_diff_le_basic ({sn} / {LCM} : 𝕂) ({UNIFORM_MAX_NUM} / {LCM} : ℝ)')
        print(f'        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)')
        print(f'        {lhs_args}')
        print(f'        {rhs_args}')
        print(f'        M D')
        print(f'        {lhs_h}')
        print(f'        {rhs_h}')
        print(f'        {diff_h}')
        print(f'        (by norm_num) hM_nn hD_nn')
    print(f'  | ⟨_ + {N_WORDS}, h⟩ => exact absurd h (by omega)')
    print()

    # ---------- Emit final theorem ----------
    print("set_option maxHeartbeats 800000 in")
    print(f"/-- **Lipschitz bound for `bch_octic_term`**: `‖Z₈(z, y) − Z₈(x, y)‖ ≤ 8·M⁷·‖z−x‖`")
    print(f"where `M = ‖z‖+‖x‖+‖y‖`.")
    print(f"")
    print(f"Analog of `norm_bch_septic_term_diff_le` (session 28) at one degree higher;")
    print(f"the deg-8 BCH coefficient is Lipschitz in its first argument.")
    print(f"")
    print(f"With `z = (a'+b) + W` and `‖W‖ = O(s²)`, gives an O(s⁹·‖W‖) bound on")
    print(f"`‖C₈(z, y) − C₈(a'+b, y)‖`. Completes the `bch_octic_term` infrastructure")
    print(f"quartet (def + norm bound + vanishing + Lipschitz) for stepping stone 1.")
    print(f"")
    print(f"The proof uses a uniform per-i bound `({UNIFORM_MAX_NUM}/{LCM}) · 8 · M⁷ · ‖z−x‖`,")
    print(f"giving `Σ ≤ {N_WORDS}·{UNIFORM_MAX_NUM}·8/{LCM} = {N_WORDS*UNIFORM_MAX_NUM*8}/{LCM} = {sp.Rational(N_WORDS*UNIFORM_MAX_NUM*8, LCM)} ≤ 8`. -/")
    print("theorem norm_bch_octic_term_diff_le (z x y : 𝔸) :")
    print("    ‖bch_octic_term 𝕂 z y - bch_octic_term 𝕂 x y‖ ≤")
    print("      8 * (‖z‖ + ‖x‖ + ‖y‖) ^ 7 * ‖z - x‖ := by")
    print("  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM_def")
    print("  have hM_nn : 0 ≤ M := by positivity")
    print("  have hz_le : ‖z‖ ≤ M := by")
    print("    show ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg x, norm_nonneg y]")
    print("  have hx_le : ‖x‖ ≤ M := by")
    print("    show ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg y]")
    print("  have hy_le : ‖y‖ ≤ M := by")
    print("    show ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖; linarith [norm_nonneg z, norm_nonneg x]")
    print("  have hM7_nn : 0 ≤ M^7 := pow_nonneg hM_nn 7")
    print("  have hzx_nn : 0 ≤ ‖z - x‖ := norm_nonneg _")
    print("  rw [bch_octic_term_eq_sum, bch_octic_term_eq_sum, ← Finset.sum_sub_distrib]")
    print(f"  calc ‖∑ i : Fin {N_WORDS}, (bchOcticTerm (𝕂 := 𝕂) z y i - bchOcticTerm (𝕂 := 𝕂) x y i)‖")
    print(f"      ≤ ∑ i : Fin {N_WORDS}, ‖bchOcticTerm (𝕂 := 𝕂) z y i - bchOcticTerm (𝕂 := 𝕂) x y i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin {N_WORDS}, ({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 8 * M^7 * ‖z - x‖ :=")
    print(f"        Finset.sum_le_sum (fun i _ => bchOcticTerm_diff_norm_le (𝕂 := 𝕂) z x y M hz_le hx_le hy_le hM_nn i)")
    print(f"    _ = {N_WORDS} * (({UNIFORM_MAX_NUM} / {LCM} : ℝ) * 8 * M^7 * ‖z - x‖) := by")
    print(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ ≤ 8 * M^7 * ‖z - x‖ := by nlinarith [hM7_nn, hzx_nn]")


if __name__ == "__main__":
    main()
