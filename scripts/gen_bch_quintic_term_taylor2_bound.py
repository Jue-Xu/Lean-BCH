#!/usr/bin/env python3
"""
Generate Lean code for the norm bound on bch_quintic_term_taylor2_remainder:

    ‖bch_quintic_term_taylor2_remainder(x, V, y)‖ ≤ K · M³ · ‖V‖²

where M = ‖x‖ + ‖V‖ + ‖y‖.

Approach: split into per-k (V-count) sub-pieces, then triangle inequality.
* k=2 sub-piece: 70 terms, max|num|=24. Direct bound by `(70·24/720) · ‖V‖² · M³`.
* k=3 sub-piece: 30 terms, max|num|=24. Lifted via `‖V‖ ≤ M`: `(30·24/720) · ‖V‖³ · M² ≤ ‖V‖² · M³ · `.
* k=4 sub-piece:  5 terms, max|num|= 6. Similar lift.

Uniform per-i bound `(max_abs/720) · ‖V‖² · M³` works for ALL k ≥ 2:
each word with k V's has product bound `‖V‖^k · M^(5-k)` ≤ `‖V‖² · M³` since
`‖V‖^(k-2) ≤ M^(k-2)` (auto from `‖V‖ ≤ M`).

In Lean, we bound exactly 2 V-positions by Vn=‖V‖, and the remaining
(k-2) V-positions and all (5-k) non-V positions by M = ‖x‖+‖V‖+‖y‖. The
product is then literally `Vn² · M³` — same expression for k=2,3,4.
"""

import sympy as sp
from collections import defaultdict
from itertools import combinations
import sys


# ---- BCH computation ----

def ncpoly_zero(): return defaultdict(lambda: sp.Integer(0))
def ncpoly_from_scalar(c):
    r = ncpoly_zero(); c = sp.sympify(c)
    if c != 0: r[()] = c
    return r
def ncpoly_a(): r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r
def ncpoly_b(): r = ncpoly_zero(); r[(1,)] = sp.Integer(1); return r
def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items(): r[w] = r[w] + c
    for w, c in q.items(): r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0: return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0), {w: c * v for w, v in p.items()})
def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_truncate(p, mx):
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in p.items() if len(w) <= mx})
def ncpoly_exp(x, mx):
    r = ncpoly_from_scalar(1); xp = ncpoly_from_scalar(1)
    for k in range(1, mx+1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), mx)
        r = ncpoly_add(r, ncpoly_scale(xp, sp.Rational(1, sp.factorial(k))))
    return r
def ncpoly_log_one_plus(x, mx):
    r = ncpoly_zero(); xp = ncpoly_from_scalar(1)
    for k in range(1, mx+1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), mx)
        sign = sp.Integer(1) if k%2==1 else sp.Integer(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign/sp.Integer(k)))
    return r
def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in p.items() if len(w) == k})
def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


# ---- Compute per-k structure ----

def substitute_at(w, positions, atom):
    result = list(w)
    for i in positions: result[i] = atom
    return tuple(result)

def word_in_xVy(w_in_xy):
    return tuple(0 if a == 0 else 2 for a in w_in_xy)

def compute_per_k():
    a, b = ncpoly_a(), ncpoly_b()
    bch_5 = extract_degree(bch_series(a, b, 5), 5)
    per_k = {k: defaultdict(lambda: sp.Integer(0)) for k in [2, 3, 4]}
    for w, c in bch_5.items():
        if c == 0: continue
        w_xVy = word_in_xVy(w)
        x_positions = [i for i, atom in enumerate(w) if atom == 0]
        for k in range(2, len(x_positions) + 1):
            for S in combinations(x_positions, k):
                new_w = substitute_at(w_xVy, S, 1)
                per_k[k][new_w] = per_k[k][new_w] + c
    return per_k


# ---- Lean emission ----

def word_lean(w):
    """Map atom 0(x)→'x', 1(V)→'V', 2(y)→'y'."""
    return ' * '.join(['x', 'V', 'y'][a] for a in w)


def word_letter_at(w, i):
    return ['x', 'V', 'y'][w[i]]


def hyp_for_letter(letter, kind):
    """Letter is 'x', 'V', or 'y'; kind is 'M' or 'V'.

    Returns the hypothesis name for the bound on that letter in the proof:
    * If letter is 'x' or 'y', the bound is always M (returns 'hx_M' or 'hy_M').
    * If letter is 'V' and kind is 'V', the bound is Vn (returns 'hV_Vn').
    * If letter is 'V' and kind is 'M', the bound is M (returns 'hV_M').
    """
    if letter == 'x':
        return 'hx_M'
    if letter == 'y':
        return 'hy_M'
    if letter == 'V':
        return 'hV_Vn' if kind == 'V' else 'hV_M'
    raise ValueError(f"Unknown letter {letter}")


def emit_perk_def(k, items, lcm, helper_name):
    """Emit the per-k DEF."""
    N = len(items)
    def_name = f"bch_quintic_term_taylor2_remainder_{k}V"
    cap_name = ''.join(p[:1].upper() + p[1:] for p in def_name.split("_"))

    print(f"/-- The k={k} sub-piece of `bch_quintic_term_taylor2_remainder`: sum")
    print(f"over each bch_quintic_term word of placing V at exactly {k} positions")
    print(f"among the word's x-positions. {N} terms in {{x, V, y}}. -/")
    print(f"noncomputable def {def_name} (𝕂 : Type*) [RCLike 𝕂]")
    print(f"    {{𝔸 : Type*}} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (x V y : 𝔸) : 𝔸 :=")
    first = True
    for w, c in sorted(items, key=lambda kv: kv[0]):
        n = int(sp.nsimplify(c * lcm))
        prefix = "    " if first else "  + "
        print(f"{prefix}({n} / {lcm} : 𝕂) • ({word_lean(w)})")
        first = False
    print()


def emit_split_identity(per_k, lcm):
    """Emit the additive identity decomposition."""
    print("set_option maxHeartbeats 32000000 in")
    print("omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print("/-- **Per-k split identity**: the second-order Taylor remainder of")
    print("bch_quintic_term decomposes additively into k=2, k=3, k=4 sub-pieces. -/")
    print("theorem bch_quintic_term_taylor2_remainder_split (x V y : 𝔸) :")
    print("    bch_quintic_term_taylor2_remainder 𝕂 x V y =")
    print("      bch_quintic_term_taylor2_remainder_2V 𝕂 x V y +")
    print("      bch_quintic_term_taylor2_remainder_3V 𝕂 x V y +")
    print("      bch_quintic_term_taylor2_remainder_4V 𝕂 x V y := by")
    print("  unfold bch_quintic_term_taylor2_remainder")
    print("    bch_quintic_term_taylor2_remainder_2V")
    print("    bch_quintic_term_taylor2_remainder_3V")
    print("    bch_quintic_term_taylor2_remainder_4V")
    print("  match_scalars <;> ring")
    print()


def emit_perk_term_family(k, items, lcm):
    """Emit the Fin N-indexed Term family for the k-V piece."""
    N = len(items)
    def_name = f"bch_quintic_term_taylor2_remainder_{k}V"
    cap = ''.join(p[:1].upper() + p[1:] for p in def_name.split("_"))
    prefix = cap  # PascalCase prefix

    print(f"-- Per-Nat-index family for `{def_name}`.")
    print(f"set_option maxHeartbeats 800000 in")
    print(f"private noncomputable def {prefix}TermN (x V y : 𝔸) : Nat → 𝔸")
    for idx, (w, c) in enumerate(items):
        n = int(sp.nsimplify(c * lcm))
        print(f"  | {idx} => ({n} / {lcm} : 𝕂) • ({word_lean(w)})")
    print(f"  | _ => 0")
    print()

    print(f"/-- `Fin {N}`-indexed wrapper for `{prefix}TermN`. -/")
    print(f"private noncomputable def {prefix}Term (x V y : 𝔸) (i : Fin {N}) : 𝔸 :=")
    print(f"  {prefix}TermN (𝕂 := 𝕂) x V y i.val")
    print()

    print(f"-- The explicit `{def_name}` def equals the `Finset.sum` form.")
    print(f"set_option maxHeartbeats 16000000 in")
    print(f"set_option maxRecDepth 2000 in")
    print(f"omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print(f"private theorem {def_name}_eq_sum (x V y : 𝔸) :")
    print(f"    {def_name} 𝕂 x V y = ∑ i : Fin {N}, {prefix}Term (𝕂 := 𝕂) x V y i := by")
    print(f"  unfold {def_name} {prefix}Term")
    print(f"  rw [Fin.sum_univ_eq_sum_range (fun k => {prefix}TermN (𝕂 := 𝕂) x V y k)]")
    print(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero,")
    print(f"    {prefix}TermN, zero_add]")
    print()

    # Per-index uniform bound
    max_abs = max(abs(int(sp.nsimplify(c * lcm))) for _, c in items)
    print(f"-- Per-index uniform bound: ‖{prefix}Term x V y i‖ ≤ ({max_abs}/{lcm}) · Vn² · M³.")
    print(f"set_option maxHeartbeats 32000000 in")
    print(f"omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print(f"private lemma {prefix}Term_norm_le (x V y : 𝔸) (M Vn : ℝ)")
    print(f"    (hx_M : ‖x‖ ≤ M) (hV_Vn : ‖V‖ ≤ Vn) (hy_M : ‖y‖ ≤ M)")
    print(f"    (hV_M : ‖V‖ ≤ M)")
    print(f"    (hM_nn : 0 ≤ M) (hVn_nn : 0 ≤ Vn) :")
    print(f"    ∀ i : Fin {N}, ‖{prefix}Term (𝕂 := 𝕂) x V y i‖ "
          f"≤ ({max_abs} / {lcm} : ℝ) * Vn^2 * M^3 := fun i =>")
    print(f"  match i with")
    for idx, (w, c) in enumerate(items):
        n = int(sp.nsimplify(c * lcm))
        # V-positions: pick first 2 as Vn-bounded, rest as M-bounded
        V_positions = [i for i, a in enumerate(w) if a == 1]
        # Choose b_i for each letter: 2 V's get Vn, rest (including extra V's) get M
        chosen_Vn_positions = set(V_positions[:2])  # first 2 V-positions bounded by Vn
        bounds_letter = []
        for pos in range(5):
            letter = word_letter_at(w, pos)
            if letter == 'V' and pos in chosen_Vn_positions:
                bounds_letter.append(('V', 'V'))  # ‖V‖ ≤ Vn
            elif letter == 'V':
                bounds_letter.append(('V', 'M'))  # ‖V‖ ≤ M (extra V-positions)
            else:
                bounds_letter.append((letter, 'M'))  # ‖x or y‖ ≤ M
        # Build the bound list: corresponds to b_i values (Vn for first 2 V's, M for rest)
        bounds_str_list = []
        hyp_list = []
        for letter, kind in bounds_letter:
            if kind == 'V':
                bounds_str_list.append('Vn')
                hyp_list.append(hyp_for_letter(letter, kind))
            else:
                bounds_str_list.append('M')
                hyp_list.append(hyp_for_letter(letter, kind))
        bounds_str = ' * '.join(bounds_str_list)
        # The product `Vn * Vn * M * M * M` (or permutation) equals `Vn^2 * M^3` by ring.

        word_str = word_lean(w)
        word_args = ' '.join(['x', 'V', 'y'][a] for a in w)
        print(f"  | ⟨{idx}, _⟩ =>")
        print(f"    show ‖({n} / {lcm} : 𝕂) • ({word_str})‖ ≤ "
              f"({max_abs} / {lcm} : ℝ) * Vn^2 * M^3 from by")
        print(f"      calc ‖({n} / {lcm} : 𝕂) • ({word_str})‖")
        print(f"          ≤ ‖({n} / {lcm} : 𝕂)‖ * ‖{word_str}‖ := norm_smul_le _ _")
        print(f"        _ ≤ ({max_abs} / {lcm} : ℝ) * ‖{word_str}‖ := by")
        print(f"            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)")
        print(f"            rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num")
        print(f"        _ ≤ ({max_abs} / {lcm} : ℝ) * ({' * '.join('‖' + w + '‖' for w in word_args.split())}) := by")
        print(f"            apply mul_le_mul_of_nonneg_left (norm_5prod_le _ _ _ _ _) (by positivity)")
        print(f"        _ ≤ ({max_abs} / {lcm} : ℝ) * ({bounds_str}) := by gcongr")
        print(f"        _ = ({max_abs} / {lcm} : ℝ) * Vn^2 * M^3 := by ring")
    print(f"  | ⟨_ + {N}, h⟩ => absurd h (by omega)")
    print()


def emit_perk_bound_theorem(k, items, lcm):
    """Emit the per-k bound theorem (‖_kV‖ ≤ K · Vn² · M³)."""
    N = len(items)
    def_name = f"bch_quintic_term_taylor2_remainder_{k}V"
    cap = ''.join(p[:1].upper() + p[1:] for p in def_name.split("_"))
    prefix = cap
    max_abs = max(abs(int(sp.nsimplify(c * lcm))) for _, c in items)
    coef_num = N * max_abs

    print(f"set_option maxHeartbeats 800000 in")
    print(f"omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print(f"/-- **Per-k norm bound for `{def_name}`**:")
    print(f"`‖{def_name}(x, V, y)‖ ≤ ({coef_num}/{lcm}) · Vn² · M³` for `Vn = ‖V‖` and")
    print(f"`M ≥ ‖x‖, ‖V‖, ‖y‖`. -/")
    print(f"theorem norm_{def_name}_le (x V y : 𝔸) (M Vn : ℝ)")
    print(f"    (hx_M : ‖x‖ ≤ M) (hV_Vn : ‖V‖ ≤ Vn) (hy_M : ‖y‖ ≤ M)")
    print(f"    (hV_M : ‖V‖ ≤ M)")
    print(f"    (hM_nn : 0 ≤ M) (hVn_nn : 0 ≤ Vn) :")
    print(f"    ‖{def_name} 𝕂 x V y‖ ≤ ({coef_num} / {lcm} : ℝ) * Vn^2 * M^3 := by")
    print(f"  rw [{def_name}_eq_sum]")
    print(f"  calc ‖∑ i : Fin {N}, {prefix}Term (𝕂 := 𝕂) x V y i‖")
    print(f"      ≤ ∑ i : Fin {N}, ‖{prefix}Term (𝕂 := 𝕂) x V y i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin {N}, ({max_abs} / {lcm} : ℝ) * Vn^2 * M^3 :=")
    print(f"        Finset.sum_le_sum (fun i _ => "
          f"{prefix}Term_norm_le (𝕂 := 𝕂) x V y M Vn hx_M hV_Vn hy_M hV_M hM_nn hVn_nn i)")
    print(f"    _ = {N} * (({max_abs} / {lcm} : ℝ) * Vn^2 * M^3) := by")
    print(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ = ({coef_num} / {lcm} : ℝ) * Vn^2 * M^3 := by ring")
    print()


def emit_combined_bound(per_k, lcm):
    """Emit the combined bound theorem for `bch_quintic_term_taylor2_remainder`."""
    K_total = 0
    for k in [2, 3, 4]:
        items = sorted([(w, c) for w, c in per_k[k].items() if c != 0])
        N = len(items)
        max_abs = max(abs(int(sp.nsimplify(c * lcm))) for _, c in items)
        K_total += N * max_abs

    print(f"set_option maxHeartbeats 800000 in")
    print(f"omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    print(f"/-- **Norm bound for `bch_quintic_term_taylor2_remainder`**:")
    print(f"`‖bch_quintic_term_taylor2_remainder(x, V, y)‖ ≤ ({K_total}/{lcm}) · M³ · ‖V‖²`")
    print(f"where `M = ‖x‖ + ‖V‖ + ‖y‖`.")
    print()
    print(f"Combines the per-k=2, k=3, k=4 sub-piece bounds via triangle inequality.")
    print(f"Constants: k=2 contributes 1680/720, k=3 contributes 720/720, k=4 contributes")
    print(f"30/720; total = {K_total}/{lcm}. -/")
    print(f"theorem norm_bch_quintic_term_taylor2_remainder_le (x V y : 𝔸) :")
    print(f"    ‖bch_quintic_term_taylor2_remainder 𝕂 x V y‖ ≤")
    print(f"      ({K_total} / {lcm} : ℝ) * (‖x‖ + ‖V‖ + ‖y‖)^3 * ‖V‖^2 := by")
    print(f"  set M := ‖x‖ + ‖V‖ + ‖y‖ with hM_def")
    print(f"  set Vn := ‖V‖ with hVn_def")
    print(f"  have hM_nn : 0 ≤ M := by positivity")
    print(f"  have hVn_nn : 0 ≤ Vn := norm_nonneg _")
    print(f"  have hx_M : ‖x‖ ≤ M := by")
    print(f"    rw [hM_def]; linarith [norm_nonneg V, norm_nonneg y]")
    print(f"  have hV_M : ‖V‖ ≤ M := by")
    print(f"    rw [hM_def]; linarith [norm_nonneg x, norm_nonneg y]")
    print(f"  have hy_M : ‖y‖ ≤ M := by")
    print(f"    rw [hM_def]; linarith [norm_nonneg x, norm_nonneg V]")
    print(f"  have hV_Vn : ‖V‖ ≤ Vn := le_refl _")
    print(f"  rw [bch_quintic_term_taylor2_remainder_split]")
    # Per-k bound applications
    for k in [2, 3, 4]:
        items = sorted([(w, c) for w, c in per_k[k].items() if c != 0])
        N = len(items)
        max_abs = max(abs(int(sp.nsimplify(c * lcm))) for _, c in items)
        kK = N * max_abs
        print(f"  have h{k} := norm_bch_quintic_term_taylor2_remainder_{k}V_le "
              f"(𝕂 := 𝕂) x V y M Vn hx_M hV_Vn hy_M hV_M hM_nn hVn_nn")
        print(f"  -- h{k} : ‖_kV‖ ≤ ({kK}/{lcm}) * Vn^2 * M^3")
    print(f"  calc ‖bch_quintic_term_taylor2_remainder_2V 𝕂 x V y +")
    print(f"         bch_quintic_term_taylor2_remainder_3V 𝕂 x V y +")
    print(f"         bch_quintic_term_taylor2_remainder_4V 𝕂 x V y‖")
    print(f"      ≤ ‖bch_quintic_term_taylor2_remainder_2V 𝕂 x V y +")
    print(f"         bch_quintic_term_taylor2_remainder_3V 𝕂 x V y‖ +")
    print(f"        ‖bch_quintic_term_taylor2_remainder_4V 𝕂 x V y‖ := norm_add_le _ _")
    print(f"    _ ≤ ‖bch_quintic_term_taylor2_remainder_2V 𝕂 x V y‖ +")
    print(f"        ‖bch_quintic_term_taylor2_remainder_3V 𝕂 x V y‖ +")
    print(f"        ‖bch_quintic_term_taylor2_remainder_4V 𝕂 x V y‖ := by")
    print(f"        linarith [norm_add_le (bch_quintic_term_taylor2_remainder_2V 𝕂 x V y) "
          f"(bch_quintic_term_taylor2_remainder_3V 𝕂 x V y)]")
    print(f"    _ ≤ _ := by linarith [h2, h3, h4]")


def main():
    per_k = compute_per_k()
    LCM = 720

    for k in [2, 3, 4]:
        items = sorted([(w, c) for w, c in per_k[k].items() if c != 0])
        emit_perk_def(k, items, LCM, helper_name=None)

    emit_split_identity(per_k, LCM)

    for k in [2, 3, 4]:
        items = sorted([(w, c) for w, c in per_k[k].items() if c != 0])
        emit_perk_term_family(k, items, LCM)
        emit_perk_bound_theorem(k, items, LCM)

    emit_combined_bound(per_k, LCM)


if __name__ == "__main__":
    main()
