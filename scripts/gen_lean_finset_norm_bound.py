#!/usr/bin/env python3
"""
Generate Lean code to replace `norm_C5_LinResidual_polynomial_le` axiom.

**Per-degree split strategy** for faster compilation:
  - Separate `linResTermN`, `linResBoundN` functions for N = 7, 8, 9.
  - Per-degree identity / per-term bound / sum bound, each over smaller Fin.
  - Combine in main theorem via triangle inequality.
"""

import sys
sys.path.insert(0, '/Users/jue/Documents/Claude/Projects/Lean-BCH/scripts')
from compute_C5_diff_LinResidual import LinResidual

terms_by_deg = {7: [], 8: [], 9: []}
for word, coef in LinResidual.items():
    deg = len(word)
    terms_by_deg[deg].append((word, coef))

for deg in [7, 8, 9]:
    terms_by_deg[deg].sort()

COMMON_DENOM = {7: 92160, 8: 184320, 9: 368640}

# For each degree, build list of (word, num, denom).
terms_by_deg_int = {}
for deg in [7, 8, 9]:
    cd = COMMON_DENOM[deg]
    lst = []
    for word, coef in terms_by_deg[deg]:
        num_over_cd = coef * cd
        assert num_over_cd.q == 1
        num_int = int(num_over_cd)
        lst.append((word, num_int, cd))
    terms_by_deg_int[deg] = lst

counts = {d: len(terms_by_deg_int[d]) for d in [7, 8, 9]}
print(f"-- Counts: deg-7={counts[7]}, deg-8={counts[8]}, deg-9={counts[9]}", file=sys.stderr)


def word_to_lean(word):
    return ' * '.join(word)


lines = []

# ============================================================
# 1. Per-degree helpers (3 lemmas, same as before)
# ============================================================
for deg in [7, 8, 9]:
    letters_decl = ' '.join(f"l{i}" for i in range(1, deg + 1))
    letters_prod = ' * '.join(f"l{i}" for i in range(1, deg + 1))
    letters_norms = ' * '.join(f"‖l{i}‖" for i in range(1, deg + 1))
    letters_s = ' * '.join(['s'] * deg)
    hyps_decl = ' '.join(f"(h{i} : ‖l{i}‖ ≤ s)" for i in range(1, deg + 1))
    norm_Nprod_args = ' '.join(['_'] * deg)

    lines.append(f"omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in")
    lines.append(f"/-- **Helper (deg-{deg})**: `‖c • (l₁·…·l{deg})‖ ≤ cb · s^{deg}` if `‖c‖ ≤ cb` and each `‖lᵢ‖ ≤ s`. -/")
    lines.append(f"private lemma deg{deg}_smul_word_le")
    lines.append(f"    (c : 𝕂) (cb : ℝ) (hc : ‖c‖ ≤ cb)")
    lines.append(f"    ({letters_decl} : 𝔸) (s : ℝ)")
    lines.append(f"    {hyps_decl}")
    lines.append(f"    (hcb : 0 ≤ cb) (hs : 0 ≤ s) :")
    lines.append(f"    ‖c • ({letters_prod})‖ ≤ cb * s ^ {deg} := by")
    lines.append(f"  calc ‖c • ({letters_prod})‖")
    lines.append(f"      ≤ ‖c‖ * ‖{letters_prod}‖ := norm_smul_le _ _")
    lines.append(f"    _ ≤ cb * ‖{letters_prod}‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)")
    lines.append(f"    _ ≤ cb * ({letters_norms}) :=")
    lines.append(f"        mul_le_mul_of_nonneg_left (norm_{deg}prod_le {norm_Nprod_args}) hcb")
    lines.append(f"    _ ≤ cb * ({letters_s}) := by")
    lines.append(f"        refine mul_le_mul_of_nonneg_left ?_ hcb; gcongr")
    lines.append(f"    _ = cb * s ^ {deg} := by ring")
    lines.append("")

# ============================================================
# 2. Per-degree `linResTermN` definitions
# ============================================================
for deg in [7, 8, 9]:
    n = counts[deg]
    lines.append(f"/-- Per-index family: the {n} deg-{deg} terms of `C5_LinResidual_polynomial`. -/")
    lines.append(f"private noncomputable def linResTerm{deg} (a b : 𝔸) : Fin {n} → 𝔸")
    for idx, (word, num, denom) in enumerate(terms_by_deg_int[deg]):
        word_str = word_to_lean(word)
        lines.append(f"  | ⟨{idx}, _⟩ => ({num} / {denom} : 𝕂) • ({word_str})")
    lines.append(f"  | ⟨_ + {n}, h⟩ => absurd h (by omega)")
    lines.append("")

# ============================================================
# 3. Per-degree `linResBoundN` definitions
# ============================================================
for deg in [7, 8, 9]:
    n = counts[deg]
    lines.append(f"/-- Per-index upper bound on `‖linResTerm{deg} i‖`. -/")
    lines.append(f"private noncomputable def linResBound{deg} (s : ℝ) : Fin {n} → ℝ")
    for idx, (word, num, denom) in enumerate(terms_by_deg_int[deg]):
        abs_num = abs(num)
        lines.append(f"  | ⟨{idx}, _⟩ => ({abs_num} / {denom} : ℝ) * s ^ {deg}")
    lines.append(f"  | ⟨_ + {n}, h⟩ => absurd h (by omega)")
    lines.append("")

# ============================================================
# 4. Per-degree polynomial parts
# ============================================================
for deg in [7, 8, 9]:
    n = counts[deg]
    lines.append(f"/-- Sum form of the deg-{deg} part of `C5_LinResidual_polynomial`. -/")
    lines.append(f"private noncomputable def C5_LinResidual_deg{deg} (a b : 𝔸) : 𝔸 :=")
    parts = []
    for word, num, denom in terms_by_deg_int[deg]:
        word_str = word_to_lean(word)
        parts.append(f"  ({num} / {denom} : 𝕂) • ({word_str})")
    lines.append('  ' + ' +\n  '.join(p.lstrip() for p in parts))
    lines.append("")

# ============================================================
# 5. Algebraic identity: C5_LinResidual_polynomial = deg7 + deg8 + deg9
# ============================================================
# Note: use Lean `--` comments instead of doc comments on `set_option ... in` declarations.
# Doc-comment + set_option_in + lemma breaks Lean's doc-attachment parser.
lines.append("-- Decomposition of the polynomial into its per-degree parts.")
lines.append("set_option maxHeartbeats 32000000 in")
lines.append("private lemma C5_LinResidual_polynomial_eq_parts (a b : 𝔸) :")
lines.append("    C5_LinResidual_polynomial 𝕂 a b =")
lines.append("      C5_LinResidual_deg7 (𝕂 := 𝕂) a b + C5_LinResidual_deg8 (𝕂 := 𝕂) a b + C5_LinResidual_deg9 (𝕂 := 𝕂) a b := by")
lines.append("  unfold C5_LinResidual_polynomial C5_LinResidual_deg7 C5_LinResidual_deg8 C5_LinResidual_deg9")
lines.append("  abel")
lines.append("")

# ============================================================
# 6. Per-degree identity: deg{N} part = ∑ i, linResTerm{N} i
# ============================================================
for deg in [7, 8, 9]:
    n = counts[deg]
    hbs = max(8_000_000, n * 200_000)  # Heartbeats scale with n.
    lines.append(f"-- The deg-{deg} part expressed as a `Finset.sum`.")
    lines.append(f"set_option maxHeartbeats {hbs} in")
    lines.append(f"private lemma C5_LinResidual_deg{deg}_eq_sum (a b : 𝔸) :")
    lines.append(f"    C5_LinResidual_deg{deg} (𝕂 := 𝕂) a b = ∑ i : Fin {n}, linResTerm{deg} (𝕂 := 𝕂) a b i := by")
    lines.append(f"  unfold C5_LinResidual_deg{deg}")
    lines.append(f"  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, linResTerm{deg}, add_zero]")
    lines.append(f"  abel")
    lines.append("")

# ============================================================
# 7. Per-degree per-term bound: ∀ i, ‖linResTerm{N} i‖ ≤ linResBound{N} i
# ============================================================
for deg in [7, 8, 9]:
    n = counts[deg]
    hbs = max(16_000_000, n * 200_000)
    lines.append(f"-- Per-index norm bound for `linResTerm{deg}`.")
    lines.append(f"set_option maxHeartbeats {hbs} in")
    lines.append(f"private lemma linResTerm{deg}_norm_le")
    lines.append(f"    (a b : 𝔸) (s : ℝ) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
    lines.append(f"    ∀ i : Fin {n}, ‖linResTerm{deg} (𝕂 := 𝕂) a b i‖ ≤ linResBound{deg} s i := fun i =>")
    lines.append(f"  match i with")

    for idx, (word, num, denom) in enumerate(terms_by_deg_int[deg]):
        abs_num = abs(num)
        letter_hyps = ' '.join(['ha' if c == 'a' else 'hb' for c in word])
        letter_args = ' '.join(word)
        coef_expr = f"({num} / {denom} : 𝕂)"
        bound_expr = f"({abs_num} / {denom} : ℝ)"
        lines.append(f"  | ⟨{idx}, _⟩ =>")
        lines.append(f"    show ‖{coef_expr} • ({word_to_lean(word)})‖ ≤ {bound_expr} * s ^ {deg} from")
        lines.append(f"      deg{deg}_smul_word_le {coef_expr} {bound_expr}")
        lines.append(f"        (by rw [norm_div]; simp [RCLike.norm_ofNat])")
        lines.append(f"        {letter_args} s {letter_hyps} (by positivity) hs")
    lines.append(f"  | ⟨_ + {n}, h⟩ => absurd h (by omega)")
    lines.append("")

# ============================================================
# 8. Per-degree sum-of-bounds
# ============================================================
sum_abs_by_deg = {}
for deg in [7, 8, 9]:
    total = sum(abs(num) for _, num, _ in terms_by_deg_int[deg])
    sum_abs_by_deg[deg] = total
    print(f"-- deg-{deg}: Σ|num| = {total}, denom = {COMMON_DENOM[deg]}", file=sys.stderr)

for deg in [7, 8, 9]:
    n = counts[deg]
    total = sum_abs_by_deg[deg]
    cd = COMMON_DENOM[deg]
    hbs = max(8_000_000, n * 200_000)
    # For sum bound, use uniform per-i bound (max coefficient) + Finset.sum_const.
    # This gives a looser but easier-to-prove bound: ≤ N_terms · K_max / cd · s^N.
    max_coef = max(abs(num) for _, num, _ in terms_by_deg_int[deg])
    n_terms_max_bound = n * max_coef
    lines.append(f"-- Sum of deg-{deg} bounds: ∑ ≤ {n}·{max_coef}/{cd} · s^{deg} = {n_terms_max_bound}/{cd} · s^{deg}.")
    lines.append(f"-- Uses uniform per-i bound (max coefficient) + Finset.sum_const.")
    lines.append(f"set_option maxHeartbeats {hbs} in")
    lines.append(f"private lemma sum_linResBound{deg}_le (s : ℝ) (hs : 0 ≤ s) :")
    lines.append(f"    ∑ i : Fin {n}, linResBound{deg} s i ≤ ({n_terms_max_bound} / {cd} : ℝ) * s ^ {deg} := by")
    lines.append(f"  have hs_pow_nn : 0 ≤ s ^ {deg} := pow_nonneg hs {deg}")
    lines.append(f"  have h_unif : ∀ i : Fin {n}, linResBound{deg} s i ≤ ({max_coef} / {cd} : ℝ) * s ^ {deg} := fun i =>")
    lines.append(f"    match i with")
    for idx, (word, num, denom) in enumerate(terms_by_deg_int[deg]):
        abs_num = abs(num)
        lines.append(f"    | ⟨{idx}, _⟩ => by")
        lines.append(f"      show ({abs_num} / {cd} : ℝ) * s ^ {deg} ≤ ({max_coef} / {cd} : ℝ) * s ^ {deg}")
        lines.append(f"      nlinarith [hs_pow_nn]")
    lines.append(f"    | ⟨_ + {n}, h⟩ => absurd h (by omega)")
    lines.append(f"  calc ∑ i : Fin {n}, linResBound{deg} s i")
    lines.append(f"      ≤ ∑ _i : Fin {n}, ({max_coef} / {cd} : ℝ) * s ^ {deg} := Finset.sum_le_sum (fun i _ => h_unif i)")
    lines.append(f"    _ = {n} * (({max_coef} / {cd} : ℝ) * s ^ {deg}) := by")
    lines.append(f"        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]")
    lines.append(f"        ring")
    lines.append(f"    _ = ({n_terms_max_bound} / {cd} : ℝ) * s ^ {deg} := by ring")
    lines.append("")

# ============================================================
# 9. Main theorem (replaces the axiom)
# ============================================================
# Compute the looser bounds: N_terms · K_max / cd.
max_coef = {deg: max(abs(num) for _, num, _ in terms_by_deg_int[deg]) for deg in [7, 8, 9]}
loose_bound_num = {deg: counts[deg] * max_coef[deg] for deg in [7, 8, 9]}
denom7 = COMMON_DENOM[7]
denom8 = COMMON_DENOM[8]
denom9 = COMMON_DENOM[9]
b7 = loose_bound_num[7]
b8 = loose_bound_num[8]
b9 = loose_bound_num[9]

lines.append("-- **The polynomial bound** (replaces the previous private axiom).")
lines.append("set_option maxHeartbeats 16000000 in")
lines.append("private theorem norm_C5_LinResidual_polynomial_le")
lines.append("    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :")
lines.append("    ‖C5_LinResidual_polynomial 𝕂 a b‖ ≤ 1 * (‖a‖ + ‖b‖) ^ 7 := by")
lines.append("  set s := ‖a‖ + ‖b‖ with hs_def")
lines.append("  have hs_nn : 0 ≤ s := by positivity")
lines.append("  have ha : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
lines.append("  have hb : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
lines.append("  have hs_lt : s < 1 / 4 := hab")
lines.append("  have hs7_nn : 0 ≤ s ^ 7 := pow_nonneg hs_nn 7")
lines.append("  -- Per-degree norm bounds.")
lines.append(f"  have hdeg7 : ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b‖ ≤ ({b7} / {denom7} : ℝ) * s ^ 7 := by")
lines.append("    rw [C5_LinResidual_deg7_eq_sum]")
lines.append("    calc ‖∑ i, linResTerm7 (𝕂 := 𝕂) a b i‖")
lines.append("        ≤ ∑ i, ‖linResTerm7 (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
lines.append("      _ ≤ ∑ i, linResBound7 s i :=")
lines.append("          Finset.sum_le_sum (fun i _ => linResTerm7_norm_le a b s ha hb hs_nn i)")
lines.append(f"      _ ≤ ({b7} / {denom7} : ℝ) * s ^ 7 := sum_linResBound7_le s hs_nn")
lines.append(f"  have hdeg8 : ‖C5_LinResidual_deg8 (𝕂 := 𝕂) a b‖ ≤ ({b8} / {denom8} : ℝ) * s ^ 8 := by")
lines.append("    rw [C5_LinResidual_deg8_eq_sum]")
lines.append("    calc ‖∑ i, linResTerm8 (𝕂 := 𝕂) a b i‖")
lines.append("        ≤ ∑ i, ‖linResTerm8 (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
lines.append("      _ ≤ ∑ i, linResBound8 s i :=")
lines.append("          Finset.sum_le_sum (fun i _ => linResTerm8_norm_le a b s ha hb hs_nn i)")
lines.append(f"      _ ≤ ({b8} / {denom8} : ℝ) * s ^ 8 := sum_linResBound8_le s hs_nn")
lines.append(f"  have hdeg9 : ‖C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖ ≤ ({b9} / {denom9} : ℝ) * s ^ 9 := by")
lines.append("    rw [C5_LinResidual_deg9_eq_sum]")
lines.append("    calc ‖∑ i, linResTerm9 (𝕂 := 𝕂) a b i‖")
lines.append("        ≤ ∑ i, ‖linResTerm9 (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
lines.append("      _ ≤ ∑ i, linResBound9 s i :=")
lines.append("          Finset.sum_le_sum (fun i _ => linResTerm9_norm_le a b s ha hb hs_nn i)")
lines.append(f"      _ ≤ ({b9} / {denom9} : ℝ) * s ^ 9 := sum_linResBound9_le s hs_nn")
# Don't keep separate deg7/deg8/deg9 sum vars (overwritten above by uniform bounds).
deg7_sum = b7
deg8_sum = b8
deg9_sum = b9
lines.append("  -- Polynomial degrees relative to s^7 (for s ≤ 1/4).")
lines.append("  have hs8 : s ^ 8 ≤ s ^ 7 * (1/4) := by")
lines.append("    have heq : s^8 = s^7 * s := by ring")
lines.append("    rw [heq]; nlinarith [hs7_nn]")
lines.append("  have hs9 : s ^ 9 ≤ s ^ 7 * (1/16) := by")
lines.append("    have heq : s^9 = s^7 * (s*s) := by ring")
lines.append("    rw [heq]; nlinarith [hs7_nn, sq_nonneg s]")
lines.append("  -- Triangle inequality on the per-degree decomposition.")
lines.append("  rw [C5_LinResidual_polynomial_eq_parts]")
lines.append("  calc ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b + C5_LinResidual_deg8 (𝕂 := 𝕂) a b + C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖")
lines.append("      ≤ ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b + C5_LinResidual_deg8 (𝕂 := 𝕂) a b‖ + ‖C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖ := norm_add_le _ _")
lines.append("    _ ≤ ‖C5_LinResidual_deg7 (𝕂 := 𝕂) a b‖ + ‖C5_LinResidual_deg8 (𝕂 := 𝕂) a b‖ + ‖C5_LinResidual_deg9 (𝕂 := 𝕂) a b‖ := by")
lines.append("        linarith [norm_add_le (C5_LinResidual_deg7 (𝕂 := 𝕂) a b) (C5_LinResidual_deg8 (𝕂 := 𝕂) a b),")
lines.append("                   norm_nonneg (C5_LinResidual_deg9 (𝕂 := 𝕂) a b)]")
lines.append(f"    _ ≤ ({deg7_sum} / {denom7} : ℝ) * s ^ 7 + ({deg8_sum} / {denom8} : ℝ) * s ^ 8 + ({deg9_sum} / {denom9} : ℝ) * s ^ 9 := by")
lines.append("        linarith [hdeg7, hdeg8, hdeg9]")
lines.append("    _ ≤ 1 * s ^ 7 := by nlinarith [hs7_nn, hs8, hs9]")
lines.append("")

print('\n'.join(lines))
