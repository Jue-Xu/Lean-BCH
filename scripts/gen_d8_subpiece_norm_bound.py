#!/usr/bin/env python3
"""
Generate Lean norm-bound lemmas for the d8 non-Dynkin sub-pieces of
`septic_d8_perturbation_poly`.

Pieces (CAS-derived in `gen_d8_P2_subpieces.py`, `gen_d8_P3_subpieces.py`,
existing perturbation script):

  P_2 sub-pieces (3):
    septic_d8_P2_C5_cubic_poly  ( 78 terms, LCM 184320,  Σ|num|/LCM ≈ 0.0052)
    septic_d8_P2_C6_quad_poly   (110 terms, LCM 368640,  Σ|num|/LCM ≈ 0.0081)
    septic_d8_P2_C7_lin_poly    (174 terms, LCM 3870720, Σ|num|/LCM ≈ 0.0108)
  P_3 sub-piece (1):
    septic_d8_P3_C6_lin_poly    (166 terms, LCM 1105920, Σ|num|/LCM ≈ 0.0126)
  P_4 single piece (1):
    septic_d8_P4_poly           (154 terms, LCM 552960,  Σ|num|/LCM ≈ 0.0093)
  Cross V_2·V_3 (1):
    septic_d8_cross_V2_V3_poly  (174 terms, LCM 1105920, Σ|num|/LCM ≈ ...)

For each, we emit:
  • SubpieceTermN (Nat → 𝔸) family.
  • SubpieceTerm (Fin N → 𝔸) wrapper.
  • _eq_sum (explicit form = ∑ Fin N, ...)
  • Term_norm_le (per-i ‖term‖ ≤ MAX/LCM · s^8).
  • norm_le (Σ ‖term‖ ≤ N·MAX/LCM · s^8 ≤ K · s^8).

For pieces with N > 124 we split into halves (single Finset.sum_range_succ
unfold fails simp recursion at ≥125 terms; see memory).

Usage:
    python3 gen_d8_subpiece_norm_bound.py <piece_name>
where <piece_name> is one of:
    P2_C5_cubic | P2_C6_quad | P2_C7_lin | P3_C6_lin | P4 | cross_V2_V3
"""

import sympy as sp
from collections import defaultdict
import sys


# ---- ncpoly helpers (copy from gen_d8_P2_subpieces.py) ----

def ncpoly_zero():
    return defaultdict(lambda: sp.Integer(0))


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
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0: return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0),
                       {w: c * v for w, v in p.items()})


def ncpoly_sub(p, q): return ncpoly_add(p, ncpoly_scale(q, -1))


def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in r.items() if c != 0})


def ncpoly_bracket(p, q):
    return ncpoly_sub(ncpoly_mul(p, q), ncpoly_mul(q, p))


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
    m1 = defaultdict(lambda: sp.Integer(0),
                     {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def substitute(p, sub_a, sub_b):
    result = ncpoly_zero()
    for word, coef in p.items():
        prod = ncpoly_from_scalar(1)
        for atom in word:
            sub_poly = sub_a if atom == 0 else sub_b
            prod = ncpoly_mul(prod, sub_poly)
        result = ncpoly_add(result, ncpoly_scale(prod, coef))
    return result


# ---- Sub-piece computation ----

def compute_subpiece(name):
    """Return (items, target_degree) for the named sub-piece."""
    a = ncpoly_a(); b = ncpoly_b()
    half = sp.Rational(1, 2)
    half_a = ncpoly_scale(a, half)
    x = ncpoly_add(half_a, b)
    bch_inner = bch_series(half_a, b, 8)
    V2 = extract_degree(bch_inner, 2)
    V3 = extract_degree(bch_inner, 3)
    V4 = extract_degree(bch_inner, 4)
    V5 = extract_degree(bch_inner, 5)
    V6 = extract_degree(bch_inner, 6)
    x_plus_V2 = ncpoly_add(x, V2)
    x_plus_V3 = ncpoly_add(x, V3)
    x_plus_V4 = ncpoly_add(x, V4)
    x_plus_V5 = ncpoly_add(x, V5)
    x_plus_V6 = ncpoly_add(x, V6)

    def cross_piece(Vj, Vk, target_deg):
        bch_jk = bch_series(ncpoly_add(ncpoly_add(x, Vj), Vk), half_a, target_deg)
        bch_j = bch_series(ncpoly_add(x, Vj), half_a, target_deg)
        bch_k = bch_series(ncpoly_add(x, Vk), half_a, target_deg)
        bch_0 = bch_series(x, half_a, target_deg)
        result = ncpoly_add(ncpoly_sub(bch_jk, bch_j), ncpoly_sub(bch_0, bch_k))
        return extract_degree(result, target_deg)

    def single_piece(Vj, target_deg):
        bch_static = bch_series(x, half_a, target_deg)
        bch_at_xVj = bch_series(ncpoly_add(x, Vj), half_a, target_deg)
        return extract_degree(ncpoly_sub(bch_at_xVj, bch_static), target_deg)

    bch_full_7 = bch_series(a, b, 7)
    bch_3_abs = extract_degree(bch_full_7, 3)
    bch_4_abs = extract_degree(bch_full_7, 4)
    bch_5_abs = extract_degree(bch_full_7, 5)
    bch_6_abs = extract_degree(bch_full_7, 6)
    bch_7_abs = extract_degree(bch_full_7, 7)

    # ---- d8 sub-pieces ----
    if name == "P2_C5_cubic":
        bch_5_at_xV2 = substitute(bch_5_abs, x_plus_V2, half_a)
        bch_5_at_x = substitute(bch_5_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_5_at_xV2, bch_5_at_x), 8)
        deg = 8
    elif name == "P2_C6_quad":
        bch_6_at_xV2 = substitute(bch_6_abs, x_plus_V2, half_a)
        bch_6_at_x = substitute(bch_6_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_6_at_xV2, bch_6_at_x), 8)
        deg = 8
    elif name == "P2_C7_lin":
        bch_7_at_xV2 = substitute(bch_7_abs, x_plus_V2, half_a)
        bch_7_at_x = substitute(bch_7_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_7_at_xV2, bch_7_at_x), 8)
        deg = 8
    elif name == "P4":
        bch_static = bch_series(x, half_a, 8)
        bch_at_xV4 = bch_series(x_plus_V4, half_a, 8)
        poly = extract_degree(ncpoly_sub(bch_at_xV4, bch_static), 8)
        deg = 8
    elif name == "P3_C6_lin":
        bch_static = bch_series(x, half_a, 8)
        bch_at_xV3 = bch_series(x_plus_V3, half_a, 8)
        P3 = extract_degree(ncpoly_sub(bch_at_xV3, bch_static), 8)
        inner = ncpoly_bracket(V3, half_a)
        mid = ncpoly_bracket(V3, inner)
        outer = ncpoly_bracket(half_a, mid)
        C4_quad = ncpoly_scale(outer, sp.Rational(-1, 24))
        poly = ncpoly_sub(P3, C4_quad)
        deg = 8
    elif name == "cross_V2_V3":
        x_p_V2_V3 = ncpoly_add(x_plus_V2, V3)
        bch_full = bch_series(x_p_V2_V3, half_a, 8)
        bch_V2 = bch_series(x_plus_V2, half_a, 8)
        bch_V3 = bch_series(x_plus_V3, half_a, 8)
        bch_x = bch_series(x, half_a, 8)
        cross = ncpoly_add(
            ncpoly_sub(bch_full, bch_V2),
            ncpoly_sub(bch_x, bch_V3))
        poly = extract_degree(cross, 8)
        deg = 8
    # ---- d7 sub-pieces ----
    elif name == "d7_P2_C5_quad":
        # septic_d7_P2_C5_quad_poly: deg-7 part of bch_quintic(x+V_2, a') - bch_quintic(x, a').
        bch_5_at_xV2 = substitute(bch_5_abs, x_plus_V2, half_a)
        bch_5_at_x = substitute(bch_5_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_5_at_xV2, bch_5_at_x), 7)
        deg = 7
    elif name == "d7_P2_C6_lin":
        # septic_d7_P2_C6_lin_poly: deg-7 part of bch_sextic(x+V_2, a') - bch_sextic(x, a').
        bch_6_at_xV2 = substitute(bch_6_abs, x_plus_V2, half_a)
        bch_6_at_x = substitute(bch_6_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_6_at_xV2, bch_6_at_x), 7)
        deg = 7
    elif name == "d7_P3_C5_lin":
        # septic_d7_P3_C5_lin_poly = septic_d7_P3_poly - septic_d7_P3_C3_quad_poly
        # P_3 = deg-7 part of (bch(x + V_3, ½a) - bch(x, ½a))
        # C_3_quad = (1/12)·[V_3, [V_3, ½a]] (Dynkin)
        P3 = single_piece(V3, 7)
        inner = ncpoly_bracket(V3, half_a)
        outer = ncpoly_bracket(V3, inner)
        C3_quad = ncpoly_scale(outer, sp.Rational(1, 12))
        poly = ncpoly_sub(P3, C3_quad)
        deg = 7
    # ---- d8 parent pieces ----
    elif name == "d8_P2": poly, deg = single_piece(V2, 8), 8
    elif name == "d8_P3": poly, deg = single_piece(V3, 8), 8
    elif name == "d8_P5": poly, deg = single_piece(V5, 8), 8
    elif name == "d8_P6": poly, deg = single_piece(V6, 8), 8
    elif name == "d8_cross_V2_V4": poly, deg = cross_piece(V2, V4, 8), 8
    elif name == "d8_cross_V2_V5": poly, deg = cross_piece(V2, V5, 8), 8
    elif name == "d8_cross_V3_V4": poly, deg = cross_piece(V3, V4, 8), 8
    # ---- d8 Dynkin sub-piece ----
    elif name == "d8_P3_C4_quad":
        # septic_d8_P3_C4_quad_poly = -(1/24)·[a', [V_3, [V_3, a']]]
        inner = ncpoly_bracket(V3, half_a)
        mid = ncpoly_bracket(V3, inner)
        outer = ncpoly_bracket(half_a, mid)
        poly = ncpoly_scale(outer, sp.Rational(-1, 24))
        deg = 8
    # ---- d7 parent pieces ----
    elif name == "d7_P2": poly, deg = single_piece(V2, 7), 7
    elif name == "d7_P3": poly, deg = single_piece(V3, 7), 7
    elif name == "d7_P4": poly, deg = single_piece(V4, 7), 7
    elif name == "d7_P5": poly, deg = single_piece(V5, 7), 7
    elif name == "d7_cross_V2_V3": poly, deg = cross_piece(V2, V3, 7), 7
    elif name == "d7_cross_V2_V4": poly, deg = cross_piece(V2, V4, 7), 7
    # ---- d7 Dynkin sub-piece ----
    elif name == "d7_P3_C3_quad":
        # septic_d7_P3_C3_quad_poly = (1/12)·[V_3, [V_3, a']]
        inner = ncpoly_bracket(V3, half_a)
        outer = ncpoly_bracket(V3, inner)
        poly = ncpoly_scale(outer, sp.Rational(1, 12))
        deg = 7
    # ---- d=9 residual: k=4 V_2 part of C_5 diff ----
    elif name == "d8_P2_C5_quartic_residual":
        # septic_d8_P2_C5_quartic_residual_poly: deg-9 part of
        #   bch_quintic_term(x + V_2, ½a) - bch_quintic_term(x, ½a)
        # = k=4 V_2 substitutions into C_5 (5 z-positions; deg = 5 - 4 + 8 = 9).
        bch_5_at_xV2 = substitute(bch_5_abs, x_plus_V2, half_a)
        bch_5_at_x = substitute(bch_5_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_5_at_xV2, bch_5_at_x), 9)
        deg = 9
    # ---- d=9 residual: k=3 V_2 part of C_6 diff ----
    elif name == "d8_P2_C6_cubic_residual":
        # septic_d8_P2_C6_cubic_residual_poly: deg-9 part of
        #   bch_sextic_term(x + V_2, ½a) - bch_sextic_term(x, ½a)
        # = k=3 V_2 substitutions into C_6 (6 z-positions; deg = 6 - 3 + 6 = 9).
        bch_6_at_xV2 = substitute(bch_6_abs, x_plus_V2, half_a)
        bch_6_at_x = substitute(bch_6_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_6_at_xV2, bch_6_at_x), 9)
        deg = 9
    # ---- d=10 residual: k=4 V_2 part of C_6 diff ----
    elif name == "d8_P2_C6_quartic_residual":
        # septic_d8_P2_C6_quartic_residual_poly: deg-10 part of
        #   bch_sextic_term(x + V_2, ½a) - bch_sextic_term(x, ½a)
        # = k=4 V_2 substitutions into C_6 (6 z-positions; deg = 6 - 4 + 8 = 10).
        bch_6_at_xV2 = substitute(bch_6_abs, x_plus_V2, half_a)
        bch_6_at_x = substitute(bch_6_abs, x, half_a)
        poly = extract_degree(ncpoly_sub(bch_6_at_xV2, bch_6_at_x), 10)
        deg = 10
    else:
        raise ValueError(f"Unknown piece name: {name}")

    items = sorted([(w, c) for w, c in poly.items() if c != 0], key=lambda x: x[0])
    return items, deg


# ---- Lean code emission ----

def word_lean(w):
    return ' * '.join('a' if x == 0 else 'b' for x in w)


def word_args(w):
    return ' '.join('a' if x == 0 else 'b' for x in w)


def word_hyps(w):
    return ' '.join('ha' if x == 0 else 'hb' for x in w)


def lcm_and_stats(items):
    LCM = 1
    for _, c in items:
        if c != 0:
            LCM = sp.lcm(LCM, sp.denom(sp.nsimplify(c)))
    LCM = int(LCM)
    max_abs = max(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    sum_abs = sum(abs(int(sp.nsimplify(c * LCM))) for _, c in items)
    return LCM, max_abs, sum_abs


def emit_single_sum(piece_lean_name, items, lcm, max_abs, deg=8):
    """Emit single-Finset.sum norm-bound lemma (for N ≤ 124).

    deg: the polynomial degree (7 or 8); selects `deg7_smul_word_le` vs
    `{helper}` and `s^deg` in the bound.
    """
    helper = f"deg{deg}_smul_word_le"
    N = len(items)
    cap = piece_lean_name.replace("_poly", "")  # drop trailing _poly for prefix
    # Build a clean PascalCase prefix for the helper-family name.
    # e.g. septic_d8_P2_C5_cubic -> SepticD8P2C5Cubic
    parts = cap.split("_")
    prefix = "".join(p[:1].upper() + p[1:] for p in parts)

    print(f"-- Per-Nat-index family for `{piece_lean_name}`.")
    print("set_option maxHeartbeats 1600000 in")
    print(f"private noncomputable def {prefix}TermN (a b : 𝔸) : Nat → 𝔸")
    for idx, (w, c) in enumerate(items):
        n = int(sp.nsimplify(c * lcm))
        print(f"  | {idx} => ({n} / {lcm} : 𝕂) • ({word_lean(w)})")
    print("  | _ => 0")
    print()

    print(f"/-- `Fin {N}`-indexed wrapper for `{prefix}TermN`. -/")
    print(f"private noncomputable def {prefix}Term (a b : 𝔸) (i : Fin {N}) : 𝔸 :=")
    print(f"  {prefix}TermN (𝕂 := 𝕂) a b i.val")
    print()

    print(f"-- The explicit `{piece_lean_name}` def equals the `Finset.sum` form.")
    print("set_option maxHeartbeats 16000000 in")
    print("set_option maxRecDepth 2000 in")
    print(f"private theorem {piece_lean_name}_eq_sum (a b : 𝔸) :")
    print(f"    {piece_lean_name} 𝕂 a b = ∑ i : Fin {N}, {prefix}Term (𝕂 := 𝕂) a b i := by")
    print(f"  unfold {piece_lean_name} {prefix}Term")
    print(f"  rw [Fin.sum_univ_eq_sum_range (fun k => {prefix}TermN (𝕂 := 𝕂) a b k)]")
    print("  simp only [Finset.sum_range_succ, Finset.sum_range_zero,")
    print(f"    {prefix}TermN, zero_add]")
    print()

    print(f"-- Per-index uniform bound: `‖{prefix}Term a b i‖ ≤ ({max_abs}/{lcm}) · s^{deg}`.")
    print("set_option maxHeartbeats 8000000 in")
    print(f"private lemma {prefix}Term_norm_le (a b : 𝔸) (s : ℝ)")
    print("    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
    print(f"    ∀ i : Fin {N}, ‖{prefix}Term (𝕂 := 𝕂) a b i‖ "
          f"≤ ({max_abs} / {lcm} : ℝ) * s^{deg} := fun i =>")
    print("  match i with")
    for idx, (w, c) in enumerate(items):
        n = int(sp.nsimplify(c * lcm))
        wargs = word_args(w)
        whyps = word_hyps(w)
        print(f"  | ⟨{idx}, _⟩ =>")
        print(f"    show ‖({n} / {lcm} : 𝕂) • ({word_lean(w)})‖ ≤ "
              f"({max_abs} / {lcm} : ℝ) * s^{deg} from")
        print(f"      {helper} ({n} / {lcm} : 𝕂) ({max_abs} / {lcm} : ℝ)")
        print(f"        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)")
        print(f"        {wargs} s {whyps} (by norm_num) hs")
    print(f"  | ⟨_ + {N}, h⟩ => absurd h (by omega)")
    print()

    # The combined bound: N · max_abs / LCM
    coef_num = N * max_abs
    coef_den = lcm

    super = {7: "⁷", 8: "⁸", 9: "⁹", 10: "¹⁰"}[deg]
    print("set_option maxHeartbeats 800000 in")
    print(f"/-- **Norm bound for `{piece_lean_name}`**:")
    print(f"`‖{piece_lean_name}(a,b)‖ ≤ ({coef_num}/{coef_den}) · (‖a‖+‖b‖){super}`.")
    print()
    print(f"{N} explicit deg-{deg} terms, max |numerator| = {max_abs}, LCM = {lcm}.")
    print(f"Per-term uniform bound `({max_abs}/{lcm}) · s^{deg}` summed over Fin {N}. -/")
    print(f"theorem norm_{piece_lean_name}_le (a b : 𝔸) :")
    print(f"    ‖{piece_lean_name} 𝕂 a b‖ ≤ "
          f"({coef_num} / {coef_den} : ℝ) * (‖a‖ + ‖b‖) ^ {deg} := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print("  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
    print("  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
    print(f"  rw [{piece_lean_name}_eq_sum]")
    print(f"  calc ‖∑ i : Fin {N}, {prefix}Term (𝕂 := 𝕂) a b i‖")
    print(f"      ≤ ∑ i : Fin {N}, ‖{prefix}Term (𝕂 := 𝕂) a b i‖ := norm_sum_le _ _")
    print(f"    _ ≤ ∑ _i : Fin {N}, ({max_abs} / {lcm} : ℝ) * s^{deg} :=")
    print(f"        Finset.sum_le_sum (fun i _ => {prefix}Term_norm_le "
          f"(𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)")
    print(f"    _ = {N} * (({max_abs} / {lcm} : ℝ) * s^{deg}) := by")
    print("        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
    print(f"    _ = ({coef_num} / {coef_den} : ℝ) * s^{deg} := by ring")
    print()


def emit_split_half(piece_lean_name, items, lcm, max_abs, deg=8):
    """Emit split-half Finset.sum norm-bound lemmas (for N > 124).

    Splits N items into two halves at N//2. Each half gets its own
    TermN family, Term wrapper, eq_sum, per-i bound, and half-sum bound.
    The whole-poly statement combines via triangle inequality + a `_split`
    lemma rewriting the def as a sum of two explicit forms (via `abel`).
    """
    helper = f"deg{deg}_smul_word_le"
    N = len(items)
    SPLIT = N // 2
    first_items = items[:SPLIT]
    second_items = items[SPLIT:]
    N1, N2 = len(first_items), len(second_items)

    # Build a clean PascalCase prefix for the helper-family name.
    parts = piece_lean_name.replace("_poly", "").split("_")
    base_prefix = "".join(p[:1].upper() + p[1:] for p in parts)

    def emit_half(half_label, half_items, half_N, half_prefix):
        print(f"-- Per-Nat-index family for the {half_label} half of `{piece_lean_name}`.")
        print("set_option maxHeartbeats 1600000 in")
        print(f"private noncomputable def {half_prefix}TermN (a b : 𝔸) : Nat → 𝔸")
        for idx, (w, c) in enumerate(half_items):
            n = int(sp.nsimplify(c * lcm))
            print(f"  | {idx} => ({n} / {lcm} : 𝕂) • ({word_lean(w)})")
        print("  | _ => 0")
        print()

        print(f"/-- `Fin {half_N}`-indexed wrapper for `{half_prefix}TermN`. -/")
        print(f"private noncomputable def {half_prefix}Term (a b : 𝔸) (i : Fin {half_N}) : 𝔸 :=")
        print(f"  {half_prefix}TermN (𝕂 := 𝕂) a b i.val")
        print()

        print(f"-- The explicit {half_label}-half sum equals the `Finset.sum` form.")
        print("set_option maxHeartbeats 16000000 in")
        print("set_option maxRecDepth 2000 in")
        print(f"private theorem {half_prefix}_explicit_eq_sum (a b : 𝔸) :")
        print("    ", end="")
        first = True
        for _, (w, c) in enumerate(half_items):
            n = int(sp.nsimplify(c * lcm))
            sep = "" if first else " +\n      "
            print(f"{sep}({n} / {lcm} : 𝕂) • ({word_lean(w)})", end="")
            first = False
        print(" =")
        print(f"      ∑ i : Fin {half_N}, {half_prefix}Term (𝕂 := 𝕂) a b i := by")
        print(f"  unfold {half_prefix}Term")
        print(f"  rw [Fin.sum_univ_eq_sum_range (fun k => {half_prefix}TermN (𝕂 := 𝕂) a b k)]")
        print("  simp only [Finset.sum_range_succ, Finset.sum_range_zero,")
        print(f"    {half_prefix}TermN, zero_add]")
        print()

        print(f"-- Per-index uniform bound: `‖{half_prefix}Term a b i‖ ≤ ({max_abs}/{lcm}) · s^{deg}`.")
        print("set_option maxHeartbeats 8000000 in")
        print(f"private lemma {half_prefix}Term_norm_le (a b : 𝔸) (s : ℝ)")
        print("    (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) (hs : 0 ≤ s) :")
        print(f"    ∀ i : Fin {half_N}, ‖{half_prefix}Term (𝕂 := 𝕂) a b i‖ "
              f"≤ ({max_abs} / {lcm} : ℝ) * s^{deg} := fun i =>")
        print("  match i with")
        for idx, (w, c) in enumerate(half_items):
            n = int(sp.nsimplify(c * lcm))
            wargs = word_args(w)
            whyps = word_hyps(w)
            print(f"  | ⟨{idx}, _⟩ =>")
            print(f"    show ‖({n} / {lcm} : 𝕂) • ({word_lean(w)})‖ ≤ "
                  f"({max_abs} / {lcm} : ℝ) * s^{deg} from")
            print(f"      {helper} ({n} / {lcm} : 𝕂) ({max_abs} / {lcm} : ℝ)")
            print(f"        (by rw [norm_div]; simp [RCLike.norm_ofNat] <;> norm_num)")
            print(f"        {wargs} s {whyps} (by norm_num) hs")
        print(f"  | ⟨_ + {half_N}, h⟩ => absurd h (by omega)")
        print()

        print("set_option maxHeartbeats 1600000 in")
        print(f"-- Norm bound on the {half_label} half.")
        print(f"private theorem norm_{half_prefix}Sum_le (a b : 𝔸) :")
        print(f"    ‖∑ i : Fin {half_N}, {half_prefix}Term (𝕂 := 𝕂) a b i‖ "
              f"≤ ({half_N} * {max_abs} / {lcm} : ℝ) * (‖a‖ + ‖b‖) ^ {deg} := by")
        print("  set s := ‖a‖ + ‖b‖ with hs_def")
        print("  have hs_nn : 0 ≤ s := by positivity")
        print("  have ha_le : ‖a‖ ≤ s := by linarith [norm_nonneg b]")
        print("  have hb_le : ‖b‖ ≤ s := by linarith [norm_nonneg a]")
        print(f"  calc ‖∑ i : Fin {half_N}, {half_prefix}Term (𝕂 := 𝕂) a b i‖")
        print(f"      ≤ ∑ i : Fin {half_N}, ‖{half_prefix}Term (𝕂 := 𝕂) a b i‖ "
              ":= norm_sum_le _ _")
        print(f"    _ ≤ ∑ _i : Fin {half_N}, ({max_abs} / {lcm} : ℝ) * s^{deg} :=")
        print(f"        Finset.sum_le_sum (fun i _ => {half_prefix}Term_norm_le "
              f"(𝕂 := 𝕂) a b s ha_le hb_le hs_nn i)")
        print(f"    _ = {half_N} * (({max_abs} / {lcm} : ℝ) * s^{deg}) := by")
        print("        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring")
        print(f"    _ = ({half_N} * {max_abs} / {lcm} : ℝ) * s^{deg} := by ring")
        print()

    emit_half("first", first_items, N1, base_prefix + "First")
    emit_half("second", second_items, N2, base_prefix + "Second")

    # Split lemma: piece = first_explicit + second_explicit (via abel).
    print(f"-- Split `{piece_lean_name}` into two explicit halves.")
    print("set_option maxHeartbeats 16000000 in")
    print(f"private theorem {piece_lean_name}_split (a b : 𝔸) :")
    print(f"    {piece_lean_name} 𝕂 a b =")
    # First-half explicit form
    print("    (", end="")
    first = True
    for w, c in first_items:
        n = int(sp.nsimplify(c * lcm))
        sep = "" if first else " +\n      "
        print(f"{sep}({n} / {lcm} : 𝕂) • ({word_lean(w)})", end="")
        first = False
    print(") +")
    # Second-half explicit form
    print("    (", end="")
    first = True
    for w, c in second_items:
        n = int(sp.nsimplify(c * lcm))
        sep = "" if first else " +\n      "
        print(f"{sep}({n} / {lcm} : 𝕂) • ({word_lean(w)})", end="")
        first = False
    print(") := by")
    print(f"  unfold {piece_lean_name}")
    print("  abel")
    print()

    # Combined theorem.
    total_num = N * max_abs
    total_den = lcm
    print("set_option maxHeartbeats 800000 in")
    print(f"/-- **Norm bound for `{piece_lean_name}`**:")
    print(f"`‖{piece_lean_name}(a,b)‖ ≤ ({total_num}/{total_den}) · (‖a‖+‖b‖)^{deg}`.")
    print()
    print(f"{N} explicit deg-{deg} terms (split {N1}/{N2}), max |numerator| = {max_abs}, LCM = {lcm}.")
    print(f"Uses the **split-half** Finset.sum approach: `≤ ‖first‖ + ‖second‖`. -/")
    print(f"theorem norm_{piece_lean_name}_le (a b : 𝔸) :")
    print(f"    ‖{piece_lean_name} 𝕂 a b‖ ≤ "
          f"({total_num} / {total_den} : ℝ) * (‖a‖ + ‖b‖) ^ {deg} := by")
    print("  set s := ‖a‖ + ‖b‖ with hs_def")
    print("  have hs_nn : 0 ≤ s := by positivity")
    print(f"  have hsdeg_nn : 0 ≤ s ^ {deg} := pow_nonneg hs_nn {deg}")
    print(f"  rw [{piece_lean_name}_split,")
    print(f"      {base_prefix}First_explicit_eq_sum,")
    print(f"      {base_prefix}Second_explicit_eq_sum]")
    print(f"  calc ‖(∑ i : Fin {N1}, {base_prefix}FirstTerm (𝕂 := 𝕂) a b i) + "
          f"(∑ i : Fin {N2}, {base_prefix}SecondTerm (𝕂 := 𝕂) a b i)‖")
    print(f"      ≤ ‖∑ i : Fin {N1}, {base_prefix}FirstTerm (𝕂 := 𝕂) a b i‖ +")
    print(f"          ‖∑ i : Fin {N2}, {base_prefix}SecondTerm (𝕂 := 𝕂) a b i‖ := norm_add_le _ _")
    print(f"    _ ≤ ({N1} * {max_abs} / {lcm} : ℝ) * s^{deg} +")
    print(f"          ({N2} * {max_abs} / {lcm} : ℝ) * s^{deg} :=")
    print(f"        add_le_add (norm_{base_prefix}FirstSum_le a b) "
          f"(norm_{base_prefix}SecondSum_le a b)")
    print(f"    _ = ({total_num} / {total_den} : ℝ) * s^{deg} := by ring")
    print()


def main():
    if len(sys.argv) < 2:
        print("Usage: gen_d8_subpiece_norm_bound.py <piece_name>", file=sys.stderr)
        print("Valid: P2_C5_cubic, P2_C6_quad, P2_C7_lin, P3_C6_lin, P4, cross_V2_V3",
              file=sys.stderr)
        sys.exit(1)

    name = sys.argv[1]
    items, deg = compute_subpiece(name)
    lcm, max_abs, sum_abs = lcm_and_stats(items)
    N = len(items)
    sys.stderr.write(f"# Piece: {name} (deg {deg})\n")
    sys.stderr.write(f"# {N} terms, LCM = {lcm}, max|num| = {max_abs}, "
                     f"Σ|num| = {sum_abs}\n")
    sys.stderr.write(f"# Σ|num|/LCM = {sum_abs}/{lcm} ≈ {sum_abs/lcm:.6f}\n")
    sys.stderr.write(f"# Bound:  N·max/LCM = {N}·{max_abs}/{lcm} = "
                     f"{N*max_abs}/{lcm} ≈ {N*max_abs/lcm:.4f}\n")

    # Map name -> Lean def name.
    lean_name = {
        # d8 sub-pieces (added session 53)
        "P2_C5_cubic": "septic_d8_P2_C5_cubic_poly",
        "P2_C6_quad":  "septic_d8_P2_C6_quad_poly",
        "P2_C7_lin":   "septic_d8_P2_C7_lin_poly",
        "P3_C6_lin":   "septic_d8_P3_C6_lin_poly",
        "P4":          "septic_d8_P4_poly",
        "cross_V2_V3": "septic_d8_cross_V2_V3_poly",
        # d7 sub-pieces (added session 54)
        "d7_P2_C5_quad": "septic_d7_P2_C5_quad_poly",
        "d7_P2_C6_lin":  "septic_d7_P2_C6_lin_poly",
        "d7_P3_C5_lin":  "septic_d7_P3_C5_lin_poly",
        # d8 parent + Dynkin pieces (this session)
        "d8_P2":          "septic_d8_P2_poly",
        "d8_P3":          "septic_d8_P3_poly",
        "d8_P5":          "septic_d8_P5_poly",
        "d8_P6":          "septic_d8_P6_poly",
        "d8_cross_V2_V4": "septic_d8_cross_V2_V4_poly",
        "d8_cross_V2_V5": "septic_d8_cross_V2_V5_poly",
        "d8_cross_V3_V4": "septic_d8_cross_V3_V4_poly",
        "d8_P3_C4_quad":  "septic_d8_P3_C4_quad_poly",
        # d7 parent + Dynkin pieces (this session)
        "d7_P2":          "septic_d7_P2_poly",
        "d7_P3":          "septic_d7_P3_poly",
        "d7_P4":          "septic_d7_P4_poly",
        "d7_P5":          "septic_d7_P5_poly",
        "d7_cross_V2_V3": "septic_d7_cross_V2_V3_poly",
        "d7_cross_V2_V4": "septic_d7_cross_V2_V4_poly",
        "d7_P3_C3_quad":  "septic_d7_P3_C3_quad_poly",
        # d8 P_2 C_5 deg-9 residual (this session)
        "d8_P2_C5_quartic_residual": "septic_d8_P2_C5_quartic_residual_poly",
        # d8 P_2 C_6 deg-9 residual (this session)
        "d8_P2_C6_cubic_residual": "septic_d8_P2_C6_cubic_residual_poly",
        # d8 P_2 C_6 deg-10 residual (this session)
        "d8_P2_C6_quartic_residual": "septic_d8_P2_C6_quartic_residual_poly",
    }[name]

    if N <= 124:
        emit_single_sum(lean_name, items, lcm, max_abs, deg=deg)
    else:
        emit_split_half(lean_name, items, lcm, max_abs, deg=deg)


if __name__ == "__main__":
    main()
