#!/usr/bin/env python3
"""Generate the full Stage 1 Lean section (R7 def + norm bound) from
`scripts/r7_data.txt`.

Outputs to stdout. Pipe to a file or insert into `BCH/Suzuki5Quintic.lean`.

Format expected in r7_data.txt:
    idx | word | c0 | c1 | c2 | K_w
where coefficient = c0 + c1·p + c2·p² (after Suzuki cubic reduction)
and K_w is a rational upper bound on |coef(p)| for p ∈ [41449/10⁵, 41450/10⁵].
"""
from fractions import Fraction
from typing import List, Tuple


def parse_rational(s: str) -> Fraction:
    """Parse '527657/62500000000' or '-17/14515200' into a Fraction."""
    return Fraction(s)


def format_rational(r: Fraction) -> str:
    """Format Fraction as 'p/q' (or 'p' if denominator is 1)."""
    if r.denominator == 1:
        return str(r.numerator)
    return f"{r.numerator}/{r.denominator}"


def load_data(path: str) -> List[Tuple[int, str, Fraction, Fraction, Fraction, Fraction]]:
    """Load (idx, word, c0, c1, c2, K_w) tuples from r7_data.txt."""
    data = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split('|')
            idx_str, word, c0, c1, c2, K_w = parts
            data.append((int(idx_str), word, parse_rational(c0), parse_rational(c1),
                         parse_rational(c2), parse_rational(K_w)))
    return data


def word_to_lean_product(word: str) -> str:
    """Convert 'AAABABB' to 'A * A * A * B * A * B * B'."""
    return ' * '.join(word)


def word_to_norm_args(word: str) -> str:
    """For r7_smul_word_le call: produce the args 'A B A A B B A' (no separator)."""
    return ' '.join(word)


def word_to_h_args(word: str) -> str:
    """Norm hypothesis args: 'hA hB hA hA hB hB hA'."""
    return ' '.join(f"h{ch}" for ch in word)


def coef_to_lean_expr(c0: Fraction, c1: Fraction, c2: Fraction) -> str:
    """Format c0 + c1·p + c2·p² as Lean expression in (p : ℝ)."""
    parts = []
    # Constant
    if c0 != 0:
        parts.append(f"({format_rational(c0)} : ℝ)")
    # p term
    if c1 != 0:
        parts.append(f"({format_rational(c1)} : ℝ) * p")
    # p² term
    if c2 != 0:
        parts.append(f"({format_rational(c2)} : ℝ) * p^2")
    if not parts:
        return "(0 : ℝ)"
    return " + ".join(parts)


def coef_at_suzukiP_expr(c0: Fraction, c1: Fraction, c2: Fraction) -> str:
    """Format c0 + c1·suzukiP + c2·suzukiP² as Lean expression."""
    parts = []
    if c0 != 0:
        parts.append(f"({format_rational(c0)} : ℝ)")
    if c1 != 0:
        parts.append(f"({format_rational(c1)} : ℝ) * suzukiP")
    if c2 != 0:
        parts.append(f"({format_rational(c2)} : ℝ) * suzukiP^2")
    if not parts:
        return "(0 : ℝ)"
    return " + ".join(parts)


# ---------- Section emitters ----------

def emit_helper() -> str:
    return '''
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **R7 smul-word helper**: `‖c • (l₁·…·l₇)‖ ≤ K · m^7` given `|c| ≤ K`
and each `‖lᵢ‖ ≤ m`. Used per-i in `r7Term_norm_le`. -/
private lemma r7_smul_word_le (c K : ℝ) (hc : |c| ≤ K)
    (l1 l2 l3 l4 l5 l6 l7 : 𝔸) (m : ℝ)
    (h1 : ‖l1‖ ≤ m) (h2 : ‖l2‖ ≤ m) (h3 : ‖l3‖ ≤ m)
    (h4 : ‖l4‖ ≤ m) (h5 : ‖l5‖ ≤ m) (h6 : ‖l6‖ ≤ m) (h7 : ‖l7‖ ≤ m)
    (hK : 0 ≤ K) (hm : 0 ≤ m) :
    ‖c • (l1 * l2 * l3 * l4 * l5 * l6 * l7)‖ ≤ K * m^7 := by
  rw [norm_smul, Real.norm_eq_abs]
  calc |c| * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖
      ≤ K * ‖l1 * l2 * l3 * l4 * l5 * l6 * l7‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ K * (‖l1‖ * ‖l2‖ * ‖l3‖ * ‖l4‖ * ‖l5‖ * ‖l6‖ * ‖l7‖) :=
        mul_le_mul_of_nonneg_left (norm_7prod_le _ _ _ _ _ _ _) hK
    _ ≤ K * (m * m * m * m * m * m * m) := by gcongr
    _ = K * m^7 := by ring
'''


def emit_r7Term_def(data) -> str:
    lines = ['''
-- Per-index family: the 126 non-zero terms of `suzuki5_R7 A B p`. Each
-- term is `(c₀ + c₁·p + c₂·p²) • word(A, B)` where the coefficient is the
-- post-Suzuki-cubic-reduction form, and `word(A, B)` is a 7-letter monomial
-- in {A, B}.
--
-- CAS-derived from `Lean-Trotter/scripts/compute_bch_r7.py`. The
-- polynomial-in-p form preserves the Stage 3 algebraic identity (τ⁷ match
-- under `IsSuzukiCubic p`); the per-term bound at `p = suzukiP` is given
-- by `r7Bound i`.
set_option maxHeartbeats 1600000 in
private noncomputable def r7Term (A B : 𝔸) (p : ℝ) : Fin 126 → 𝔸''']
    for idx, word, c0, c1, c2, _K_w in data:
        coef_expr = coef_to_lean_expr(c0, c1, c2)
        word_prod = word_to_lean_product(word)
        lines.append(f'  | ⟨{idx}, _⟩ => ({coef_expr}) • ({word_prod})')
    lines.append('  | ⟨_ + 126, h⟩ => absurd h (by omega)')
    return '\n'.join(lines) + '\n'


def emit_r7Bound_def(data) -> str:
    lines = ['''
-- Per-index upper bound `K_i ≥ |c_i(p)|` for `p ∈ [41449/10⁵, 41450/10⁵]`
-- (the interval containing `suzukiP`). Rounded up to 10⁻¹² precision so the
-- nlinarith proof in `r7Term_norm_le` has comfortable slack.
--
-- Defined on `Nat` (rather than `Fin 126`) so `Finset.sum_range_succ` reduction
-- in `sum_r7Bound_le` doesn't get stuck on `Fin.succ` chains.
--
-- `Σ_{k<126} r7BoundN k = 1950990333 / 10¹¹ ≤ bchR7UniformConstant = 0.01951`.
set_option maxHeartbeats 800000 in
private noncomputable def r7BoundN : Nat → ℝ''']
    for idx, _word, _c0, _c1, _c2, K_w in data:
        lines.append(f'  | {idx} => {format_rational(K_w)}')
    lines.append('  | _ => 0')
    lines.append('')
    lines.append('-- Fin-indexed wrapper around `r7BoundN` (for use with `Finset.sum (Fin 126)`).')
    lines.append('private noncomputable def r7Bound (i : Fin 126) : ℝ := r7BoundN i.val')
    return '\n'.join(lines) + '\n'


def emit_suzuki5_R7_def() -> str:
    return '''
/-- The explicit τ⁷ element `R₇` of the Suzuki-S4 BCH expansion: the
sum of 126 non-zero 7-letter Childs-words at Suzuki `p`, with coefficients
that are quadratic-in-p polynomials (after Suzuki-cubic reduction).

`suzuki5_R7 A B suzukiP` is the leading τ⁷ term in
`log(suzuki5Product A B suzukiP τ) − τ•(A+B)` modulo `O(τ⁸)`. -/
noncomputable def suzuki5_R7 (A B : 𝔸) (p : ℝ) : 𝔸 :=
  ∑ i : Fin 126, r7Term A B p i
'''


def emit_r7Term_norm_le(data) -> str:
    lines = ['''
-- Per-index norm bound for `r7Term` at `p = suzukiP`:
-- `‖r7Term A B suzukiP i‖ ≤ r7Bound i · m^7` where `m = max(‖A‖, ‖B‖)`.
set_option maxHeartbeats 64000000 in
private lemma r7Term_norm_le (A B : 𝔸) (m : ℝ)
    (hA : ‖A‖ ≤ m) (hB : ‖B‖ ≤ m) (hm : 0 ≤ m) :
    ∀ i : Fin 126, ‖r7Term A B suzukiP i‖ ≤ r7Bound i * m^7 := by
  intro i
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  match i with''']
    for idx, word, c0, c1, c2, K_w in data:
        coef_at_suz = coef_at_suzukiP_expr(c0, c1, c2)
        word_prod = word_to_lean_product(word)
        word_args = word_to_norm_args(word)
        h_args = word_to_h_args(word)
        K_str = format_rational(K_w)
        lines.append(f'''  | ⟨{idx}, _⟩ =>
      show ‖({coef_at_suz}) • ({word_prod})‖ ≤ ({K_str} : ℝ) * m^7
      have hcoef : |({coef_at_suz})| ≤ ({K_str} : ℝ) := by
        rw [abs_le]
        refine ⟨?_, ?_⟩ <;>
          nlinarith [hlo, hhi, sq_nonneg suzukiP,
                     sq_nonneg (suzukiP - 41449/100000),
                     sq_nonneg (suzukiP - 41450/100000)]
      exact r7_smul_word_le _ _ hcoef {word_args} m {h_args} (by norm_num) hm''')
    lines.append('  | ⟨_ + 126, h⟩ => exact absurd h (by omega)')
    return '\n'.join(lines) + '\n'


def emit_sum_r7Bound_le(data) -> str:
    # The full sum is 1950990333/100000000000 which is < 1951/100000 = 0.01951.
    total = sum(K_w for _, _, _, _, _, K_w in data)
    return f'''
-- The sum of `r7Bound i` over all 126 indices is ≤ `bchR7UniformConstant`.
-- Strategy: convert `Finset.sum (Fin 126)` to `Finset.sum (Finset.range 126)` via
-- `Fin.sum_univ_eq_sum_range`, then reduce 126 times via `Finset.sum_range_succ`.
-- `r7BoundN` reduces nicely on concrete `Nat` literals, so the final expression
-- is a sum of 126 concrete rationals that `norm_num` can verify.
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 2000 in
private lemma sum_r7Bound_le : (∑ i : Fin 126, r7Bound i) ≤ bchR7UniformConstant := by
  unfold bchR7UniformConstant r7Bound
  rw [Fin.sum_univ_eq_sum_range (fun k => r7BoundN k)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r7BoundN, zero_add]
  norm_num
'''


def emit_norm_suzuki5_R7_le_bchR7Bound() -> str:
    return '''
/-- **The headline R₇ norm bound at Suzuki p**: under the Childs-word
expansion at Suzuki `p`, `‖suzuki5_R7 A B suzukiP‖ ≤ bchR7Bound A B
= 0.01951 · max(‖A‖, ‖B‖)^7`.

Proof: triangle inequality on the 126-term Finset.sum + per-i bound
`r7Term_norm_le` + final `sum_r7Bound_le`. -/
theorem norm_suzuki5_R7_le_bchR7Bound (A B : 𝔸) :
    ‖suzuki5_R7 A B suzukiP‖ ≤ bchR7Bound A B := by
  unfold suzuki5_R7 bchR7Bound
  set m := max ‖A‖ ‖B‖ with hm_def
  have hA : ‖A‖ ≤ m := le_max_left _ _
  have hB : ‖B‖ ≤ m := le_max_right _ _
  have hm_nn : 0 ≤ m := le_max_of_le_left (norm_nonneg _)
  calc ‖∑ i : Fin 126, r7Term A B suzukiP i‖
      ≤ ∑ i : Fin 126, ‖r7Term A B suzukiP i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 126, r7Bound i * m^7 :=
        Finset.sum_le_sum (fun i _ => r7Term_norm_le A B m hA hB hm_nn i)
    _ = (∑ i : Fin 126, r7Bound i) * m^7 := by
        rw [← Finset.sum_mul]
    _ ≤ bchR7UniformConstant * m^7 := by
        have := sum_r7Bound_le
        have hm7_nn : 0 ≤ m^7 := pow_nonneg hm_nn 7
        nlinarith
'''


def main():
    import os
    data_path = os.path.join(os.path.dirname(__file__), 'r7_data.txt')
    data = load_data(data_path)
    assert len(data) == 126, f"Expected 126 entries, got {len(data)}"

    print(emit_helper())
    print(emit_r7Term_def(data))
    print(emit_r7Bound_def(data))
    print(emit_suzuki5_R7_def())
    print(emit_r7Term_norm_le(data))
    print(emit_sum_r7Bound_le(data))
    print(emit_norm_suzuki5_R7_le_bchR7Bound())


if __name__ == "__main__":
    main()
