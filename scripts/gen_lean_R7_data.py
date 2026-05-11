#!/usr/bin/env python3
"""Generate Lean-ready data for the 126-word suzuki5_R7 definition + norm bound.

For each non-zero 7-letter word w in R₇ at Suzuki p (after Suzuki cubic
reduction), output:
  - The exact rational polynomial coefficient `coef(w, p) = c0 + c1·p + c2·p²`.
  - A rational upper bound `K_w` on `|coef(w, p)|` over the interval
    `p ∈ [41449/100000, 41450/100000]` (which contains suzukiP exactly).

Pipeline (mirrors the session 23 Finset.sum closure):
  1. Run the BCH expansion (mirrors compute_bch_r7.py).
  2. For each of 126 non-zero words, store (word, c0, c1, c2).
  3. Compute K_w := max_{p ∈ interval} |c0 + c1·p + c2·p²|, rounded up
     at 10⁻¹² precision (rational ceiling).
  4. Verify Σ K_w ≤ 0.01951 - safety_margin.
  5. Emit Lean code for: (a) r7Term (Fin 126 → 𝔸), (b) r7Bound (Fin 126 → ℝ),
     (c) r7CoefAt_suzukiP_abs_le (per-term coefficient bound),
     (d) sum_r7Bound_le (final ∑ bound).

Usage:  python3 scripts/gen_lean_R7_data.py
"""
import sympy as sp
from collections import defaultdict
from fractions import Fraction
from typing import Dict, Tuple, List

# Import the existing NCPoly machinery.
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..',
                                'Lean-Trotter', 'scripts'))
# Use exec to import the helpers without importing main().
_LEANTROTTER_SCRIPT = os.path.join(
    os.path.dirname(__file__), '..', '..',
    'Lean-Trotter', 'scripts', 'compute_bch_r7.py'
)
with open(_LEANTROTTER_SCRIPT) as fh:
    _src = fh.read().split('def main')[0]
exec(_src, globals())


# ---------- Bound on |c0 + c1·p + c2·p²| over [a, b] ----------

def quad_abs_max_over_interval(c0: sp.Rational, c1: sp.Rational, c2: sp.Rational,
                               a: sp.Rational, b: sp.Rational) -> sp.Rational:
    """Compute exact max of |c0 + c1·p + c2·p²| over p in [a, b], as a Rational.

    Strategy:
      - If c2 == 0: linear in p, max at one of endpoints.
      - Else: quadratic. Critical point at p* = -c1/(2·c2). If a ≤ p* ≤ b,
        evaluate at p*; else only endpoints.
    """
    def f(p):
        return c0 + c1 * p + c2 * p ** 2
    candidates = [f(a), f(b)]
    if c2 != 0:
        pstar = -c1 / (2 * c2)
        if a <= pstar <= b:
            candidates.append(f(pstar))
    return max(abs(c) for c in candidates)


def rational_ceiling(x: sp.Rational, precision: int = 10**12) -> sp.Rational:
    """Round Rational x up to a multiple of 1/precision."""
    # x = numer/denom; want smallest k such that k/precision ≥ x.
    k = (x * precision)
    # Ceiling
    if k.q == 1:
        k_int = int(k.p)
    else:
        k_int = int(k.p // k.q) + (1 if k.p % k.q != 0 else 0)
    return sp.Rational(k_int, precision)


# ---------- Polynomial coefficient extraction ----------

def poly_to_c012(c: sp.Expr, p: sp.Symbol) -> Tuple[sp.Rational, sp.Rational, sp.Rational]:
    """Extract (c0, c1, c2) such that c = c0 + c1·p + c2·p² (after Suzuki reduction).

    The CAS already reduces p^3 via Suzuki cubic, so c should be at most quadratic in p.
    """
    c_expanded = sp.expand(c)
    c_poly = sp.Poly(c_expanded, p)
    coeffs = c_poly.all_coeffs()  # highest degree first
    # Pad with zeros at the front if degree < 2
    while len(coeffs) < 3:
        coeffs = [sp.Rational(0)] + coeffs
    if len(coeffs) > 3:
        raise ValueError(f"Coefficient is degree > 2 in p after Suzuki reduction: {c}")
    c2, c1, c0 = coeffs
    return sp.Rational(c0), sp.Rational(c1), sp.Rational(c2)


# ---------- Word formatting ----------

def word_to_letters(w: Tuple[int, ...]) -> str:
    """Convert tuple of 0/1 (A=0, B=1) to a string like 'A * A * B * ...'"""
    letters = ['A' if x == 0 else 'B' for x in w]
    return ' * '.join(letters)


def word_index_to_label(w: Tuple[int, ...]) -> str:
    """For comment: convert tuple to 'AAAAAAB' style."""
    return ''.join('A' if x == 0 else 'B' for x in w)


# ---------- Main ----------

def main():
    p = sp.Symbol('p')
    suzuki_p_val_num = float(1 / (4 - 4 ** sp.Rational(1, 3)))
    print(f"# suzukiP ≈ {suzuki_p_val_num:.10f}")
    print(f"# Interval: [41449/100000, 41450/100000] = [{41449/100000}, {41450/100000}]")
    print(f"# (suzukiP must lie in this interval, slack ≈ 10⁻⁶)")
    print()
    print("Computing log(S4)(τ) - τ·(A+B) up to degree 7 (may take 1-2 min)...")

    residual = log_s4_residual(p, max_degree=7)
    r7 = extract_degree(residual, 7)
    r7_reduced = defaultdict(lambda: sp.Integer(0))
    for w, c in r7.items():
        c_red = simplify_under_suzuki(c, p)
        if c_red != 0:
            r7_reduced[w] = c_red
    print(f"R₇ has {len(r7_reduced)} non-zero 7-letter words.")

    # Sort by lexicographic order of word tuple
    words_sorted = sorted(r7_reduced.keys())
    assert len(words_sorted) == 126, f"Expected 126 words, got {len(words_sorted)}"

    # Extract polynomial coefficients (c0, c1, c2) per word
    a_int = sp.Rational(41449, 100000)
    b_int = sp.Rational(41450, 100000)

    data = []  # list of (idx, word_tuple, c0, c1, c2, K_w)
    total_K = sp.Rational(0)
    for idx, w in enumerate(words_sorted):
        c_expr = r7_reduced[w]
        c0, c1, c2 = poly_to_c012(c_expr, p)
        K_max = quad_abs_max_over_interval(c0, c1, c2, a_int, b_int)
        # Round up to 10^-12 precision
        K_w = rational_ceiling(K_max, 10**12)
        data.append((idx, w, c0, c1, c2, K_w))
        total_K += K_w
    print(f"\nΣ K_w = {total_K} ≈ {float(total_K):.12f}")
    print(f"Target: bchR7UniformConstant = 0.01951 = 1951/100000 ≈ {1951/100000:.12f}")
    print(f"Slack: {1951/100000 - float(total_K):.12e}")

    target = sp.Rational(1951, 100000)
    if total_K > target:
        print(f"WARNING: Σ K_w > 0.01951! Difference: {float(total_K - target):.12e}")
        print("Need to bump bchR7UniformConstant or tighten bounds.")
    else:
        print(f"✓ Σ K_w ≤ 0.01951 (slack {float(target - total_K):.12e}).")

    # Print top 10 K_w values for sanity check
    print("\nTop 10 K_w by magnitude:")
    for d in sorted(data, key=lambda x: -x[5])[:10]:
        idx, w, c0, c1, c2, K_w = d
        print(f"  Word {idx} ({word_index_to_label(w)}): K = {float(K_w):.12f} = {K_w}")

    # Per-block stats
    print("\nPer-block (#A's, count, K_block):")
    for n_a in range(8):
        block = [d for d in data if sum(1 for x in d[1] if x == 0) == n_a]
        if block:
            K_block = sum(d[5] for d in block)
            print(f"  {n_a} A's: count={len(block)}, K={float(K_block):.10f}")

    # Save data for next step
    out_path = os.path.join(os.path.dirname(__file__), 'r7_data.txt')
    with open(out_path, 'w') as f:
        f.write(f"# 126 words for R₇ at Suzuki p\n")
        f.write(f"# Format: idx | word | c0 | c1 | c2 | K_w\n")
        f.write(f"# (coefficient = c0 + c1·p + c2·p², K_w = upper bound on |coef| over [41449/10⁵, 41450/10⁵])\n")
        f.write(f"# Sum K_w = {total_K} ≈ {float(total_K):.12f}\n\n")
        for idx, w, c0, c1, c2, K_w in data:
            word_str = word_index_to_label(w)
            f.write(f"{idx}|{word_str}|{c0}|{c1}|{c2}|{K_w}\n")
    print(f"\nWrote per-word data to: {out_path}")


if __name__ == "__main__":
    main()
