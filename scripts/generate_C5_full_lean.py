#!/usr/bin/env python3
"""
Generate the complete Lean theorem code for the C5_diff_residual discharge.
"""
import sys
sys.path.insert(0, '/Users/jue/Documents/Claude/Projects/Lean-BCH/scripts')
from compute_C5_diff_LinResidual import LinResidual, by_degree

# Use a single common denominator for all terms (LCM of 92160, 184320, 368640 = 368640).
SINGLE_DENOM = 368640
common_denoms = {7: SINGLE_DENOM, 8: SINGLE_DENOM, 9: SINGLE_DENOM}

def word_to_lean(word):
    return ' * '.join(word)

# Generate the explicit polynomial expression
# Format: each line is `(num / denom : 𝕂) • (word)` joined with ` +\n`

# Build lists of terms per degree
all_terms_per_deg = {}
for deg in [7, 8, 9]:
    if deg not in by_degree:
        continue
    denom = common_denoms[deg]
    terms = []
    for word, coef in sorted(by_degree[deg]):
        num = coef * denom
        if num == 0:
            continue
        word_str = word_to_lean(word)
        terms.append(f"({num} / {denom} : 𝕂) • ({word_str})")
    all_terms_per_deg[deg] = terms

# Print the polynomial expression as Lean code.
# Format: parenthesized sum, with comments separating per-degree groups.
print("    (")
for i, deg in enumerate([7, 8, 9]):
    if deg not in all_terms_per_deg:
        continue
    terms = all_terms_per_deg[deg]
    if i > 0:
        print(" +")
    print(f"     -- Degree {deg} ({len(terms)} terms):")
    for j, term in enumerate(terms):
        if j > 0:
            print(" +")
        print(f"     {term}", end='')
print()
print("    )")

# Compute total |coef|·s^7-equivalent for the bound.
total_abs_7 = sum(abs(c) for w, c in by_degree.get(7, []))
total_abs_8 = sum(abs(c) for w, c in by_degree.get(8, []))
total_abs_9 = sum(abs(c) for w, c in by_degree.get(9, []))

# Bound LinResidual ≤ (total_abs_7 + total_abs_8/4 + total_abs_9/16) · s^7 for s ≤ 1/4.
total_bound_in_s7 = total_abs_7 + total_abs_8 / 4 + total_abs_9 / 16

print()
print(f"-- Norm bound on the deg-7+ residual:")
print(f"-- Sum of |coef|·s^d for d ∈ {{7,8,9}}, with s^d ≤ s^7 · (1/4)^(d-7):")
print(f"-- = {total_abs_7} · s^7 + {total_abs_8} · s^8 + {total_abs_9} · s^9")
print(f"-- ≤ ({total_abs_7} + {total_abs_8}/4 + {total_abs_9}/16) · s^7 (for s ≤ 1/4)")
print(f"-- = {total_bound_in_s7} · s^7")
print(f"-- ≈ {float(total_bound_in_s7):.6f} · s^7")

# Also output: total absolute scaled-integer-coefficient sum (for the bound).
# Each scaled coef is num_i (with denom 368640).
# For the bound: Σ |num_i| · s^d_i / 368640.
print()
print("-- Computing absolute scaled coefs:")
total_abs_scaled_7 = sum(abs(c * SINGLE_DENOM) for w, c in by_degree.get(7, []))
total_abs_scaled_8 = sum(abs(c * SINGLE_DENOM) for w, c in by_degree.get(8, []))
total_abs_scaled_9 = sum(abs(c * SINGLE_DENOM) for w, c in by_degree.get(9, []))
print(f"-- Σ |scaled coef_i| at deg 7 = {total_abs_scaled_7}")
print(f"-- Σ |scaled coef_i| at deg 8 = {total_abs_scaled_8}")
print(f"-- Σ |scaled coef_i| at deg 9 = {total_abs_scaled_9}")
print(f"-- Total scaled bound: {total_abs_scaled_7} + {total_abs_scaled_8}/4 + {total_abs_scaled_9}/16 = {total_abs_scaled_7 + total_abs_scaled_8 // 4 + total_abs_scaled_9 // 16}")
print(f"-- = scaled bound / {SINGLE_DENOM}")
