#!/usr/bin/env python3
"""
Integrate the generated Finset.sum-based norm bound proof into SymmetricQuintic.lean.

Replaces the `norm_C5_LinResidual_polynomial_le` axiom (and its leading comment)
with the generated helpers + linResTerm + linResBound + identity + per-term + sum bound + main theorem.
"""

import subprocess

# 1. Read generated insertion content.
with open('/tmp/gen_lean_output.lean', 'r') as f:
    generated = f.read()

# 2. Read the current SymmetricQuintic.lean.
filepath = '/Users/jue/Documents/Claude/Projects/Lean-BCH/BCH/SymmetricQuintic.lean'
with open(filepath, 'r') as f:
    src = f.read()

# 3. Match the axiom block (comments + declaration).
axiom_block = """-- The polynomial bound (small private axiom; ‖polynomial‖ ≤ 1·s^7 for s ≤ 1/4).
-- Σ|coef| values verified by CAS at scripts/compute_C5_diff_LinResidual.py:
--   deg-7 terms: Σ|c|/d ≈ 0.0207
--   deg-8 terms: Σ|c|/d ≈ 0.0052
--   deg-9 terms: Σ|c|/d ≈ 0.000694
-- Total ≤ 0.0221·s^7 (for s ≤ 1/4) ≪ 1·s^7.
-- Formal Lean proof of this bound is mechanical but extremely verbose
-- (~3000 lines for 205 per-term `gcongr`+chain `norm_add_le`); kept as
-- focused private axiom for tractability.
private axiom norm_C5_LinResidual_polynomial_le
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖C5_LinResidual_polynomial 𝕂 a b‖ ≤ 1 * (‖a‖ + ‖b‖) ^ 7"""

assert axiom_block in src, "Axiom block not found in source!"

# 4. Replace with generated content (without the type class params since we're in a variable section).
new_block = generated.strip()

new_src = src.replace(axiom_block, new_block)

with open(filepath, 'w') as f:
    f.write(new_src)

print(f"Replaced axiom block ({len(axiom_block)} chars) with new content ({len(new_block)} chars).")
print(f"New file size: {len(new_src)} chars, {new_src.count(chr(10))} lines.")
