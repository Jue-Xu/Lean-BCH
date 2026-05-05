# Lean-BCH session 14 starter: sextic_pure_identity Lean port

## Context

Session 13 (2026-04-26 to 2026-04-27) **CAS-verified** the sextic_pure_identity at deg 5:

```
½·W_subst[5] + ⅓·y³_subst[5] - ¼·y⁴_subst[5] + ⅕·y⁵_subst[5] - C₅ = 0
```

(Lean-Trotter `scripts/discover_quintic_identity.py` rev `6d029b6`,
local-only.) This unlocks B1.c discharge via the strategy of computing
deg-5 cancellations in the post-substitution {a, b} polynomial.

This document gives the exact Lean theorem to add to `BCH/Basic.lean`,
with an attempted proof. The proof was DRAFTED but not yet verified
to compile (build was killed mid-run for time reasons).

## Where to insert

In `BCH/Basic.lean`, between line 2758 (end of `quintic_pure_identity`
proof: `noncomm_ring`) and line 2760 (`set_option maxHeartbeats
128000000 in` for `norm_bch_quintic_remainder_le`).

## Theorem statement (with `let` bindings — may need inlining)

```lean
/-! ### Sixth-order BCH: degree-5 cancellation identity (sextic_pure_identity) -/

-- Pure {a, b} ring identity for the degree-5 cancellation of pieceB_sextic.
-- After substituting ea → exp(a), eb → exp(b), the deg-5 part of
--   ½W_H1 + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅
-- vanishes. This identity captures that vanishing as a pure {a, b} ring
-- identity, with explicit polynomial expressions for each substituted piece's
-- deg-5 part.
--
-- T₂ = y_subst[2] = ab + ½a² + ½b² (matches existing P₂ in quintic remainder).
-- T₃ = y_subst[3] = ⅙a³ + ½a²b + ½ab² + ⅙b³.
-- T₄ = y_subst[4] = (1/24)a⁴ + ⅙a³b + ¼a²b² + ⅙ab³ + (1/24)b⁴.
-- z = a + b.
-- W5 = W_subst[5] expressed as: 6 pure deg-5 monomials - (z·T₄ + T₄·z) - (T₂·T₃ + T₃·T₂).
-- y3_5 = y³_subst[5] = z²·T₃ + z·T₃·z + T₃·z² + z·T₂² + T₂·z·T₂ + T₂²·z.
-- y4_5 = y⁴_subst[5] = z³·T₂ + z²·T₂·z + z·T₂·z² + T₂·z³.
-- y5_5 = y⁵_subst[5] = z⁵.
--
-- Identity: ½·W5 + ⅓·y3_5 - ¼·y4_5 + ⅕·z⁵ - bch_quintic_term = 0.
-- Verified by Lean-Trotter/scripts/discover_quintic_identity.py rev 6d029b6.
set_option maxHeartbeats 4000000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem sextic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂)
    let y3_5 : 𝔸 := z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z
    let y4_5 : 𝔸 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3
    (2 : 𝕂)⁻¹ • W5 + (3 : 𝕂)⁻¹ • y3_5 - (4 : 𝕂)⁻¹ • y4_5 + (5 : 𝕂)⁻¹ • z ^ 5
      - bch_quintic_term 𝕂 a b = 0 := by
  -- Multiply by 720 (LCM of 2,3,4,5,6,12,24,60 = 60; ×720 covers all C₅ denominators).
  have h720ne : (720 : 𝕂) ≠ 0 := by exact_mod_cast (show (720 : ℕ) ≠ 0 by norm_num)
  have hinj : Function.Injective ((720 : 𝕂) • · : 𝔸 → 𝔸) := by
    intro x₀ y₀ hxy; have := congrArg ((720 : 𝕂)⁻¹ • ·) hxy
    simp only [smul_smul, inv_mul_cancel₀ h720ne, one_smul] at this; exact this
  apply hinj; simp only [smul_zero]
  -- IMPORTANT: may need `dsimp only` here to unfold the `let` bindings before simp.
  unfold bch_quintic_term bch_quintic_group_1 bch_quintic_group_4
    bch_quintic_group_6 bch_quintic_group_24
  -- Expand powers first so scalar smuls inside (e.g. T₂^2) get distributed.
  simp only [pow_succ, pow_zero, one_mul]
  -- Distribute scalars through all algebraic operations.
  simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul]
  -- Clear scalar products. ×720 covers all denominators 2, 3, 4, 5, 6, 12, 24, 60, 720.
  simp only [mul_assoc,
    mul_inv_cancel₀ (show (2 : 𝕂) ≠ 0 from two_ne_zero),
    inv_mul_cancel₀ (show (2 : 𝕂) ≠ 0 from two_ne_zero),
    mul_inv_cancel₀ h720ne,
    show (720 : 𝕂) * (2 : 𝕂)⁻¹ = 360 from by norm_num,
    show (720 : 𝕂) * (3 : 𝕂)⁻¹ = 240 from by norm_num,
    show (720 : 𝕂) * (4 : 𝕂)⁻¹ = 180 from by norm_num,
    show (720 : 𝕂) * (5 : 𝕂)⁻¹ = 144 from by norm_num,
    show (720 : 𝕂) * (6 : 𝕂)⁻¹ = 120 from by norm_num,
    show (720 : 𝕂) * (12 : 𝕂)⁻¹ = 60 from by norm_num,
    show (720 : 𝕂) * (24 : 𝕂)⁻¹ = 30 from by norm_num,
    show (720 : 𝕂) * (60 : 𝕂)⁻¹ = 12 from by norm_num,
    show (720 : 𝕂) * (720 : 𝕂)⁻¹ = 1 from mul_inv_cancel₀ h720ne,
    -- Two-level nesting
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 180 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹) = 120 from by norm_num,
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 120 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (4 : 𝕂)⁻¹) = 90 from by norm_num,
    show (720 : 𝕂) * ((4 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 90 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (24 : 𝕂)⁻¹) = 15 from by norm_num,
    show (720 : 𝕂) * ((24 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 15 from by norm_num,
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹) = 40 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹) = 40 from by norm_num,
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * (4 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((4 : 𝕂)⁻¹ * (3 : 𝕂)⁻¹) = 60 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (12 : 𝕂)⁻¹) = 30 from by norm_num,
    show (720 : 𝕂) * ((12 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 30 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * (60 : 𝕂)⁻¹) = 6 from by norm_num,
    show (720 : 𝕂) * ((60 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹) = 6 from by norm_num,
    -- Three-level nesting
    show (720 : 𝕂) * ((3 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 60 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 90 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (6 : 𝕂)⁻¹)) = 30 from by norm_num,
    show (720 : 𝕂) * ((2 : 𝕂)⁻¹ * ((6 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 30 from by norm_num,
    show (720 : 𝕂) * ((6 : 𝕂)⁻¹ * ((2 : 𝕂)⁻¹ * (2 : 𝕂)⁻¹)) = 30 from by norm_num,
    one_smul, mul_one]
  simp only [ofNat_smul_eq_nsmul (R := 𝕂)]
  noncomm_ring
```

## Potential issues & alternative formulations

### Issue 1: `let` bindings may not unfold

In Lean 4, `let x := e` in theorem statements creates a let-bound term.
The `apply hinj; simp only [smul_zero]` step should reduce, but
subsequent `simp only` lemmas may not unfold the lets.

**Fix**: Add `dsimp only` after `apply hinj; simp only [smul_zero]` to
force unfolding of all `let` bindings before the main simplification:

```lean
  apply hinj; simp only [smul_zero]
  dsimp only  -- Unfold all let bindings explicitly.
  unfold bch_quintic_term ...
```

### Issue 2: Inline alternative (longer but more reliable)

If `let` bindings cause issues, inline everything (matching
quintic_pure_identity's pattern at line 2705):

```lean
private theorem sextic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    -- ½·W5
    (2 : 𝕂)⁻¹ • ((60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 + ...) +
    -- ⅓·y3_5
    (3 : 𝕂)⁻¹ • ((a + b) ^ 2 * ((6 : 𝕂)⁻¹ • a ^ 3 + ... ) + ...) +
    ...
```

This is very long (~80 lines for the statement alone) but has no
`let`-binding worries.

### Issue 3: noncomm_ring timeout

After ×720 scalar clearing, the integer-coef identity has ~150
products at deg 5. noncomm_ring expands into ~32 monomials in {a, b}
and verifies each coefficient.

If timeout: bump `maxHeartbeats` further (e.g., 8 billion). Or split
the identity into 2-3 smaller `have` statements:
- `hW5_alt`: equivalent reformulation of W5 piece.
- `hy3_5_alt`: equivalent reformulation of y3_5 piece.
- Final composition is easier.

### Issue 4: Missing simp lemmas

If specific scalar combinations aren't in the simp list, noncomm_ring
may fail with "scalar didn't simplify to integer". Add lemmas as
needed for `(720) * (n⁻¹ * m⁻¹)` patterns.

## Downstream usage

After sextic_pure_identity is proved, build `norm_bch_sextic_remainder_le`
in the same file (analog of `norm_bch_quintic_remainder_le` at line
2760+, ~800 lines). The structure parallels the existing quintic
remainder proof but uses sextic_pure_identity for deg-5 cancellation.

After that, extend the cubic template `norm_symmetric_bch_cubic_sub_poly_le`
(line ~3798) to give B1.c (`norm_symmetric_bch_quintic_sub_poly_le`),
~400-600 additional lines.

## Build/verify recipe

```bash
cd ~/Documents/Claude/Projects/Lean-BCH
git checkout main
git pull
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build  # baseline, should pass
# Apply the patch from this file to BCH/Basic.lean
lake build  # verify identity compiles
```

If lake build hangs at sextic_pure_identity for >5 minutes, suspect
noncomm_ring timeout — kill, bump heartbeats or split.

## Estimate

- Lean port of sextic_pure_identity: 1-2 hours (with iteration).
- norm_bch_sextic_remainder_le: 1-2 days (~800 lines paralleling
  existing quintic remainder).
- B1.c main theorem: 1 day (~400-600 lines).
- B1.d trivial wrapper: 1 hour.
- Total to discharge B1.c axiom: ~3-4 days.
