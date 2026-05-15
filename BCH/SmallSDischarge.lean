/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH Small-s Discharge: pure identities, decompositions, and remainder bounds

This file extends `BCH.Basic` with the algebraic infrastructure used for the
small-s discharge of the BCH remainder bounds:

* Pure ring identities (`quintic_pure_identity`, `sextic_pure_identity`,
  `septic_pure_identity`, `octic_pure_identity`, `nonic_pure_identity`).
* Power telescoping and y_k - z_k decompositions.
* I₁ / I₂ residual decompositions and R + T₅ + ... cancellation identities.
* T_k norm bounds and P²/PzP/P³-residual cluster bounds.
* `pieceB_*_decomp` central decompositions.
* `norm_bch_septic_remainder_le` (public) and `norm_bch_octic_remainder_le`
  (public, axiom-gated for the small-s case).
* Symmetric BCH cubic/quintic/septic polynomial-form definitions and norm bounds.

Split from `BCH/Basic.lean` (formerly a single 22 000-line file) to enable
parallel compilation: `BCH.Basic` and `BCH.SmallSDischarge` build independently
once dependencies are satisfied. -/

import BCH.Basic
import Mathlib.Algebra.Lie.OfAssociative

namespace BCH

noncomputable section

open scoped Nat
open NormedSpace Topology Finset

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ### Quintic algebraic identity for BCH -/

-- The degree-4 pure identity: verified by noncomm_ring at Ring level (no 𝕂 needed).
-- After ×24 clearing: the Y₄-½(Y₁Y₃+Y₂²+Y₃Y₁)+⅓(Y₁²Y₂+...)-¼Y₁⁴+C₄ = 0.
omit [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
theorem quintic_pure_identity_cleared (a b : 𝔸) :
    -- 24×[Y₄-½(Y₁Y₃+Y₂²+Y₃Y₁)+⅓(Y₁²Y₂+Y₁Y₂Y₁+Y₂Y₁²)-¼Y₁⁴+C₄] = 0
    -- z := a+b, U := 2ab+a²+b² (= 2Y₂)
    (a ^ 4 + 4 • (a ^ 3 * b) + 6 • (a ^ 2 * b ^ 2) + 4 • (a * b ^ 3) + b ^ 4) -
    2 • ((a + b) * (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) +
         (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) * (a + b)) -
    3 • ((2 • (a * b) + a ^ 2 + b ^ 2) * (2 • (a * b) + a ^ 2 + b ^ 2)) +
    4 • ((a + b) ^ 2 * (2 • (a * b) + a ^ 2 + b ^ 2) +
         (a + b) * (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) +
         (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) ^ 2) -
    6 • (a + b) ^ 4 +
    (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
     (a * (a * b - b * a) - (a * b - b * a) * a) * b) = 0 := by
  noncomm_ring

-- 𝕂-scalar version of the degree-4 cancellation identity.
-- Same identity as quintic_pure_identity_cleared, but stated with 𝕂-scalars
-- so it can be used in the NormedAlgebra 𝕂 𝔸 context.
-- Proved by ×24 scalar clearing (with triple-nesting lemmas) + noncomm_ring.
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private theorem quintic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
    (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
    (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
    (2 : 𝕂)⁻¹ • ((a + b) * ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) +
      ((6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)) * (a + b)) -
    (2 : 𝕂)⁻¹ • (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) ^ 2 +
    (3 : 𝕂)⁻¹ • ((a + b) ^ 2 * (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) +
      (a + b) * (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) * (a + b) +
      (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) * (a + b) ^ 2) -
    (4 : 𝕂)⁻¹ • (a + b) ^ 4 - bch_quartic_term 𝕂 a b = 0 := by
  unfold bch_quartic_term
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-! ### Sixth-order BCH: degree-5 cancellation identity (sextic_pure_identity) -/

-- Pure {a, b} ring identity for the degree-5 cancellation of pieceB_sextic.
-- After substituting ea → exp(a), eb → exp(b), the deg-5 part of
--   ½W_H1 + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅
-- vanishes. This identity expresses that vanishing as an explicit pure
-- {a, b} ring identity.
--
-- Notation (for readability):
--   z  = a + b
--   T₂ = ab + ½a² + ½b²        (= y_subst[2])
--   T₃ = ⅙a³ + ½a²b + ½ab² + ⅙b³  (= y_subst[3])
--   T₄ = (1/24)a⁴ + ⅙a³b + ¼a²b² + ⅙ab³ + (1/24)b⁴  (= y_subst[4])
--
--   W5 = (60)⁻¹·a⁵ + (60)⁻¹·b⁵ + (12)⁻¹·ab⁴ + (12)⁻¹·a⁴b
--      + (6)⁻¹·a²b³ + (6)⁻¹·a³b² - (z·T₄ + T₄·z) - (T₂·T₃ + T₃·T₂)
--   y3_5 = z²·T₃ + z·T₃·z + T₃·z² + z·T₂² + T₂·z·T₂ + T₂²·z
--   y4_5 = z³·T₂ + z²·T₂·z + z·T₂·z² + T₂·z³
--   y5_5 = z⁵
--
-- Identity: ½·W5 + ⅓·y3_5 - ¼·y4_5 + ⅕·z⁵ - bch_quintic_term = 0.
-- Verified by Lean-Trotter/scripts/discover_quintic_identity.py rev 6d029b6.
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
  intro z T₂ T₃ T₄ W5 y3_5 y4_5
  show _ = (0 : 𝔸)
  simp only [show z = a + b from rfl,
    show T₂ = a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2 from rfl,
    show T₃ = (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 from rfl,
    show T₄ = (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4 from rfl,
    show W5 = (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂) from rfl,
    show y3_5 = z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z from rfl,
    show y4_5 = z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3 from rfl]
  unfold bch_quintic_term bch_quintic_group_1 bch_quintic_group_4
    bch_quintic_group_6 bch_quintic_group_24
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-! ### Seventh-order BCH: degree-6 cancellation identity (septic_pure_identity)

Analog of `sextic_pure_identity` at one degree higher. After substituting
ea → exp(a), eb → exp(b), the deg-6 part of
  `½W_H1 + ⅓y³ - ¼y⁴ + ⅕y⁵ - ⅙y⁶ - C₃ - C₄ - C₅ - C₆`
vanishes. This identity expresses that vanishing as an explicit pure {a, b}
ring identity, with the deg-6 leading term `bch_sextic_term`.

Notation:
- `z = a + b`
- `T_k = y_dk` for k = 2..5 (deg-k of `y = exp(a)·exp(b) - 1`)
- `W6 = 2·y_d6 - (y²)_d6`
- `y3_6 = (y³)_d6`, `y4_6 = (y⁴)_d6`, `y5_6 = (y⁵)_d6`, `y6_6 = z⁶`

CAS-verified (`derive_septic_lean.py`): `½W6 + ⅓y3_6 - ¼y4_6 + ⅕y5_6 - ⅙z⁶ - bch_sextic_term = 0`. -/

set_option maxHeartbeats 16000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
theorem septic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    -- W6 = 2·y_d6 - (y²)_d6, where (y²)_d6 = z·T_5 + T_2·T_4 + T_3·T_3 + T_4·T_2 + T_5·z
    let W6 : 𝔸 := (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
        (360 : 𝕂)⁻¹ • b ^ 6 -
        (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z)
    -- y3_6 = (y³)_d6: 10 terms from k+l+m=6, each ≥ 1
    -- partitions: (1,1,4) perms, (1,2,3) perms, (2,2,2)
    let y3_6 : 𝔸 := z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
        z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
        T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
        T₂ ^ 3
    -- y4_6 = (y⁴)_d6: 10 terms from k+l+m+n=6, each ≥ 1
    -- partitions: (1,1,1,3) 4 perms, (1,1,2,2) 6 perms
    let y4_6 : 𝔸 := z ^ 3 * T₃ + z ^ 2 * T₃ * z + z * T₃ * z ^ 2 + T₃ * z ^ 3 +
        z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
        T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2
    -- y5_6 = (y⁵)_d6: 5 terms from (1,1,1,1,2) perms
    let y5_6 : 𝔸 := z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
        z * T₂ * z ^ 3 + T₂ * z ^ 4
    -- (y⁶)_d6 = z⁶ (only (1,1,1,1,1,1))
    (2 : 𝕂)⁻¹ • W6 + (3 : 𝕂)⁻¹ • y3_6 - (4 : 𝕂)⁻¹ • y4_6 +
      (5 : 𝕂)⁻¹ • y5_6 - (6 : 𝕂)⁻¹ • z ^ 6 - bch_sextic_term 𝕂 a b = 0 := by
  intro z T₂ T₃ T₄ T₅ W6 y3_6 y4_6 y5_6
  show _ = (0 : 𝔸)
  simp only [show z = a + b from rfl,
    show T₂ = a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2 from rfl,
    show T₃ = (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 from rfl,
    show T₄ = (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4 from rfl,
    show T₅ = (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5 from rfl,
    show W6 = (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
        (360 : 𝕂)⁻¹ • b ^ 6 -
        (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) from rfl,
    show y3_6 = z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
        z * T₂ * T₃ + z * T₃ * T₂ + T₂ * z * T₃ +
        T₂ * T₃ * z + T₃ * z * T₂ + T₃ * T₂ * z +
        T₂ ^ 3 from rfl,
    show y4_6 = z ^ 3 * T₃ + z ^ 2 * T₃ * z + z * T₃ * z ^ 2 + T₃ * z ^ 3 +
        z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
        T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2 from rfl,
    show y5_6 = z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
        z * T₂ * z ^ 3 + T₂ * z ^ 4 from rfl]
  unfold bch_sextic_term
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

-- ===================================
-- octic_pure_identity (deg-7 cancellation)
-- Generated by scripts/gen_octic_pure_identity.py
-- ===================================

set_option maxHeartbeats 64000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Eighth-order BCH: degree-7 cancellation identity (octic_pure_identity)**

Analog of `septic_pure_identity` at one degree higher. After substituting
ea → exp(a), eb → exp(b), the deg-7 part of
  `½W_H1 + ⅓y³ − ¼y⁴ + ⅕y⁵ − ⅙y⁶ + ⅐y⁷ − C₃ − C₄ − C₅ − C₆ − C₇`
vanishes. This identity expresses that vanishing as an explicit pure {a, b}
ring identity, with the deg-7 leading term `bch_septic_term`.

Notation:
- `z = a + b`
- `T_k = y_dk` for k = 2..6 (deg-k of `y = exp(a)·exp(b) − 1`)
- `W7 = 2·y_d7 − (y²)_d7`
- `y3_7 = (y³)_d7`, `y4_7 = (y⁴)_d7`, `y5_7 = (y⁵)_d7`,
  `y6_7 = (y⁶)_d7`, `(y⁷)_d7 = z⁷`

Foundation for the small-s case of `norm_bch_octic_remainder_le`
(future), the deg-8 analog of `norm_bch_septic_remainder_le`. -/
private theorem octic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let T₆ : 𝔸 := (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6
    -- W7 = 2·y_d7 − (y²)_d7, where (y²)_d7 = z·T_6 + T_2·T_5 + T_3·T_4 + T_4·T_3 + T_5·T_2 + T_6·z
    let W7 : 𝔸 := (2520 : 𝕂)⁻¹ • a ^ 7 + (360 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (120 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (72 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (72 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (120 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (360 : 𝕂)⁻¹ • (a * b ^ 6) + (2520 : 𝕂)⁻¹ • b ^ 7 -
        (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z)
    -- y3_7 = (y³)_d7: 15 terms from k+l+m=7, each ≥ 1
    let y3_7 : 𝔸 :=
        z * z * T₅
        + z * T₂ * T₄
        + z * T₃ * T₃
        + z * T₄ * T₂
        + z * T₅ * z
        + T₂ * z * T₄
        + T₂ * T₂ * T₃
        + T₂ * T₃ * T₂
        + T₂ * T₄ * z
        + T₃ * z * T₃
        + T₃ * T₂ * T₂
        + T₃ * T₃ * z
        + T₄ * z * T₂
        + T₄ * T₂ * z
        + T₅ * z * z
    -- y4_7 = (y⁴)_d7: 20 terms from k_1+k_2+k_3+k_4=7, each ≥ 1
    let y4_7 : 𝔸 :=
        z * z * z * T₄
        + z * z * T₂ * T₃
        + z * z * T₃ * T₂
        + z * z * T₄ * z
        + z * T₂ * z * T₃
        + z * T₂ * T₂ * T₂
        + z * T₂ * T₃ * z
        + z * T₃ * z * T₂
        + z * T₃ * T₂ * z
        + z * T₄ * z * z
        + T₂ * z * z * T₃
        + T₂ * z * T₂ * T₂
        + T₂ * z * T₃ * z
        + T₂ * T₂ * z * T₂
        + T₂ * T₂ * T₂ * z
        + T₂ * T₃ * z * z
        + T₃ * z * z * T₂
        + T₃ * z * T₂ * z
        + T₃ * T₂ * z * z
        + T₄ * z * z * z
    -- y5_7 = (y⁵)_d7: 15 terms from k_1+...+k_5=7, each ≥ 1
    let y5_7 : 𝔸 :=
        z * z * z * z * T₃
        + z * z * z * T₂ * T₂
        + z * z * z * T₃ * z
        + z * z * T₂ * z * T₂
        + z * z * T₂ * T₂ * z
        + z * z * T₃ * z * z
        + z * T₂ * z * z * T₂
        + z * T₂ * z * T₂ * z
        + z * T₂ * T₂ * z * z
        + z * T₃ * z * z * z
        + T₂ * z * z * z * T₂
        + T₂ * z * z * T₂ * z
        + T₂ * z * T₂ * z * z
        + T₂ * T₂ * z * z * z
        + T₃ * z * z * z * z
    -- y6_7 = (y⁶)_d7: 6 terms (single T_2 among 5 z's)
    let y6_7 : 𝔸 :=
        z * z * z * z * z * T₂
        + z * z * z * z * T₂ * z
        + z * z * z * T₂ * z * z
        + z * z * T₂ * z * z * z
        + z * T₂ * z * z * z * z
        + T₂ * z * z * z * z * z
    -- (y⁷)_d7 = z⁷ (only (1,1,1,1,1,1,1))
    (2 : 𝕂)⁻¹ • W7 + (3 : 𝕂)⁻¹ • y3_7 - (4 : 𝕂)⁻¹ • y4_7 +
      (5 : 𝕂)⁻¹ • y5_7 - (6 : 𝕂)⁻¹ • y6_7 + (7 : 𝕂)⁻¹ • z ^ 7 -
      bch_septic_term 𝕂 a b = 0 := by
  intro z T₂ T₃ T₄ T₅ T₆ W7 y3_7 y4_7 y5_7 y6_7
  show _ = (0 : 𝔸)
  simp only [show z = a + b from rfl,
    show T₂ = a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2 from rfl,
    show T₃ = (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 from rfl,
    show T₄ = (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4 from rfl,
    show T₅ = (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5 from rfl,
    show T₆ = (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6 from rfl,
    show W7 = (2520 : 𝕂)⁻¹ • a ^ 7 + (360 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (120 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (72 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (72 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (120 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (360 : 𝕂)⁻¹ • (a * b ^ 6) + (2520 : 𝕂)⁻¹ • b ^ 7 -
        (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z) from rfl,
    show y3_7 =
        z * z * T₅
        + z * T₂ * T₄
        + z * T₃ * T₃
        + z * T₄ * T₂
        + z * T₅ * z
        + T₂ * z * T₄
        + T₂ * T₂ * T₃
        + T₂ * T₃ * T₂
        + T₂ * T₄ * z
        + T₃ * z * T₃
        + T₃ * T₂ * T₂
        + T₃ * T₃ * z
        + T₄ * z * T₂
        + T₄ * T₂ * z
        + T₅ * z * z
        from rfl,
    show y4_7 =
        z * z * z * T₄
        + z * z * T₂ * T₃
        + z * z * T₃ * T₂
        + z * z * T₄ * z
        + z * T₂ * z * T₃
        + z * T₂ * T₂ * T₂
        + z * T₂ * T₃ * z
        + z * T₃ * z * T₂
        + z * T₃ * T₂ * z
        + z * T₄ * z * z
        + T₂ * z * z * T₃
        + T₂ * z * T₂ * T₂
        + T₂ * z * T₃ * z
        + T₂ * T₂ * z * T₂
        + T₂ * T₂ * T₂ * z
        + T₂ * T₃ * z * z
        + T₃ * z * z * T₂
        + T₃ * z * T₂ * z
        + T₃ * T₂ * z * z
        + T₄ * z * z * z
        from rfl,
    show y5_7 =
        z * z * z * z * T₃
        + z * z * z * T₂ * T₂
        + z * z * z * T₃ * z
        + z * z * T₂ * z * T₂
        + z * z * T₂ * T₂ * z
        + z * z * T₃ * z * z
        + z * T₂ * z * z * T₂
        + z * T₂ * z * T₂ * z
        + z * T₂ * T₂ * z * z
        + z * T₃ * z * z * z
        + T₂ * z * z * z * T₂
        + T₂ * z * z * T₂ * z
        + T₂ * z * T₂ * z * z
        + T₂ * T₂ * z * z * z
        + T₃ * z * z * z * z
        from rfl,
    show y6_7 =
        z * z * z * z * z * T₂
        + z * z * z * z * T₂ * z
        + z * z * z * T₂ * z * z
        + z * z * T₂ * z * z * z
        + z * T₂ * z * z * z * z
        + T₂ * z * z * z * z * z
        from rfl]
  unfold bch_septic_term
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

-- ===================================
-- nonic_pure_identity (deg-8 cancellation)
-- Generated by scripts/gen_nonic_pure_identity.py
-- ===================================

set_option maxHeartbeats 128000000 in
set_option maxRecDepth 2000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Ninth-order BCH: degree-8 cancellation identity (nonic_pure_identity)**

Analog of `octic_pure_identity` at one degree higher. After substituting
ea → exp(a), eb → exp(b), the deg-8 part of
  `½W_H1 + ⅓y³ − ¼y⁴ + ⅕y⁵ − ⅙y⁶ + ⅐y⁷ − ⅛y⁸ − C₃ − C₄ − C₅ − C₆ − C₇ − C₈`
vanishes. This identity expresses that vanishing as an explicit pure {a, b}
ring identity, with the deg-8 leading term `bch_octic_term`.

Notation:
- `z = a + b`
- `T_k = y_dk` for k = 2..7 (deg-k of `y = exp(a)·exp(b) − 1`)
- `W8 = 2·y_d8 − (y²)_d8`
- `y3_8 = (y³)_d8`, `y4_8 = (y⁴)_d8`, `y5_8 = (y⁵)_d8`,
  `y6_8 = (y⁶)_d8`, `y7_8 = (y⁷)_d8`, `(y⁸)_d8 = z⁸`

Foundation for stepping stone 1 (`symmetric_bch_septic_sub_poly_axiom`)
discharge — the deg-9 analog of T2-F7e. -/
private theorem nonic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let T₆ : 𝔸 := (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6
    let T₇ : 𝔸 := (5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a * b ^ 6) + (5040 : 𝕂)⁻¹ • b ^ 7
    -- W8 = 2·y_d8 − (y²)_d8, where (y²)_d8 = z·T_7 + T_2·T_6 + T_3·T_5 + T_4·T_4 + T_5·T_3 + T_6·T_2 + T_7·z
    let W8 : 𝔸 := (20160 : 𝕂)⁻¹ • a ^ 8 + (2520 : 𝕂)⁻¹ • (a ^ 7 * b) +
        (720 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (360 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3) +
        (288 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4) + (360 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a ^ 2 * b ^ 6) + (2520 : 𝕂)⁻¹ • (a * b ^ 7) +
        (20160 : 𝕂)⁻¹ • b ^ 8 -
        (z * T₇ + T₂ * T₆ + T₃ * T₅ + T₄ * T₄ + T₅ * T₃ + T₆ * T₂ + T₇ * z)
    -- y3_8 = (y^3)_d8: 21 terms from k_1+...+k_3=8, each ≥ 1
    let y3_8 : 𝔸 :=
        z * z * T₆
        + z * T₂ * T₅
        + z * T₃ * T₄
        + z * T₄ * T₃
        + z * T₅ * T₂
        + z * T₆ * z
        + T₂ * z * T₅
        + T₂ * T₂ * T₄
        + T₂ * T₃ * T₃
        + T₂ * T₄ * T₂
        + T₂ * T₅ * z
        + T₃ * z * T₄
        + T₃ * T₂ * T₃
        + T₃ * T₃ * T₂
        + T₃ * T₄ * z
        + T₄ * z * T₃
        + T₄ * T₂ * T₂
        + T₄ * T₃ * z
        + T₅ * z * T₂
        + T₅ * T₂ * z
        + T₆ * z * z
    -- y4_8 = (y^4)_d8: 35 terms from k_1+...+k_4=8, each ≥ 1
    let y4_8 : 𝔸 :=
        z * z * z * T₅
        + z * z * T₂ * T₄
        + z * z * T₃ * T₃
        + z * z * T₄ * T₂
        + z * z * T₅ * z
        + z * T₂ * z * T₄
        + z * T₂ * T₂ * T₃
        + z * T₂ * T₃ * T₂
        + z * T₂ * T₄ * z
        + z * T₃ * z * T₃
        + z * T₃ * T₂ * T₂
        + z * T₃ * T₃ * z
        + z * T₄ * z * T₂
        + z * T₄ * T₂ * z
        + z * T₅ * z * z
        + T₂ * z * z * T₄
        + T₂ * z * T₂ * T₃
        + T₂ * z * T₃ * T₂
        + T₂ * z * T₄ * z
        + T₂ * T₂ * z * T₃
        + T₂ * T₂ * T₂ * T₂
        + T₂ * T₂ * T₃ * z
        + T₂ * T₃ * z * T₂
        + T₂ * T₃ * T₂ * z
        + T₂ * T₄ * z * z
        + T₃ * z * z * T₃
        + T₃ * z * T₂ * T₂
        + T₃ * z * T₃ * z
        + T₃ * T₂ * z * T₂
        + T₃ * T₂ * T₂ * z
        + T₃ * T₃ * z * z
        + T₄ * z * z * T₂
        + T₄ * z * T₂ * z
        + T₄ * T₂ * z * z
        + T₅ * z * z * z
    -- y5_8 = (y^5)_d8: 35 terms from k_1+...+k_5=8, each ≥ 1
    let y5_8 : 𝔸 :=
        z * z * z * z * T₄
        + z * z * z * T₂ * T₃
        + z * z * z * T₃ * T₂
        + z * z * z * T₄ * z
        + z * z * T₂ * z * T₃
        + z * z * T₂ * T₂ * T₂
        + z * z * T₂ * T₃ * z
        + z * z * T₃ * z * T₂
        + z * z * T₃ * T₂ * z
        + z * z * T₄ * z * z
        + z * T₂ * z * z * T₃
        + z * T₂ * z * T₂ * T₂
        + z * T₂ * z * T₃ * z
        + z * T₂ * T₂ * z * T₂
        + z * T₂ * T₂ * T₂ * z
        + z * T₂ * T₃ * z * z
        + z * T₃ * z * z * T₂
        + z * T₃ * z * T₂ * z
        + z * T₃ * T₂ * z * z
        + z * T₄ * z * z * z
        + T₂ * z * z * z * T₃
        + T₂ * z * z * T₂ * T₂
        + T₂ * z * z * T₃ * z
        + T₂ * z * T₂ * z * T₂
        + T₂ * z * T₂ * T₂ * z
        + T₂ * z * T₃ * z * z
        + T₂ * T₂ * z * z * T₂
        + T₂ * T₂ * z * T₂ * z
        + T₂ * T₂ * T₂ * z * z
        + T₂ * T₃ * z * z * z
        + T₃ * z * z * z * T₂
        + T₃ * z * z * T₂ * z
        + T₃ * z * T₂ * z * z
        + T₃ * T₂ * z * z * z
        + T₄ * z * z * z * z
    -- y6_8 = (y^6)_d8: 21 terms from k_1+...+k_6=8, each ≥ 1
    let y6_8 : 𝔸 :=
        z * z * z * z * z * T₃
        + z * z * z * z * T₂ * T₂
        + z * z * z * z * T₃ * z
        + z * z * z * T₂ * z * T₂
        + z * z * z * T₂ * T₂ * z
        + z * z * z * T₃ * z * z
        + z * z * T₂ * z * z * T₂
        + z * z * T₂ * z * T₂ * z
        + z * z * T₂ * T₂ * z * z
        + z * z * T₃ * z * z * z
        + z * T₂ * z * z * z * T₂
        + z * T₂ * z * z * T₂ * z
        + z * T₂ * z * T₂ * z * z
        + z * T₂ * T₂ * z * z * z
        + z * T₃ * z * z * z * z
        + T₂ * z * z * z * z * T₂
        + T₂ * z * z * z * T₂ * z
        + T₂ * z * z * T₂ * z * z
        + T₂ * z * T₂ * z * z * z
        + T₂ * T₂ * z * z * z * z
        + T₃ * z * z * z * z * z
    -- y7_8 = (y^7)_d8: 7 terms from k_1+...+k_7=8, each ≥ 1
    let y7_8 : 𝔸 :=
        z * z * z * z * z * z * T₂
        + z * z * z * z * z * T₂ * z
        + z * z * z * z * T₂ * z * z
        + z * z * z * T₂ * z * z * z
        + z * z * T₂ * z * z * z * z
        + z * T₂ * z * z * z * z * z
        + T₂ * z * z * z * z * z * z
    -- (y⁸)_d8 = z⁸ (only (1,1,1,1,1,1,1,1))
    (2 : 𝕂)⁻¹ • W8 + (3 : 𝕂)⁻¹ • y3_8 - (4 : 𝕂)⁻¹ • y4_8 +
      (5 : 𝕂)⁻¹ • y5_8 - (6 : 𝕂)⁻¹ • y6_8 + (7 : 𝕂)⁻¹ • y7_8 -
      (8 : 𝕂)⁻¹ • z ^ 8 - bch_octic_term 𝕂 a b = 0 := by
  intro z T₂ T₃ T₄ T₅ T₆ T₇ W8 y3_8 y4_8 y5_8 y6_8 y7_8
  show _ = (0 : 𝔸)
  simp only [show z = a + b from rfl,
    show T₂ = a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2 from rfl,
    show T₃ = (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3 from rfl,
    show T₄ = (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4 from rfl,
    show T₅ = (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5 from rfl,
    show T₆ = (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6 from rfl,
    show T₇ = (5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a * b ^ 6) + (5040 : 𝕂)⁻¹ • b ^ 7 from rfl,
    show W8 = (20160 : 𝕂)⁻¹ • a ^ 8 + (2520 : 𝕂)⁻¹ • (a ^ 7 * b) +
        (720 : 𝕂)⁻¹ • (a ^ 6 * b ^ 2) + (360 : 𝕂)⁻¹ • (a ^ 5 * b ^ 3) +
        (288 : 𝕂)⁻¹ • (a ^ 4 * b ^ 4) + (360 : 𝕂)⁻¹ • (a ^ 3 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a ^ 2 * b ^ 6) + (2520 : 𝕂)⁻¹ • (a * b ^ 7) +
        (20160 : 𝕂)⁻¹ • b ^ 8 -
        (z * T₇ + T₂ * T₆ + T₃ * T₅ + T₄ * T₄ + T₅ * T₃ + T₆ * T₂ + T₇ * z) from rfl,
    show y3_8 =
        z * z * T₆
        + z * T₂ * T₅
        + z * T₃ * T₄
        + z * T₄ * T₃
        + z * T₅ * T₂
        + z * T₆ * z
        + T₂ * z * T₅
        + T₂ * T₂ * T₄
        + T₂ * T₃ * T₃
        + T₂ * T₄ * T₂
        + T₂ * T₅ * z
        + T₃ * z * T₄
        + T₃ * T₂ * T₃
        + T₃ * T₃ * T₂
        + T₃ * T₄ * z
        + T₄ * z * T₃
        + T₄ * T₂ * T₂
        + T₄ * T₃ * z
        + T₅ * z * T₂
        + T₅ * T₂ * z
        + T₆ * z * z
        from rfl,
    show y4_8 =
        z * z * z * T₅
        + z * z * T₂ * T₄
        + z * z * T₃ * T₃
        + z * z * T₄ * T₂
        + z * z * T₅ * z
        + z * T₂ * z * T₄
        + z * T₂ * T₂ * T₃
        + z * T₂ * T₃ * T₂
        + z * T₂ * T₄ * z
        + z * T₃ * z * T₃
        + z * T₃ * T₂ * T₂
        + z * T₃ * T₃ * z
        + z * T₄ * z * T₂
        + z * T₄ * T₂ * z
        + z * T₅ * z * z
        + T₂ * z * z * T₄
        + T₂ * z * T₂ * T₃
        + T₂ * z * T₃ * T₂
        + T₂ * z * T₄ * z
        + T₂ * T₂ * z * T₃
        + T₂ * T₂ * T₂ * T₂
        + T₂ * T₂ * T₃ * z
        + T₂ * T₃ * z * T₂
        + T₂ * T₃ * T₂ * z
        + T₂ * T₄ * z * z
        + T₃ * z * z * T₃
        + T₃ * z * T₂ * T₂
        + T₃ * z * T₃ * z
        + T₃ * T₂ * z * T₂
        + T₃ * T₂ * T₂ * z
        + T₃ * T₃ * z * z
        + T₄ * z * z * T₂
        + T₄ * z * T₂ * z
        + T₄ * T₂ * z * z
        + T₅ * z * z * z
        from rfl,
    show y5_8 =
        z * z * z * z * T₄
        + z * z * z * T₂ * T₃
        + z * z * z * T₃ * T₂
        + z * z * z * T₄ * z
        + z * z * T₂ * z * T₃
        + z * z * T₂ * T₂ * T₂
        + z * z * T₂ * T₃ * z
        + z * z * T₃ * z * T₂
        + z * z * T₃ * T₂ * z
        + z * z * T₄ * z * z
        + z * T₂ * z * z * T₃
        + z * T₂ * z * T₂ * T₂
        + z * T₂ * z * T₃ * z
        + z * T₂ * T₂ * z * T₂
        + z * T₂ * T₂ * T₂ * z
        + z * T₂ * T₃ * z * z
        + z * T₃ * z * z * T₂
        + z * T₃ * z * T₂ * z
        + z * T₃ * T₂ * z * z
        + z * T₄ * z * z * z
        + T₂ * z * z * z * T₃
        + T₂ * z * z * T₂ * T₂
        + T₂ * z * z * T₃ * z
        + T₂ * z * T₂ * z * T₂
        + T₂ * z * T₂ * T₂ * z
        + T₂ * z * T₃ * z * z
        + T₂ * T₂ * z * z * T₂
        + T₂ * T₂ * z * T₂ * z
        + T₂ * T₂ * T₂ * z * z
        + T₂ * T₃ * z * z * z
        + T₃ * z * z * z * T₂
        + T₃ * z * z * T₂ * z
        + T₃ * z * T₂ * z * z
        + T₃ * T₂ * z * z * z
        + T₄ * z * z * z * z
        from rfl,
    show y6_8 =
        z * z * z * z * z * T₃
        + z * z * z * z * T₂ * T₂
        + z * z * z * z * T₃ * z
        + z * z * z * T₂ * z * T₂
        + z * z * z * T₂ * T₂ * z
        + z * z * z * T₃ * z * z
        + z * z * T₂ * z * z * T₂
        + z * z * T₂ * z * T₂ * z
        + z * z * T₂ * T₂ * z * z
        + z * z * T₃ * z * z * z
        + z * T₂ * z * z * z * T₂
        + z * T₂ * z * z * T₂ * z
        + z * T₂ * z * T₂ * z * z
        + z * T₂ * T₂ * z * z * z
        + z * T₃ * z * z * z * z
        + T₂ * z * z * z * z * T₂
        + T₂ * z * z * z * T₂ * z
        + T₂ * z * z * T₂ * z * z
        + T₂ * z * T₂ * z * z * z
        + T₂ * T₂ * z * z * z * z
        + T₃ * z * z * z * z * z
        from rfl,
    show y7_8 =
        z * z * z * z * z * z * T₂
        + z * z * z * z * z * T₂ * z
        + z * z * z * z * T₂ * z * z
        + z * z * z * T₂ * z * z * z
        + z * z * T₂ * z * z * z * z
        + z * T₂ * z * z * z * z * z
        + T₂ * z * z * z * z * z * z
        from rfl]
  unfold bch_octic_term
  simp (config := { maxSteps := 1000000 }) only [pow_succ, pow_zero, one_mul,
    smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

set_option maxHeartbeats 128000000 in
include 𝕂 in
/-- **Fifth-order BCH**: `bch(a,b) = (a+b) + ½[a,b] + bch_cubic_term(a,b) + bch_quartic_term(a,b) + O(s⁵)`.

This extends the fourth-order result `norm_bch_quartic_remainder_le` by identifying the
quartic coefficient `-(1/24)([a,[a,[a,b]]]+[b,[b,[b,a]]])`. The proof decomposes
`LHS = pieceA' + pieceB'` where pieceA' is the quintic log tail (bounded by `‖y‖⁵/(1-‖y‖)`)
and pieceB' is the algebraic piece (bounded by combining the quartic_identity with
fifth-order exp remainders and the quartic norm bound on the combined degree-4 terms). -/
theorem norm_bch_quintic_remainder_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
      3000 * (‖a‖ + ‖b‖) ^ 5 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  -- SETUP (same as quartic proof)
  set y := exp a * exp b - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖; set β := ‖b‖
  have hs_nn : 0 ≤ s := by positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have : y = (exp a - 1) * exp b + (exp b - 1) := by rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [this]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
          calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          apply add_le_add
          · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
              (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  have hs34 : s < 3 / 4 := lt_of_lt_of_le hab (by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    calc (2 : ℝ) ≤ 1 + 3 / 4 + (3 / 4) ^ 2 / 2 := by norm_num
      _ ≤ Real.exp (3 / 4) := Real.quadratic_le_exp_of_nonneg (by norm_num))
  have hs1 : s < 1 := by linarith
  -- STRATEGY: Use quartic theorem + C₄ bound + case split on s.
  -- R₃ := bch-(a+b)-½[a,b]-C₃ satisfies ‖R₃‖ ≤ 200s⁴/(2-exp(s)).
  -- LHS = R₃-C₄. By triangle: ‖LHS‖ ≤ 201s⁴/(2-exp(s)).
  -- For s ≥ 67/1000: 201/s ≤ 3000, so 201s⁴/(2-exp(s)) ≤ 3000s⁵/(2-exp(s)).
  -- For s < 67/1000: use 5th-order expansion.
  have hR₃ := norm_bch_quartic_remainder_le (𝕂 := 𝕂) a b hab
  have hC₄ : ‖bch_quartic_term 𝕂 a b‖ ≤ s ^ 4 :=
    norm_bch_quartic_term_le a b
  -- ‖LHS‖ ≤ ‖R₃‖ + ‖C₄‖
  have hLHS_s4 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
      200 * s ^ 4 / (2 - Real.exp s) + s ^ 4 := by
    have hsub : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b =
        (bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        bch_cubic_term 𝕂 a b) - bch_quartic_term 𝕂 a b := by abel
    rw [hsub]
    calc _ ≤ ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          bch_cubic_term 𝕂 a b‖ + ‖bch_quartic_term 𝕂 a b‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  -- Tighten: s⁴ ≤ s⁴/(2-exp(s)) since 2-exp(s) ≤ 1
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hLHS_201 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
      201 * s ^ 4 / (2 - Real.exp s) := by
    calc _ ≤ 200 * s ^ 4 / (2 - Real.exp s) + s ^ 4 := hLHS_s4
      _ ≤ 200 * s ^ 4 / (2 - Real.exp s) + s ^ 4 / (2 - Real.exp s) := by
          gcongr
          rw [le_div_iff₀ hdenom]
          nlinarith [pow_nonneg hs_nn 4]
      _ = 201 * s ^ 4 / (2 - Real.exp s) := by ring
  -- Case split
  by_cases hs_large : 67 / 1000 ≤ s
  · -- CASE 1: s ≥ 67/1000 — the crude bound suffices
    have hs_pos : 0 < s := by linarith
    have h201_le : 201 * s ^ 4 ≤ 3000 * s ^ 5 := by
      have : 201 ≤ 3000 * s := by linarith
      nlinarith [pow_nonneg hs_nn 4]
    calc _ ≤ 201 * s ^ 4 / (2 - Real.exp s) := hLHS_201
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) := by
          apply div_le_div_of_nonneg_right h201_le hdenom.le
  · -- CASE 2: s < 67/1000 — use pieceA'/pieceB' decomposition + 5th-order analysis
    push_neg at hs_large  -- hs_large : s < 67/1000
    -- Decompose LHS = pieceA' + pieceB'
    set y := exp a * exp b - 1 with hy_def
    have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one (𝕂 := 𝕂) a b hab
    have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
      have : y = (exp a - 1) * exp b + (exp b - 1) := by rw [hy_def, sub_mul, one_mul]; abel
      calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [this]
        _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
            calc _ ≤ ‖(exp a - 1) * exp b‖ + _ := norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_mul_le _ _
        _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
            apply add_le_add
            · exact mul_le_mul (norm_exp_sub_one_le (𝕂 := 𝕂) a) (norm_exp_le (𝕂 := 𝕂) b)
                (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
            · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
        _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
    have hdecomp : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b =
        (logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 - (3 : 𝕂)⁻¹ • y ^ 3 +
          (4 : 𝕂)⁻¹ • y ^ 4) +
        (y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b) := by
      unfold bch bch_cubic_term bch_quartic_term; abel
    rw [hdecomp]
    -- Bound pieceA' ≤ (exp(s)-1)⁵/(2-exp(s))
    have hpieceA : ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
        (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4‖ ≤
        (Real.exp s - 1) ^ 5 / (2 - Real.exp s) :=
      calc _ ≤ ‖y‖ ^ 5 / (1 - ‖y‖) := norm_logOnePlus_sub_sub_sub_sub_le (𝕂 := 𝕂) y hy_lt
        _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
            (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
    -- Bound pieceB' — this is the main technical step
    -- Uses quartic_identity + G-level refinement + quintic_pure_identity for degree-4 cancellation
    have hpieceB : ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
        (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
        bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤
        2800 * s ^ 5 / (2 - Real.exp s) := by
      -- pieceB' = quartic_pieceB - ¼y⁴ - C₄
      -- Use the quartic_identity + G-level refinement + quintic_pure_identity.
      -- After algebraic decomposition, pieceB' = [quintic terms] (degree-4 = 0).
      -- Each quintic term ≤ Cs⁵. Total ≤ 50s⁵ ≤ 2800s⁵/(2-exp(s)).
      --
      -- Define quintic exp remainders
      set G₁ := exp a - 1 - a - (2 : 𝕂)⁻¹ • a ^ 2 - (6 : 𝕂)⁻¹ • a ^ 3 -
          (24 : 𝕂)⁻¹ • a ^ 4
      set G₂ := exp b - 1 - b - (2 : 𝕂)⁻¹ • b ^ 2 - (6 : 𝕂)⁻¹ • b ^ 3 -
          (24 : 𝕂)⁻¹ • b ^ 4
      -- Quintic exp remainder bounds: ‖G₁‖ ≤ α⁵, ‖G₂‖ ≤ β⁵
      have hG₁_le : ‖G₁‖ ≤ α ^ 5 := by
        calc ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
              norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) a
          _ ≤ α ^ 5 := real_exp_fifth_order_le_quintic (norm_nonneg a)
              (lt_of_le_of_lt hα_le hs34)
      have hG₂_le : ‖G₂‖ ≤ β ^ 5 := by
        calc ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
              norm_exp_sub_one_sub_sub_sub_sub_le (𝕂 := 𝕂) b
          _ ≤ β ^ 5 := real_exp_fifth_order_le_quintic (norm_nonneg b)
              (lt_of_le_of_lt hβ_le hs34)
      -- STRATEGY: Reduce to ‖pieceB'‖ ≤ 50s⁵, then use algebraic decomposition.
      -- The degree-4 terms cancel by quintic_pure_identity (corrected sign).
      -- Remaining quintic+ terms are bounded by exp remainder norms.
      --
      -- Step 1: Reduce to showing ≤ 50*s^5
      suffices h_suff : ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ ≤ 50 * s ^ 5 by
        have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
        calc _ ≤ 50 * s ^ 5 := h_suff
          _ ≤ 2800 * s ^ 5 / (2 - Real.exp s) := by
            rw [le_div_iff₀ hdenom]
            nlinarith [pow_nonneg hs_nn 5]
      -- Step 2: Set up exp remainder variables
      set D₁ := exp a - 1 - a with hD₁_def
      set D₂ := exp b - 1 - b with hD₂_def
      set E₁ := D₁ - (2 : 𝕂)⁻¹ • a ^ 2 with hE₁_def
      set E₂ := D₂ - (2 : 𝕂)⁻¹ • b ^ 2 with hE₂_def
      set F₁ := E₁ - (6 : 𝕂)⁻¹ • a ^ 3 with hF₁_def
      set F₂ := E₂ - (6 : 𝕂)⁻¹ • b ^ 3 with hF₂_def
      -- G₁ = F₁ - (24)⁻¹a⁴, G₂ = F₂ - (24)⁻¹b⁴ (already set above)
      set P := y - (a + b) with hP_def
      set z := a + b with hz_def
      -- Step 3: Norm bounds on exp remainders
      have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α :=
        norm_exp_sub_one_sub_le (𝕂 := 𝕂) a
      have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β :=
        norm_exp_sub_one_sub_le (𝕂 := 𝕂) b
      have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
        linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
      have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
        linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
      have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
        have h := Real.norm_exp_sub_one_sub_id_le
          (show ‖α‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hα_nn]; linarith)
        rwa [Real.norm_eq_abs, abs_of_nonneg hDa_nn,
             Real.norm_eq_abs, abs_of_nonneg hα_nn] at h
      have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
        have h := Real.norm_exp_sub_one_sub_id_le
          (show ‖β‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hβ_nn]; linarith)
        rwa [Real.norm_eq_abs, abs_of_nonneg hDb_nn,
             Real.norm_eq_abs, abs_of_nonneg hβ_nn] at h
      have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
        linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
      have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
        have h := Real.norm_exp_sub_one_sub_id_le
          (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
        rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn,
             Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
      have hs56 : s < 5 / 6 := by linarith
      have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
        norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) a
      have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
        norm_exp_sub_one_sub_sub_le (𝕂 := 𝕂) b
      have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
        real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
      have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
        real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
      have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
        norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) a
      have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
        norm_exp_sub_one_sub_sub_sub_le (𝕂 := 𝕂) b
      have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
        real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
      have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
        real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
      -- Composite s-power bounds
      have hz_le : ‖z‖ ≤ s := by
        calc ‖z‖ = ‖a + b‖ := by rw [hz_def]
          _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
          _ = s := by rw [hs_def]
      have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
        have hP_split : P = a * (exp b - 1) + D₁ * exp b + D₂ := by
          simp only [hP_def, hy_def, hD₁_def, hD₂_def, hz_def]; noncomm_ring
        calc ‖P‖ = ‖a * (exp b - 1) + D₁ * exp b + D₂‖ := by rw [hP_split]
          _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
              calc _ ≤ ‖a * (exp b - 1) + D₁ * exp b‖ + ‖D₂‖ := norm_add_le _ _
                _ ≤ ‖a * (exp b - 1)‖ + ‖D₁ * exp b‖ + ‖D₂‖ := by
                    gcongr; exact norm_add_le _ _
          _ ≤ α * (Real.exp β - 1) + (Real.exp α - 1 - α) * Real.exp β +
              (Real.exp β - 1 - β) := by
              have h1 : ‖a * (exp b - 1)‖ ≤ α * (Real.exp β - 1) :=
                calc _ ≤ ‖a‖ * ‖exp b - 1‖ := norm_mul_le _ _
                  _ ≤ _ := by gcongr; exact norm_exp_sub_one_le (𝕂 := 𝕂) b
              have h2 : ‖D₁ * exp b‖ ≤ (Real.exp α - 1 - α) * Real.exp β :=
                calc _ ≤ ‖D₁‖ * ‖exp b‖ := norm_mul_le _ _
                  _ ≤ _ := mul_le_mul hD₁_le (norm_exp_le (𝕂 := 𝕂) b)
                      (norm_nonneg _) (by linarith)
              linarith [hD₂_le]
          _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
      have hP_le_s2 : ‖P‖ ≤ s ^ 2 := le_trans hP_le hEs2
      -- Step 4: Bound ‖y⁴-z⁴‖ ≤ 15s⁵ (quintic+ from y⁴ via telescoping)
      have hy_le2 : ‖y‖ ≤ 2 * s := by
        calc ‖y‖ ≤ Real.exp s - 1 := hy_le
          _ ≤ s + s ^ 2 := by linarith [hEs2]
          _ ≤ 2 * s := by nlinarith [sq_nonneg s]
      have hy4z4 : ‖y ^ 4 - z ^ 4‖ ≤ 15 * s ^ 5 := by
        -- y⁴-z⁴ = y³P+y²Pz+yPz²+Pz³ (non-commutative telescoping)
        have htel : y ^ 4 - z ^ 4 = y ^ 3 * P + y ^ 2 * P * z +
            y * P * z ^ 2 + P * z ^ 3 := by
          simp only [hP_def, hz_def]; noncomm_ring
        -- Bound each term using ‖y‖ ≤ 2s, ‖P‖ ≤ s², ‖z‖ ≤ s
        have h1 : ‖y ^ 3 * P‖ ≤ (2*s)^3 * s^2 := by
          calc _ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ ‖y‖^3 * ‖P‖ := by gcongr; exact norm_pow_le y 3
            _ ≤ (2*s)^3 * s^2 := by
                apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_le2 3) hP_le_s2
                  (norm_nonneg _) (by positivity)
        have h2 : ‖y ^ 2 * P * z‖ ≤ (2*s)^2 * s^2 * s := by
          calc _ ≤ ‖y ^ 2 * P‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ (‖y‖^2 * ‖P‖) * ‖z‖ := by
                gcongr
                calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
                  _ ≤ _ := by gcongr; exact norm_pow_le y 2
            _ ≤ ((2*s)^2 * s^2) * s := by
                apply mul_le_mul _ hz_le (norm_nonneg _) (by positivity)
                apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_le2 2) hP_le_s2
                  (norm_nonneg _) (by positivity)
        have h3 : ‖y * P * z ^ 2‖ ≤ 2*s * s^2 * s^2 := by
          calc _ ≤ ‖y * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ (‖y‖ * ‖P‖) * ‖z‖^2 := by
                gcongr
                · exact norm_mul_le _ _
                · exact norm_pow_le z 2
            _ ≤ (2*s * s^2) * s^2 := by
                apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
                  (by positivity) (by positivity)
                exact mul_le_mul hy_le2 hP_le_s2 (norm_nonneg _) (by positivity)
        have h4 : ‖P * z ^ 3‖ ≤ s^2 * s^3 := by
          calc _ ≤ ‖P‖ * ‖z ^ 3‖ := norm_mul_le _ _
            _ ≤ ‖P‖ * ‖z‖^3 := by gcongr; exact norm_pow_le z 3
            _ ≤ s^2 * s^3 := by
                apply mul_le_mul hP_le_s2 (pow_le_pow_left₀ (norm_nonneg z) hz_le 3)
                  (by positivity) (by positivity)
        calc ‖y ^ 4 - z ^ 4‖ = ‖y ^ 3 * P + y ^ 2 * P * z +
              y * P * z ^ 2 + P * z ^ 3‖ := by rw [htel]
          _ ≤ ‖y ^ 3 * P‖ + ‖y ^ 2 * P * z‖ + ‖y * P * z ^ 2‖ + ‖P * z ^ 3‖ := by
              calc _ ≤ ‖y ^ 3 * P + y ^ 2 * P * z + y * P * z ^ 2‖ + _ := norm_add_le _ _
                _ ≤ (‖y ^ 3 * P + y ^ 2 * P * z‖ + _) + _ := by gcongr; exact norm_add_le _ _
                _ ≤ _ := by linarith [norm_add_le (y ^ 3 * P) (y ^ 2 * P * z)]
          _ ≤ (2*s)^3*s^2 + (2*s)^2*s^2*s + 2*s*s^2*s^2 + s^2*s^3 := by linarith
          _ = 15 * s ^ 5 := by ring
      -- Step 5: Additional norm bounds needed for the quintic+ terms
      have hS_le : ‖P - (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2)‖ ≤
          5 * s ^ 3 := by
        -- S = P - P₂ = E₁+E₂+aD₂+D₁b+D₁D₂ (starts at degree 3)
        have hS_eq : P - (a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2) =
            E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂ := by
          simp only [hP_def, hy_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hz_def]
          noncomm_ring
        rw [hS_eq]
        have hE₁_s3 : ‖E₁‖ ≤ α ^ 3 := le_trans hE₁_le hEa3
        have hE₂_s3 : ‖E₂‖ ≤ β ^ 3 := le_trans hE₂_le hEb3
        have haD₂ : ‖a * D₂‖ ≤ α * β ^ 2 :=
          calc _ ≤ ‖a‖ * ‖D₂‖ := norm_mul_le _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans hD₂_le hDb2) hα_nn
        have hD₁b : ‖D₁ * b‖ ≤ α ^ 2 * β :=
          calc _ ≤ ‖D₁‖ * ‖b‖ := norm_mul_le _ _
            _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) le_rfl hβ_nn (by positivity)
        have hDD : ‖D₁ * D₂‖ ≤ α ^ 2 * β ^ 2 :=
          calc _ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le _ _
            _ ≤ _ := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
                (norm_nonneg _) (by positivity)
        calc ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖
            ≤ ‖E₁‖ + ‖E₂‖ + ‖a * D₂‖ + ‖D₁ * b‖ + ‖D₁ * D₂‖ := by
              have := norm_add_le E₁ E₂
              have := norm_add_le (E₁ + E₂) (a * D₂)
              have := norm_add_le (E₁ + E₂ + a * D₂) (D₁ * b)
              have := norm_add_le (E₁ + E₂ + a * D₂ + D₁ * b) (D₁ * D₂)
              linarith
          _ ≤ α ^ 3 + β ^ 3 + α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 := by
              linarith [hE₁_s3, hE₂_s3, haD₂, hD₁b, hDD]
          _ ≤ 5 * s ^ 3 := by nlinarith [pow_le_pow_left₀ hα_nn hα_le 3,
              pow_le_pow_left₀ hβ_nn hβ_le 3, pow_le_pow_left₀ hα_nn hα_le 2,
              pow_le_pow_left₀ hβ_nn hβ_le 2, pow_nonneg hs_nn 4]
      -- Step 6: Bound using individual quintic+ terms
      -- Each group ≤ Cs⁵ by the bounds proved above.
      have hG₁_s5 : ‖G₁‖ ≤ s ^ 5 :=
        le_trans hG₁_le (pow_le_pow_left₀ hα_nn hα_le 5)
      have hG₂_s5 : ‖G₂‖ ≤ s ^ 5 :=
        le_trans hG₂_le (pow_le_pow_left₀ hβ_nn hβ_le 5)
      have haF₂ : ‖a * F₂‖ ≤ s ^ 5 :=
        calc _ ≤ ‖a‖ * ‖F₂‖ := norm_mul_le _ _
          _ ≤ α * β ^ 4 := mul_le_mul_of_nonneg_left (le_trans hF₂_le hFb4) hα_nn
          _ ≤ s * s ^ 4 :=
              mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 4) (by positivity) hs_nn
          _ = s ^ 5 := by ring
      have hF₁b : ‖F₁ * b‖ ≤ s ^ 5 :=
        calc _ ≤ ‖F₁‖ * ‖b‖ := norm_mul_le _ _
          _ ≤ α ^ 4 * β := mul_le_mul (le_trans hF₁_le hFa4) le_rfl hβ_nn (by positivity)
          _ ≤ s ^ 4 * s :=
              mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 4) hβ_le (by positivity) (by positivity)
          _ = s ^ 5 := by ring
      -- Step 6a: Set up the I₁/I₂ decomposition (same as quartic proof)
      have h2ne : (2 : 𝕂) ≠ 0 := two_ne_zero
      set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
      set W_H1 := (2 : 𝕂) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          z * P - P * z - P ^ 2 with hW_H1_def
      -- H1 identity: y-z-½[a,b]-½y² = ½W
      have hH1 : y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 =
          (2 : 𝕂)⁻¹ • W_H1 := by
        suffices h : (2 : 𝕂) • (y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
            (2 : 𝕂)⁻¹ • y ^ 2) = (2 : 𝕂) • ((2 : 𝕂)⁻¹ • W_H1) by
          have hinj : Function.Injective ((2 : 𝕂) • · : 𝔸 → 𝔸) := by
            intro x₀ y₀ hxy; have := congrArg ((2 : 𝕂)⁻¹ • ·) hxy
            simp only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] at this; exact this
          exact hinj h
        rw [smul_smul, mul_inv_cancel₀ h2ne, one_smul]
        simp only [hE₁_def, hE₂_def, hD₁_def, hD₂_def, hP_def, hy_def, hW_H1_def, hz_def,
          smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h2ne, one_smul, two_smul]
        noncomm_ring
      -- I₁ = ½W + ⅓z³ - C₃, I₂ = ⅓(y³-z³)
      set I₁ := (2 : 𝕂)⁻¹ • W_H1 + (3 : 𝕂)⁻¹ • z ^ 3 -
          bch_cubic_term 𝕂 a b with hI₁_def
      set I₂ := (3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) with hI₂_def
      -- pieceB' = I₁ + I₂ - ¼y⁴ - C₄
      have hpB_split : y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b =
          I₁ + I₂ - (4 : 𝕂)⁻¹ • y ^ 4 - bch_quartic_term 𝕂 a b := by
        -- Rewrite y-z-½[a,b]-½y² = ½W by H1 identity
        conv_lhs => rw [show y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) -
            (2 : 𝕂)⁻¹ • y ^ 2 = (2 : 𝕂)⁻¹ • W_H1 from hH1]
        -- Now LHS = ½W+⅓y³-¼y⁴-C₃-C₄, RHS = I₁+I₂-¼y⁴-C₄
        -- Expand I₁ and I₂ definitions and simplify ⅓(y³-z³) = ⅓y³-⅓z³
        simp only [hI₁_def, hI₂_def, smul_sub]
        abel
      -- Step 6b: Apply quartic_identity to I₁
      have hI₁_eq2 : I₁ = (2 : 𝕂)⁻¹ • W_H1 +
          (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b := rfl
      have hI₁_quartic : I₁ =
          F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
          (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
          (2 : 𝕂)⁻¹ • P ^ 2 := by
        rw [hI₁_eq2]; exact quartic_identity 𝕂 (exp a) (exp b) a b
      -- Step 6c: Define degree-4 correction terms (matching quintic_pure_identity)
      -- corr₁ = degree-4 of I₁, corr₂ = degree-4 of I₂
      set T₃ := (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
          (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)
      set P₂ := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
      -- [A]+[B]+[C]: degree-4 of I₁
      let corr₁ := (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
          (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
          (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
          (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
          (2 : 𝕂)⁻¹ • P₂ ^ 2
      -- [D]: degree-4 of I₂
      let corr₂ := (3 : 𝕂)⁻¹ • (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2)
      -- Step 6d: Show QPI gives corr₁+corr₂-¼z⁴ = C₄
      have hQPI : corr₁ + corr₂ - (4 : 𝕂)⁻¹ • z ^ 4 -
          bch_quartic_term 𝕂 a b = 0 := by
        show (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
            (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
            (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
            (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
            (2 : 𝕂)⁻¹ • P₂ ^ 2 +
            (3 : 𝕂)⁻¹ • (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2) -
            (4 : 𝕂)⁻¹ • z ^ 4 - bch_quartic_term 𝕂 a b = 0
        -- This matches quintic_pure_identity after expanding z = a+b
        -- and the T₃, P₂ definitions.
        convert quintic_pure_identity 𝕂 a b using 2 <;> simp [hz_def] <;> ring
      -- Step 6e: Rearrange pieceB' using degree-4 cancellation
      rw [hpB_split]
      -- Goal: ‖I₁+I₂-¼y⁴-C₄‖ ≤ 50s⁵
      -- Use hQPI to cancel: I₁+I₂-¼y⁴-C₄ = (I₁-corr₁)+(I₂-corr₂)-¼(y⁴-z⁴)
      -- since corr₁+corr₂-¼z⁴ = C₄ by hQPI.
      have hrewrite : I₁ + I₂ - (4 : 𝕂)⁻¹ • y ^ 4 - bch_quartic_term 𝕂 a b =
          (I₁ - corr₁) + (I₂ - corr₂) - (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4) := by
        -- LHS - RHS = corr₁+corr₂-¼z⁴-C₄ = 0 (by QPI)
        rw [sub_eq_zero.symm]  -- convert goal A=B to A-B=0
        convert hQPI using 1    -- match _ = 0 with _ = 0
        simp only [smul_sub]
        abel
      rw [hrewrite]
      -- Step 6f: Bound each quintic+ group via triangle inequality
      -- Group 1: ‖I₁-corr₁‖ ≤ 20s⁵ (quartic_identity refined to quintic)
      have hGroup1 : ‖I₁ - corr₁‖ ≤ 20 * s ^ 5 := by
        -- Algebraic identity: I₁-corr₁ = quintic+ terms
        -- From quartic_identity: I₁ = F₁+F₂+aE₂+E₁b+D₁D₂-½(z(E₁+E₂+Q)+(E₁+E₂+Q)z)-½P²
        -- Subtract corr₁ = [A]+[B]+[C] (degree-4 pure terms)
        -- Result: G₁+G₂+aF₂+F₁b+½(a²E₂+E₁b²)+E₁E₂ - ½(z·S_rest+S_rest·z) - ½(P₂S+SP₂+S²)
        -- where S_rest = (E₁+E₂+Q)-T₃ and S = P-P₂.
        -- Each of the ~10 terms is bounded by ≤ Cs⁵.
        -- Regroup I₁-corr₁ as sum of small differences, then bound each
        rw [hI₁_quartic]
        -- I₁ = F₁+F₂+aE₂+E₁b+D₁D₂-½(z(E₁+E₂+Q)+(E₁+E₂+Q)z)-½P²
        -- corr₁ (let, transparent) = degree-4 pure terms
        -- Regroup: (I₁ terms) - corr₁ = Σ(quartic term - its degree-4 part)
        have h_regroup :
            F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
              (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
              (2 : 𝕂)⁻¹ • P ^ 2 - corr₁ =
            (F₁ - (24 : 𝕂)⁻¹ • a ^ 4) + (F₂ - (24 : 𝕂)⁻¹ • b ^ 4) +
            (a * E₂ - (6 : 𝕂)⁻¹ • (a * b ^ 3)) +
            (E₁ * b - (6 : 𝕂)⁻¹ • (a ^ 3 * b)) +
            (D₁ * D₂ - (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2)) +
            ((2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
              (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z)) +
            ((2 : 𝕂)⁻¹ • P₂ ^ 2 - (2 : 𝕂)⁻¹ • P ^ 2) := by
          -- Expand corr₁ (let binding) explicitly so abel can see all atoms
          change F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
              (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
              (2 : 𝕂)⁻¹ • P ^ 2 -
              ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
               (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
               (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
               (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
               (2 : 𝕂)⁻¹ • P₂ ^ 2) = _
          abel
        -- After h_regroup, bound 7 groups by triangle inequality.
        -- Each group ≤ Cs⁵ from proved bounds (G_i≤s⁵, aF₂≤s⁵, F₁b≤s⁵, etc.).
        -- Total: ≤ 20s⁵.
        rw [h_regroup]
        -- Simplify each group using definitional identities
        have hA : F₁ - (24 : 𝕂)⁻¹ • a ^ 4 = G₁ := by dsimp only
        have hB : F₂ - (24 : 𝕂)⁻¹ • b ^ 4 = G₂ := by dsimp only
        have hC : a * E₂ - (6 : 𝕂)⁻¹ • (a * b ^ 3) = a * F₂ := by
          have : E₂ = F₂ + (6 : 𝕂)⁻¹ • b ^ 3 := by rw [hF₂_def]; abel
          rw [this, mul_add, mul_smul_comm]; abel
        have hDt : E₁ * b - (6 : 𝕂)⁻¹ • (a ^ 3 * b) = F₁ * b := by
          have : E₁ = F₁ + (6 : 𝕂)⁻¹ • a ^ 3 := by rw [hF₁_def]; abel
          rw [this, add_mul, smul_mul_assoc]; abel
        have hEt : D₁ * D₂ - (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) =
            E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂) + (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) := by
          have hd1 : D₁ = E₁ + (2 : 𝕂)⁻¹ • a ^ 2 := by rw [hE₁_def]; abel
          have hd2 : D₂ = E₂ + (2 : 𝕂)⁻¹ • b ^ 2 := by rw [hE₂_def]; abel
          rw [hd1, hd2]; simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            smul_smul, show (2:𝕂)⁻¹*(2:𝕂)⁻¹=(4:𝕂)⁻¹ from by norm_num, smul_add]; abel
        have hFt : (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) -
            (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) =
            (2 : 𝕂)⁻¹ • (z * (T₃ - E₁ - E₂ - Q) + (T₃ - E₁ - E₂ - Q) * z) := by
          rw [← smul_sub]; congr 1; noncomm_ring
        have hGt : (2 : 𝕂)⁻¹ • P₂ ^ 2 - (2 : 𝕂)⁻¹ • P ^ 2 =
            (2 : 𝕂)⁻¹ • (P₂ ^ 2 - P ^ 2) := (smul_sub _ _ _).symm
        rw [hA, hB, hC, hDt, hEt, hFt, hGt]
        have hT₃_exp : T₃ = (6:𝕂)⁻¹ • a^3 + (6:𝕂)⁻¹ • b^3 + (2:𝕂)⁻¹ • (a*b^2) +
            (2:𝕂)⁻¹ • (a^2*b) := by dsimp only
        have hSrest_eq : T₃ - E₁ - E₂ - Q = -(F₁+F₂+a*E₂+E₁*b+D₁*D₂) := by
          simp only [hT₃_exp, hQ_def, hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def,
            mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub,
            smul_add]; abel
        -- Component s⁴ bounds
        have hF₁s : ‖F₁‖ ≤ s^4 := le_trans (le_trans hF₁_le hFa4) (pow_le_pow_left₀ hα_nn hα_le 4)
        have hF₂s : ‖F₂‖ ≤ s^4 := le_trans (le_trans hF₂_le hFb4) (pow_le_pow_left₀ hβ_nn hβ_le 4)
        have haEs : ‖a*E₂‖ ≤ s^4 :=
          calc _ ≤ ‖a‖*‖E₂‖ := norm_mul_le _ _
            _ ≤ α*(β^3) := mul_le_mul_of_nonneg_left (le_trans hE₂_le hEb3) hα_nn
            _ ≤ s*s^3 := mul_le_mul hα_le (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) hs_nn
            _ = s^4 := by ring
        have hEbs : ‖E₁*b‖ ≤ s^4 :=
          calc _ ≤ ‖E₁‖*‖b‖ := norm_mul_le _ _
            _ ≤ (α^3)*β := mul_le_mul (le_trans hE₁_le hEa3) le_rfl hβ_nn (by positivity)
            _ ≤ s^3*s := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3) hβ_le (by positivity) (by positivity)
            _ = s^4 := by ring
        have hDDs : ‖D₁*D₂‖ ≤ s^4 :=
          calc _ ≤ ‖D₁‖*‖D₂‖ := norm_mul_le _ _
            _ ≤ (α^2)*(β^2) := mul_le_mul (le_trans hD₁_le hDa2) (le_trans hD₂_le hDb2)
                (norm_nonneg _) (by positivity)
            _ ≤ s^2*s^2 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
                (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
            _ = s^4 := by ring
        have hSrest_le : ‖T₃-E₁-E₂-Q‖ ≤ 5*s^4 := by
          rw [hSrest_eq, norm_neg]; linarith [norm_add_le F₁ F₂,
            norm_add_le (F₁+F₂) (a*E₂), norm_add_le (F₁+F₂+a*E₂) (E₁*b),
            norm_add_le (F₁+F₂+a*E₂+E₁*b) (D₁*D₂)]
        have h2_le : ‖(2:𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
        have h2eq : ‖(2:𝕂)⁻¹‖ = (2:ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
        have hP₂_le : ‖P₂‖ ≤ s^2 := by
          have h1 : ‖a*b‖ ≤ α*β := norm_mul_le _ _
          have h2 : ‖(2:𝕂)⁻¹•a^2‖ ≤ α^2 :=
            calc _ ≤ 1*‖a‖^2 := by
                  exact (norm_smul_le _ _).trans (mul_le_mul h2_le (norm_pow_le a 2)
                    (norm_nonneg _) (by norm_num))
              _ = α^2 := one_mul _
          have h3 : ‖(2:𝕂)⁻¹•b^2‖ ≤ β^2 :=
            calc _ ≤ 1*‖b‖^2 := by
                  exact (norm_smul_le _ _).trans (mul_le_mul h2_le (norm_pow_le b 2)
                    (norm_nonneg _) (by norm_num))
              _ = β^2 := one_mul _
          have hP₂_triangle : ‖P₂‖ ≤ ‖a*b‖ + ‖(2:𝕂)⁻¹•a^2‖ + ‖(2:𝕂)⁻¹•b^2‖ := by
            show ‖(a * b + (2 : 𝕂)⁻¹ • a ^ 2) + (2 : 𝕂)⁻¹ • b ^ 2‖ ≤ _
            have n1 := norm_add_le (a * b + (2 : 𝕂)⁻¹ • a ^ 2) ((2 : 𝕂)⁻¹ • b ^ 2)
            have n2 := norm_add_le (a * b) ((2 : 𝕂)⁻¹ • a ^ 2)
            linarith
          have hs2 : s^2 = α^2 + 2*α*β + β^2 := by rw [hs_def]; ring
          have hαβ : 0 ≤ α * β := mul_nonneg hα_nn hβ_nn
          linarith
        -- Group 5: ‖E₁E₂+½a²E₂+½E₁b²‖ ≤ 3s⁵
        have b5 : ‖E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2)‖ ≤ 3*s^5 := by
          have t1 : ‖E₁*E₂‖ ≤ s^5 :=
            calc _ ≤ (α^3)*(β^3) :=
                  (norm_mul_le _ _).trans (mul_le_mul (le_trans hE₁_le hEa3) (le_trans hE₂_le hEb3)
                    (norm_nonneg _) (by positivity))
              _ ≤ s^3*s^3 := mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
                  (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
              _ = s^6 := by ring
              _ ≤ s^5 := by nlinarith [pow_nonneg hs_nn 5]
          have t2 : ‖(2:𝕂)⁻¹•(a^2*E₂)‖ ≤ s^5 := by
            have ha2e : ‖a^2*E₂‖ ≤ α^2*β^3 :=
              calc _ ≤ ‖a^2‖*‖E₂‖ := norm_mul_le _ _
                _ ≤ (‖a‖^2)*(β^3) := mul_le_mul (norm_pow_le a 2)
                    (le_trans hE₂_le hEb3) (norm_nonneg _) (by positivity)
            calc _ ≤ 1*(α^2*β^3) :=
                  (norm_smul_le _ _).trans (mul_le_mul h2_le ha2e (norm_nonneg _) (by norm_num))
              _ ≤ s^2*s^3 := by
                  rw [one_mul]
                  exact mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 2)
                    (pow_le_pow_left₀ hβ_nn hβ_le 3) (by positivity) (by positivity)
              _ = s^5 := by ring
          have t3 : ‖(2:𝕂)⁻¹•(E₁*b^2)‖ ≤ s^5 := by
            have he1b : ‖E₁*b^2‖ ≤ α^3*β^2 :=
              calc _ ≤ ‖E₁‖*‖b^2‖ := norm_mul_le _ _
                _ ≤ (α^3)*(‖b‖^2) := mul_le_mul (le_trans hE₁_le hEa3)
                    (norm_pow_le b 2) (norm_nonneg _) (by positivity)
            calc _ ≤ 1*(α^3*β^2) :=
                  (norm_smul_le _ _).trans (mul_le_mul h2_le he1b (norm_nonneg _) (by norm_num))
              _ ≤ s^3*s^2 := by
                  rw [one_mul]
                  exact mul_le_mul (pow_le_pow_left₀ hα_nn hα_le 3)
                    (pow_le_pow_left₀ hβ_nn hβ_le 2) (by positivity) (by positivity)
              _ = s^5 := by ring
          linarith [norm_add_le (E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)) ((2:𝕂)⁻¹•(E₁*b^2)),
            norm_add_le (E₁*E₂) ((2:𝕂)⁻¹•(a^2*E₂))]
        -- Group 6: ‖½(z·Δ+Δ·z)‖ ≤ 5s⁵ where Δ=T₃-E₁-E₂-Q
        have b6 : ‖(2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z)‖ ≤ 5*s^5 := by
          have h1 : ‖z*(T₃-E₁-E₂-Q)‖ ≤ s*(5*s^4) :=
            (norm_mul_le _ _).trans (mul_le_mul hz_le hSrest_le (norm_nonneg _) hs_nn)
          have h2 : ‖(T₃-E₁-E₂-Q)*z‖ ≤ (5*s^4)*s :=
            (norm_mul_le _ _).trans (mul_le_mul hSrest_le hz_le (norm_nonneg _) (by positivity))
          have htri := norm_add_le (z*(T₃-E₁-E₂-Q)) ((T₃-E₁-E₂-Q)*z)
          have hsum : ‖z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z‖ ≤ 2*s*(5*s^4) := by linarith
          calc ‖(2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z)‖
              ≤ ‖(2:𝕂)⁻¹‖ * ‖z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z‖ := norm_smul_le _ _
            _ ≤ (2:ℝ)⁻¹ * (2*s*(5*s^4)) := by
                rw [h2eq]; exact mul_le_mul_of_nonneg_left hsum (by norm_num)
            _ = 5*s^5 := by ring
        -- Group 7: ‖½(P₂²-P²)‖ ≤ 6s⁵
        have b7 : ‖(2:𝕂)⁻¹•(P₂^2-P^2)‖ ≤ 6*s^5 := by
          have hPd : P₂^2-P^2 = -(P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2) := by
            have hp : P = P₂+(P-P₂) := by abel
            rw [hp]; noncomm_ring
          have hp1 : ‖P₂*(P-P₂)‖ ≤ s^2*(5*s^3) :=
            (norm_mul_le _ _).trans (mul_le_mul hP₂_le hS_le (norm_nonneg _) (by positivity))
          have hp2 : ‖(P-P₂)*P₂‖ ≤ (5*s^3)*s^2 :=
            (norm_mul_le _ _).trans (mul_le_mul hS_le hP₂_le (norm_nonneg _) (by positivity))
          have hp3 : ‖(P-P₂)^2‖ ≤ (5*s^3)^2 :=
            (norm_pow_le _ 2).trans (pow_le_pow_left₀ (norm_nonneg _) hS_le 2)
          rw [hPd, smul_neg, norm_neg]
          have ht1 := norm_add_le (P₂*(P-P₂)+(P-P₂)*P₂) ((P-P₂)^2)
          have ht2 := norm_add_le (P₂*(P-P₂)) ((P-P₂)*P₂)
          have hsum : ‖P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2‖ ≤ 2*s^2*(5*s^3)+(5*s^3)^2 := by
            linarith
          calc ‖(2:𝕂)⁻¹•(P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2)‖
              ≤ ‖(2:𝕂)⁻¹‖ * ‖P₂*(P-P₂)+(P-P₂)*P₂+(P-P₂)^2‖ := norm_smul_le _ _
            _ ≤ (2:ℝ)⁻¹ * (2*s^2*(5*s^3)+(5*s^3)^2) := by
                rw [h2eq]; exact mul_le_mul_of_nonneg_left hsum (by norm_num)
            _ ≤ 6*s^5 := by nlinarith [pow_nonneg hs_nn 5, pow_nonneg hs_nn 6]
        -- Final triangle inequality: 1+1+1+1+3+5+6 = 18 ≤ 20
        have n1 := norm_add_le G₁ G₂
        have n2 := norm_add_le (G₁+G₂) (a*F₂)
        have n3 := norm_add_le (G₁+G₂+a*F₂) (F₁*b)
        have n4 := norm_add_le (G₁+G₂+a*F₂+F₁*b) (E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2))
        have n5 := norm_add_le
          (G₁+G₂+a*F₂+F₁*b+(E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2)))
          ((2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z))
        have n6 := norm_add_le
          (G₁+G₂+a*F₂+F₁*b+(E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2))+
            (2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z))
          ((2:𝕂)⁻¹•(P₂^2-P^2))
        have hcomp_sum : ‖G₁‖+‖G₂‖+‖a*F₂‖+‖F₁*b‖+
              ‖E₁*E₂+(2:𝕂)⁻¹•(a^2*E₂)+(2:𝕂)⁻¹•(E₁*b^2)‖+
              ‖(2:𝕂)⁻¹•(z*(T₃-E₁-E₂-Q)+(T₃-E₁-E₂-Q)*z)‖+
              ‖(2:𝕂)⁻¹•(P₂^2-P^2)‖ ≤ 18 * s^5 := by
          linarith [hG₁_s5, hG₂_s5, haF₂, hF₁b, b5, b6, b7]
        linarith [hcomp_sum, pow_nonneg hs_nn 5]
      -- Group 2: ‖I₂-corr₂‖ ≤ 8s⁵ (I₂ refined by P→P₂+S)
      have hGroup2 : ‖I₂ - corr₂‖ ≤ 8 * s ^ 5 := by
        -- Factor out ⅓: I₂-corr₂ = ⅓•((y³-z³)-(z²P₂+zP₂z+P₂z²))
        -- Inner ring identity: using y=z+P, the inner expr equals
        -- z²(P-P₂)+z(P-P₂)z+(P-P₂)z²+zP²+PzP+P²z+P³
        have hy_zP : y = z + P := by simp only [hP_def, hz_def]; abel
        have hinner : y ^ 3 - z ^ 3 - (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2) =
            z ^ 2 * (P - P₂) + z * (P - P₂) * z + (P - P₂) * z ^ 2 +
            z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3 := by
          rw [hy_zP]; noncomm_ring
        have hI₂_alg : I₂ - corr₂ = (3 : 𝕂)⁻¹ •
            (z ^ 2 * (P - P₂) + z * (P - P₂) * z + (P - P₂) * z ^ 2 +
             z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3) := by
          -- Factor ⅓ from I₂-corr₂. Since y = P + z definitionally (by set defs),
          -- the ring identity hinner is verified by Lean's kernel.
          rw [hI₂_def, ← smul_sub, hinner]
        rw [hI₂_alg]
        -- Bound each of 7 terms using ‖P-P₂‖ ≤ 5s³, ‖P‖ ≤ s², ‖z‖ ≤ s
        have hSn : ‖P - P₂‖ ≤ 5 * s ^ 3 := hS_le
        -- Triangle inequality: ‖⅓•(sum)‖ ≤ ‖⅓‖·(sum of norms) ≤ 1·(sum of norms)
        have h3le : ‖(3 : 𝕂)⁻¹‖ ≤ 1 := by rw [norm_inv, RCLike.norm_ofNat]; norm_num
        -- Each term: z²S ≤ s²·5s³ = 5s⁵, zP² ≤ s·s⁴ = s⁵, P³ ≤ s⁶
        -- 7 terms: 3×5s⁵ + 3×s⁵ + s⁶ = 18s⁵+s⁶ ≤ 19s⁵
        -- With ‖⅓‖ ≤ 1: total ≤ 19s⁵ ≤ 8s⁵? NO — need tighter.
        -- Actually ‖⅓‖ = 1/3, so total ≤ ⅓·19s⁵ ≈ 6.3s⁵ ≤ 8s⁵ ✓
        -- But using ‖⅓‖ ≤ 1 gives 19s⁵ which is > 8s⁵.
        -- Use exact value: ‖⅓‖ = 1/3.
        have h3eq : ‖(3 : 𝕂)⁻¹‖ = (3 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
        calc _ ≤ ‖(3 : 𝕂)⁻¹‖ * ‖z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                (P - P₂) * z ^ 2 + z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3‖ :=
              norm_smul_le _ _
          _ ≤ (3 : ℝ)⁻¹ * (19 * s ^ 5) := by
              rw [h3eq]; gcongr
              -- Bound inner sum by 19s⁵ via triangle inequality
              have t1 : ‖z ^ 2 * (P - P₂)‖ ≤ 5 * s ^ 5 := by
                calc _ ≤ ‖z‖^2 * ‖P - P₂‖ := by
                      calc _ ≤ ‖z ^ 2‖ * _ := norm_mul_le _ _
                        _ ≤ _ := by gcongr; exact norm_pow_le z 2
                  _ ≤ s^2 * (5*s^3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
                      hSn (norm_nonneg _) (by positivity)
                  _ = _ := by ring
              have t2 : ‖z * (P - P₂) * z‖ ≤ 5 * s ^ 5 := by
                calc _ ≤ ‖z‖ * ‖P - P₂‖ * ‖z‖ := by
                      calc _ ≤ ‖z * (P - P₂)‖ * ‖z‖ := norm_mul_le _ _
                        _ ≤ _ := by gcongr; exact norm_mul_le _ _
                  _ ≤ s * (5*s^3) * s := mul_le_mul (mul_le_mul hz_le hSn (norm_nonneg _)
                      (by positivity)) hz_le (norm_nonneg _) (by positivity)
                  _ = _ := by ring
              have t3 : ‖(P - P₂) * z ^ 2‖ ≤ 5 * s ^ 5 := by
                calc _ ≤ ‖P - P₂‖ * ‖z‖^2 := by
                      calc _ ≤ _ * ‖z ^ 2‖ := norm_mul_le _ _
                        _ ≤ _ := by gcongr; exact norm_pow_le z 2
                  _ ≤ (5*s^3) * s^2 := mul_le_mul hSn (pow_le_pow_left₀ (norm_nonneg z)
                      hz_le 2) (by positivity) (by positivity)
                  _ = 5 * s ^ 5 := by ring
              have t4 : ‖z * P ^ 2‖ ≤ s ^ 5 := by
                calc _ ≤ ‖z‖ * ‖P ^ 2‖ := norm_mul_le _ _
                  _ ≤ ‖z‖ * ‖P‖ ^ 2 := by gcongr; exact norm_pow_le P 2
                  _ ≤ s * (s ^ 2) ^ 2 := by
                      exact mul_le_mul hz_le (pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 2)
                        (by positivity) hs_nn
                  _ = s ^ 5 := by ring
              have t5 : ‖P * z * P‖ ≤ s ^ 5 := by
                calc _ ≤ ‖P * z‖ * ‖P‖ := norm_mul_le _ _
                  _ ≤ (‖P‖ * ‖z‖) * ‖P‖ := by gcongr; exact norm_mul_le _ _
                  _ ≤ (s ^ 2 * s) * s ^ 2 := by
                      exact mul_le_mul (mul_le_mul hP_le_s2 hz_le (norm_nonneg _)
                        (by positivity)) hP_le_s2 (norm_nonneg _) (by positivity)
                  _ = s ^ 5 := by ring
              have t6 : ‖P ^ 2 * z‖ ≤ s ^ 5 := by
                calc _ ≤ ‖P ^ 2‖ * ‖z‖ := norm_mul_le _ _
                  _ ≤ ‖P‖ ^ 2 * ‖z‖ := by gcongr; exact norm_pow_le P 2
                  _ ≤ (s ^ 2) ^ 2 * s := by
                      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 2)
                        hz_le (norm_nonneg _) (by positivity)
                  _ = s ^ 5 := by ring
              have t7 : ‖P ^ 3‖ ≤ s ^ 5 := by
                calc _ ≤ ‖P‖^3 := norm_pow_le P 3
                  _ ≤ (s^2)^3 := pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 3
                  _ = s ^ 6 := by ring
                  _ ≤ s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
              -- Total via triangle inequality
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2 + z * P ^ 2 + P * z * P + P ^ 2 * z) (P ^ 3)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2 + z * P ^ 2 + P * z * P) (P ^ 2 * z)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2 + z * P ^ 2) (P * z * P)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z +
                  (P - P₂) * z ^ 2) (z * P ^ 2)
              have := norm_add_le (z ^ 2 * (P - P₂) + z * (P - P₂) * z) ((P - P₂) * z ^ 2)
              have := norm_add_le (z ^ 2 * (P - P₂)) (z * (P - P₂) * z)
              nlinarith
          _ ≤ 8 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
      -- Group 3: ¼‖y⁴-z⁴‖ ≤ ¼·15s⁵
      have hGroup3 : ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖ ≤ 4 * s ^ 5 :=
        calc _ ≤ ‖(4 : 𝕂)⁻¹‖ * ‖y ^ 4 - z ^ 4‖ := norm_smul_le _ _
          _ ≤ (4 : ℝ)⁻¹ * (15 * s ^ 5) := by
              have : ‖(4 : 𝕂)⁻¹‖ = (4 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
              rw [this]; exact mul_le_mul_of_nonneg_left hy4z4 (by norm_num)
          _ ≤ 4 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
      -- Combine via triangle inequality
      calc ‖(I₁ - corr₁) + (I₂ - corr₂) - (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖
          ≤ ‖(I₁ - corr₁) + (I₂ - corr₂)‖ + ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖ :=
            norm_sub_le _ _
        _ ≤ (‖I₁ - corr₁‖ + ‖I₂ - corr₂‖) + ‖(4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4)‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ (20 * s ^ 5 + 8 * s ^ 5) + 4 * s ^ 5 := by linarith
        _ = 32 * s ^ 5 := by ring
        _ ≤ 50 * s ^ 5 := by nlinarith [pow_nonneg hs_nn 5]
    -- Combine pieceA' + pieceB'
    have hE1_nn : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
    have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
      linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
    have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
      have h := Real.norm_exp_sub_one_sub_id_le
        (show ‖s‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
      rwa [Real.norm_eq_abs, abs_of_nonneg hEs_nn, Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
    have hexp5 : (Real.exp s - 1) ^ 5 ≤ 200 * s ^ 5 :=
      calc (Real.exp s - 1) ^ 5 ≤ (s + s ^ 2) ^ 5 := pow_le_pow_left₀ hE1_nn (by linarith) 5
        _ = s ^ 5 * (1 + s) ^ 5 := by ring
        _ ≤ s ^ 5 * 200 := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs_nn 5)
            have : (1 + s) ^ 5 ≤ (1 + 1) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
            linarith
        _ = 200 * s ^ 5 := by ring
    calc _ ≤ ‖logOnePlus (𝕂 := 𝕂) y - y + (2 : 𝕂)⁻¹ • y ^ 2 -
            (3 : 𝕂)⁻¹ • y ^ 3 + (4 : 𝕂)⁻¹ • y ^ 4‖ +
          ‖y - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
            (2 : 𝕂)⁻¹ • y ^ 2 + (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 -
            bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ := norm_add_le _ _
      _ ≤ (Real.exp s - 1) ^ 5 / (2 - Real.exp s) +
          2800 * s ^ 5 / (2 - Real.exp s) := by linarith [hpieceA, hpieceB]
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) := by
          calc _ = ((Real.exp s - 1) ^ 5 + 2800 * s ^ 5) / (2 - Real.exp s) := by rw [add_div]
            _ ≤ (200 * s ^ 5 + 2800 * s ^ 5) / (2 - Real.exp s) := by
                apply div_le_div_of_nonneg_right _ hdenom.le; linarith
            _ = 3000 * s ^ 5 / (2 - Real.exp s) := by ring_nf

include 𝕂 in
/-- **Sixth-order BCH remainder, large-s case** (private helper for the future
`norm_bch_sextic_remainder_le`).

Crude bound for `‖a‖+‖b‖ ≥ 1/10`: combines `norm_bch_quintic_remainder_le`
with `‖C₅‖ ≤ s⁵` to give

  `‖LHS_sextic‖ ≤ 3001·s⁵/(2-exp(s)) ≤ 100000·s⁶/(2-exp(s))`

(since `3001 ≤ 100000·s` when `s ≥ 1/10`).

This is the crude case of the full sextic remainder theorem. The full
theorem requires the small-s analytic case (`s < 1/10`), which uses
`sextic_pure_identity` for the deg-5 cancellation (~700 lines, deferred to
future session). See `claude/sextic_remainder_strategy.md`. -/
theorem norm_bch_sextic_remainder_large_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_large : 1 / 10 ≤ ‖a‖ + ‖b‖) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b‖ ≤
      100000 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hR₄ := norm_bch_quintic_remainder_le (𝕂 := 𝕂) a b hab
  have hC₅ : ‖bch_quintic_term 𝕂 a b‖ ≤ s ^ 5 := norm_bch_quintic_term_le a b
  -- Algebraic split: LHS_sextic = LHS_quintic - C₅
  have hLHS_eq : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b - bch_quintic_term 𝕂 a b =
      (bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
       bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b) - bch_quintic_term 𝕂 a b := by abel
  -- ‖LHS‖ ≤ 3000s⁵/(2-exp(s)) + s⁵ ≤ 3001 s⁵/(2-exp(s))
  have hLHS_3001 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b - bch_quintic_term 𝕂 a b‖ ≤
      3001 * s ^ 5 / (2 - Real.exp s) := by
    rw [hLHS_eq]
    calc _ ≤ ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b‖ + ‖bch_quintic_term 𝕂 a b‖ :=
        norm_sub_le _ _
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) + s ^ 5 := by linarith
      _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) + s ^ 5 / (2 - Real.exp s) := by
          gcongr; rw [le_div_iff₀ hdenom]
          nlinarith [pow_nonneg hs_nn 5]
      _ = 3001 * s ^ 5 / (2 - Real.exp s) := by ring
  -- Bound 3001·s⁵ ≤ 100000·s⁶ via 3001 ≤ 100000·s (using s ≥ 1/10)
  have h_le : 3001 * s ^ 5 ≤ 100000 * s ^ 6 := by
    have h3001 : 3001 ≤ 100000 * s := by linarith
    nlinarith [pow_nonneg hs_nn 5]
  calc _ ≤ 3001 * s ^ 5 / (2 - Real.exp s) := hLHS_3001
    _ ≤ 100000 * s ^ 6 / (2 - Real.exp s) :=
        div_le_div_of_nonneg_right h_le hdenom.le

include 𝕂 in
/-- **Seventh-order BCH remainder, large-s case** (private helper for the future
`norm_bch_septic_remainder_le`).

Crude bound for `‖a‖+‖b‖ ≥ 1/10`: combines `norm_bch_sextic_remainder_le`
with `‖bch_sextic_term‖ ≤ s⁶` to give

  `‖LHS_septic‖ ≤ 100001·s⁶/(2-exp(s)) ≤ 1000010·s⁷/(2-exp(s))`

(since `100001 ≤ 1000010·s` when `s ≥ 1/10`).

This is the crude case of the full septic remainder theorem. The full
theorem requires the small-s analytic case (`s < 1/10`), which uses
`septic_pure_identity` for the deg-6 cancellation (analog of the sextic
remainder pattern). -/
theorem norm_bch_septic_remainder_large_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_large : 1 / 10 ≤ ‖a‖ + ‖b‖) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b‖ ≤
      1000010 * (‖a‖ + ‖b‖) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hR₅ := norm_bch_sextic_remainder_large_s_le (𝕂 := 𝕂) a b hab hs_large
  have hC₆ : ‖bch_sextic_term 𝕂 a b‖ ≤ s ^ 6 := norm_bch_sextic_term_le a b
  -- Algebraic split: LHS_septic = LHS_sextic - bch_sextic_term
  have hLHS_eq : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b =
      (bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
       bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
       bch_quintic_term 𝕂 a b) - bch_sextic_term 𝕂 a b := by abel
  -- ‖LHS_septic‖ ≤ 100000·s⁶/(2-exp(s)) + s⁶ ≤ 100001·s⁶/(2-exp(s))
  have hLHS_100001 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b‖ ≤
      100001 * s ^ 6 / (2 - Real.exp s) := by
    rw [hLHS_eq]
    calc _ ≤ ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
          bch_quintic_term 𝕂 a b‖ + ‖bch_sextic_term 𝕂 a b‖ := norm_sub_le _ _
      _ ≤ 100000 * s ^ 6 / (2 - Real.exp s) + s ^ 6 := by linarith
      _ ≤ 100000 * s ^ 6 / (2 - Real.exp s) + s ^ 6 / (2 - Real.exp s) := by
          gcongr; rw [le_div_iff₀ hdenom]
          nlinarith [pow_nonneg hs_nn 6]
      _ = 100001 * s ^ 6 / (2 - Real.exp s) := by ring
  -- Bound 100001·s⁶ ≤ 1000010·s⁷ via 100001 ≤ 1000010·s (using s ≥ 1/10)
  have h_le : 100001 * s ^ 6 ≤ 1000010 * s ^ 7 := by
    have h100001 : (100001 : ℝ) ≤ 1000010 * s := by linarith
    nlinarith [pow_nonneg hs_nn 6]
  calc _ ≤ 100001 * s ^ 6 / (2 - Real.exp s) := hLHS_100001
    _ ≤ 1000010 * s ^ 7 / (2 - Real.exp s) :=
        div_le_div_of_nonneg_right h_le hdenom.le

include 𝕂 in
/-- **Eighth-order BCH remainder, large-s case** (private helper for the future
`norm_bch_octic_remainder_le`).

Crude bound for `‖a‖+‖b‖ ≥ 1/10`: combines `norm_bch_septic_remainder_large_s_le`
with `‖bch_septic_term‖ ≤ s⁷` to give

  `‖LHS_octic‖ ≤ 1000011·s⁷/(2-exp(s)) ≤ 10000110·s⁸/(2-exp(s))`

(since `1000011 ≤ 10000110·s` when `s ≥ 1/10`).

This is the crude case of the full octic remainder theorem. The full
theorem requires the small-s analytic case (`s < 1/10`), which will use
`octic_pure_identity` for the deg-7 cancellation (analog of the septic
remainder pattern).

Foundation for stepping stone 1 (`symmetric_bch_septic_sub_poly_axiom`)
discharge — the deg-9 analog of T2-F7e Phase A. -/
theorem norm_bch_octic_remainder_large_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_large : 1 / 10 ≤ ‖a‖ + ‖b‖) :
    ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
      bch_septic_term 𝕂 a b‖ ≤
      10000110 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set s := ‖a‖ + ‖b‖ with hs_def
  have hs_nn : 0 ≤ s := by positivity
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hdenom_le1 : 2 - Real.exp s ≤ 1 := by linarith [Real.add_one_le_exp s]
  have hR₆ := norm_bch_septic_remainder_large_s_le (𝕂 := 𝕂) a b hab hs_large
  have hZ₇ : ‖bch_septic_term 𝕂 a b‖ ≤ s ^ 7 := norm_bch_septic_term_le a b
  -- Algebraic split: LHS_octic = LHS_septic - bch_septic_term
  have hLHS_eq : bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
      bch_septic_term 𝕂 a b =
      (bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
       bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
       bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b) -
      bch_septic_term 𝕂 a b := by abel
  -- ‖LHS_octic‖ ≤ 1000010·s⁷/(2-exp(s)) + s⁷ ≤ 1000011·s⁷/(2-exp(s))
  have hLHS_1000011 : ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
      bch_septic_term 𝕂 a b‖ ≤
      1000011 * s ^ 7 / (2 - Real.exp s) := by
    rw [hLHS_eq]
    calc _ ≤ ‖bch (𝕂 := 𝕂) a b - (a + b) - (2 : 𝕂)⁻¹ • (a * b - b * a) -
          bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
          bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b‖ +
          ‖bch_septic_term 𝕂 a b‖ := norm_sub_le _ _
      _ ≤ 1000010 * s ^ 7 / (2 - Real.exp s) + s ^ 7 := by linarith
      _ ≤ 1000010 * s ^ 7 / (2 - Real.exp s) + s ^ 7 / (2 - Real.exp s) := by
          gcongr; rw [le_div_iff₀ hdenom]
          nlinarith [pow_nonneg hs_nn 7]
      _ = 1000011 * s ^ 7 / (2 - Real.exp s) := by ring
  -- Bound 1000011·s⁷ ≤ 10000110·s⁸ via 1000011 ≤ 10000110·s (using s ≥ 1/10)
  have h_le : 1000011 * s ^ 7 ≤ 10000110 * s ^ 8 := by
    have h1000011 : (1000011 : ℝ) ≤ 10000110 * s := by linarith
    nlinarith [pow_nonneg hs_nn 7]
  calc _ ≤ 1000011 * s ^ 7 / (2 - Real.exp s) := hLHS_1000011
    _ ≤ 10000110 * s ^ 8 / (2 - Real.exp s) :=
        div_le_div_of_nonneg_right h_le hdenom.le

/-! ### Sextic remainder small-s case helpers

These are building blocks for the (future) `norm_bch_sextic_remainder_small_s_le`
which handles `s < 1/10` via the deg-5 cancellation in `sextic_pure_identity`.

Each helper is a self-contained lemma about non-commutative algebra,
provable by `noncomm_ring` after scalar clearing.
-/

/-- 5-fold non-commutative telescoping: `y⁵ - (y - P)⁵` expands as a sum of
five 5-letter words, each with one `P` factor and four `y`/`(y-P)` factors. -/
private theorem pow5_sub_zpow5_telescope (y P : 𝔸) :
    y ^ 5 - (y - P) ^ 5 =
      y ^ 4 * P + y ^ 3 * P * (y - P) + y ^ 2 * P * (y - P) ^ 2 +
        y * P * (y - P) ^ 3 + P * (y - P) ^ 4 := by
  noncomm_ring

/-- 6-fold non-commutative telescoping: `y⁶ - (y - P)⁶` expands as a sum of
six 6-letter words, each with one `P` factor and five `y`/`(y-P)` factors. -/
private theorem pow6_sub_zpow6_telescope (y P : 𝔸) :
    y ^ 6 - (y - P) ^ 6 =
      y ^ 5 * P + y ^ 4 * P * (y - P) + y ^ 3 * P * (y - P) ^ 2 +
        y ^ 2 * P * (y - P) ^ 3 + y * P * (y - P) ^ 4 + P * (y - P) ^ 5 := by
  noncomm_ring

/-- 7-fold non-commutative telescoping: `y⁷ - (y - P)⁷` expands as a sum of
seven 7-letter words, each with one `P` factor and six `y`/`(y-P)` factors. -/
private theorem pow7_sub_zpow7_telescope (y P : 𝔸) :
    y ^ 7 - (y - P) ^ 7 =
      y ^ 6 * P + y ^ 5 * P * (y - P) + y ^ 4 * P * (y - P) ^ 2 +
        y ^ 3 * P * (y - P) ^ 3 + y ^ 2 * P * (y - P) ^ 4 +
        y * P * (y - P) ^ 5 + P * (y - P) ^ 6 := by
  noncomm_ring

/-- 8-fold non-commutative telescoping: `y⁸ - (y - P)⁸` expands as a sum of
eight 8-letter words, each with one `P` factor and seven `y`/`(y-P)` factors. -/
private theorem pow8_sub_zpow8_telescope (y P : 𝔸) :
    y ^ 8 - (y - P) ^ 8 =
      y ^ 7 * P + y ^ 6 * P * (y - P) + y ^ 5 * P * (y - P) ^ 2 +
        y ^ 4 * P * (y - P) ^ 3 + y ^ 3 * P * (y - P) ^ 4 +
        y ^ 2 * P * (y - P) ^ 5 + y * P * (y - P) ^ 6 + P * (y - P) ^ 7 := by
  noncomm_ring

/-- 4-fold non-commutative telescoping: `y⁴ - (y - P)⁴` expands as a sum of
four 4-letter words, each with one `P` factor and three `y`/`(y-P)` factors. -/
private theorem pow4_sub_zpow4_telescope (y P : 𝔸) :
    y ^ 4 - (y - P) ^ 4 =
      y ^ 3 * P + y ^ 2 * P * (y - P) + y * P * (y - P) ^ 2 + P * (y - P) ^ 3 := by
  noncomm_ring

/-- 3-fold non-commutative telescoping: `y³ - (y - P)³`. -/
private theorem pow3_sub_zpow3_telescope (y P : 𝔸) :
    y ^ 3 - (y - P) ^ 3 =
      y ^ 2 * P + y * P * (y - P) + P * (y - P) ^ 2 := by
  noncomm_ring

/-- Algebraic decomposition of `y⁴ - z⁴ - y4_5` where `z = y - P` and
`y4_5 = z³T₂ + z²T₂z + zT₂z² + T₂z³` is the deg-5 contribution from
`y⁴ = (z + T₂ + ...)⁴`. Expresses the difference as a sum of 7 deg-6+
terms in the BCH context where `‖y‖ ≤ 2s`, `‖P‖ ≤ s²`, `‖z‖ ≤ s`,
`‖P-T₂‖ ≤ 5s³`. -/
private theorem y4_sub_z4_sub_y4_5_decomp (y P T₂ : 𝔸) :
    y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) =
      (y - P) ^ 3 * (P - T₂) + (y - P) ^ 2 * (P - T₂) * (y - P) +
        (y - P) * (P - T₂) * (y - P) ^ 2 + (P - T₂) * (y - P) ^ 3 +
      (y ^ 3 - (y - P) ^ 3) * P + (y ^ 2 - (y - P) ^ 2) * P * (y - P) +
      P * P * (y - P) ^ 2 := by
  noncomm_ring

/-- Norm bound for the 5-fold telescoping: given `‖y‖ ≤ 2s`, `‖z‖ ≤ s`,
`‖P‖ ≤ s²`, `‖y⁵ - z⁵‖ ≤ 31·s⁶`. Used in the small-s case of the sextic
remainder bound. -/
theorem norm_pow5_sub_zpow5_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 5 - (y - P) ^ 5‖ ≤ 31 * s ^ 6 := by
  rw [pow5_sub_zpow5_telescope]
  -- 5 terms: y⁴P + y³P(y-P) + y²P(y-P)² + yP(y-P)³ + P(y-P)⁴
  -- Bounds: 16s⁶ + 8s⁶ + 4s⁶ + 2s⁶ + s⁶ = 31s⁶
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have h_y4P : ‖y ^ 4 * P‖ ≤ (2 * s) ^ 4 * s ^ 2 :=
    calc ‖y ^ 4 * P‖ ≤ ‖y ^ 4‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 4 * ‖P‖ := by gcongr; exact norm_pow_le y 4
      _ ≤ (2 * s) ^ 4 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 4) hP (by positivity) (by positivity)
  have h_y3Pz : ‖y ^ 3 * P * z‖ ≤ (2 * s) ^ 3 * s ^ 2 * s :=
    calc ‖y ^ 3 * P * z‖ ≤ ‖y ^ 3 * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 3 * ‖P‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le y 3
      _ ≤ ((2 * s) ^ 3 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 3) hP
            (norm_nonneg _) (by positivity)
  have h_y2Pz2 : ‖y ^ 2 * P * z ^ 2‖ ≤ (2 * s) ^ 2 * s ^ 2 * s ^ 2 :=
    calc ‖y ^ 2 * P * z ^ 2‖ ≤ ‖y ^ 2 * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 2 * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 2
          · exact norm_pow_le z 2
      _ ≤ ((2 * s) ^ 2 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (norm_nonneg _) (by positivity)
  have h_yPz3 : ‖y * P * z ^ 3‖ ≤ 2 * s * s ^ 2 * s ^ 3 :=
    calc ‖y * P * z ^ 3‖ ≤ ‖y * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ (2 * s * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz4 : ‖P * z ^ 4‖ ≤ s ^ 2 * s ^ 4 :=
    calc ‖P * z ^ 4‖ ≤ ‖P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 4 := by gcongr; exact norm_pow_le z 4
      _ ≤ s ^ 2 * s ^ 4 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
          (by positivity) (by positivity)
  -- Sum via triangle inequality
  have ht1 := norm_add_le (y ^ 4 * P + y ^ 3 * P * z + y ^ 2 * P * z ^ 2 + y * P * z ^ 3)
    (P * z ^ 4)
  have ht2 := norm_add_le (y ^ 4 * P + y ^ 3 * P * z + y ^ 2 * P * z ^ 2) (y * P * z ^ 3)
  have ht3 := norm_add_le (y ^ 4 * P + y ^ 3 * P * z) (y ^ 2 * P * z ^ 2)
  have ht4 := norm_add_le (y ^ 4 * P) (y ^ 3 * P * z)
  nlinarith [pow_nonneg hs_nn 6]

/-- Norm bound for the 6-fold telescoping: given `‖y‖ ≤ 2s`, `‖z‖ ≤ s`,
`‖P‖ ≤ s²`, `‖y⁶ - z⁶‖ ≤ 63·s⁷`. Used in the small-s case of the septic
remainder bound (analog of `norm_pow5_sub_zpow5_le` at one degree higher).

Per-term bounds: `(2s)⁵·s² + (2s)⁴·s²·s + (2s)³·s²·s² + (2s)²·s²·s³ +
                 (2s)·s²·s⁴ + s²·s⁵
                = 32s⁷ + 16s⁷ + 8s⁷ + 4s⁷ + 2s⁷ + s⁷ = 63s⁷`. -/
theorem norm_pow6_sub_zpow6_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 6 - (y - P) ^ 6‖ ≤ 63 * s ^ 7 := by
  rw [pow6_sub_zpow6_telescope]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- Six terms, bounded individually.
  have h_y5P : ‖y ^ 5 * P‖ ≤ (2 * s) ^ 5 * s ^ 2 :=
    calc ‖y ^ 5 * P‖ ≤ ‖y ^ 5‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 5 * ‖P‖ := by gcongr; exact norm_pow_le y 5
      _ ≤ (2 * s) ^ 5 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 5) hP (by positivity) (by positivity)
  have h_y4Pz : ‖y ^ 4 * P * z‖ ≤ (2 * s) ^ 4 * s ^ 2 * s :=
    calc ‖y ^ 4 * P * z‖ ≤ ‖y ^ 4 * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 4 * ‖P‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖y ^ 4‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le y 4
      _ ≤ ((2 * s) ^ 4 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 4) hP
            (norm_nonneg _) (by positivity)
  have h_y3Pz2 : ‖y ^ 3 * P * z ^ 2‖ ≤ (2 * s) ^ 3 * s ^ 2 * s ^ 2 :=
    calc ‖y ^ 3 * P * z ^ 2‖ ≤ ‖y ^ 3 * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 3 * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 3
          · exact norm_pow_le z 2
      _ ≤ ((2 * s) ^ 3 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 3) hP
            (norm_nonneg _) (by positivity)
  have h_y2Pz3 : ‖y ^ 2 * P * z ^ 3‖ ≤ (2 * s) ^ 2 * s ^ 2 * s ^ 3 :=
    calc ‖y ^ 2 * P * z ^ 3‖ ≤ ‖y ^ 2 * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 2 * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 2
          · exact norm_pow_le z 3
      _ ≤ ((2 * s) ^ 2 * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (norm_nonneg _) (by positivity)
  have h_yPz4 : ‖y * P * z ^ 4‖ ≤ 2 * s * s ^ 2 * s ^ 4 :=
    calc ‖y * P * z ^ 4‖ ≤ ‖y * P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ ^ 4 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 4
      _ ≤ (2 * s * s ^ 2) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz5 : ‖P * z ^ 5‖ ≤ s ^ 2 * s ^ 5 :=
    calc ‖P * z ^ 5‖ ≤ ‖P‖ * ‖z ^ 5‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 5 := by gcongr; exact norm_pow_le z 5
      _ ≤ s ^ 2 * s ^ 5 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 5)
          (by positivity) (by positivity)
  -- Sum via triangle inequality (5 norm_add_le applications)
  have ht1 := norm_add_le
    (y ^ 5 * P + y ^ 4 * P * z + y ^ 3 * P * z ^ 2 + y ^ 2 * P * z ^ 3 + y * P * z ^ 4)
    (P * z ^ 5)
  have ht2 := norm_add_le
    (y ^ 5 * P + y ^ 4 * P * z + y ^ 3 * P * z ^ 2 + y ^ 2 * P * z ^ 3) (y * P * z ^ 4)
  have ht3 := norm_add_le
    (y ^ 5 * P + y ^ 4 * P * z + y ^ 3 * P * z ^ 2) (y ^ 2 * P * z ^ 3)
  have ht4 := norm_add_le (y ^ 5 * P + y ^ 4 * P * z) (y ^ 3 * P * z ^ 2)
  have ht5 := norm_add_le (y ^ 5 * P) (y ^ 4 * P * z)
  nlinarith [pow_nonneg hs_nn 7]

/-- Norm bound for the 7-fold telescoping: given `‖y‖ ≤ 2s`, `‖z‖ ≤ s`,
`‖P‖ ≤ s²`, `‖y⁷ - z⁷‖ ≤ 127·s⁸`. Used in the small-s case of the octic
remainder bound (analog of `norm_pow6_sub_zpow6_le` at one degree higher).

Per-term bounds: `(2s)⁶·s² + (2s)⁵·s²·s + (2s)⁴·s²·s² + (2s)³·s²·s³ +
                 (2s)²·s²·s⁴ + (2s)·s²·s⁵ + s²·s⁶
                = 64s⁸ + 32s⁸ + 16s⁸ + 8s⁸ + 4s⁸ + 2s⁸ + s⁸ = 127s⁸`. -/
theorem norm_pow7_sub_zpow7_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 7 - (y - P) ^ 7‖ ≤ 127 * s ^ 8 := by
  rw [pow7_sub_zpow7_telescope]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- Seven terms, bounded individually.
  have h_y6P : ‖y ^ 6 * P‖ ≤ (2 * s) ^ 6 * s ^ 2 :=
    calc ‖y ^ 6 * P‖ ≤ ‖y ^ 6‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 6 * ‖P‖ := by gcongr; exact norm_pow_le y 6
      _ ≤ (2 * s) ^ 6 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 6) hP (by positivity) (by positivity)
  have h_y5Pz : ‖y ^ 5 * P * z‖ ≤ (2 * s) ^ 5 * s ^ 2 * s :=
    calc ‖y ^ 5 * P * z‖ ≤ ‖y ^ 5 * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 5 * ‖P‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖y ^ 5‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le y 5
      _ ≤ ((2 * s) ^ 5 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 5) hP
            (norm_nonneg _) (by positivity)
  have h_y4Pz2 : ‖y ^ 4 * P * z ^ 2‖ ≤ (2 * s) ^ 4 * s ^ 2 * s ^ 2 :=
    calc ‖y ^ 4 * P * z ^ 2‖ ≤ ‖y ^ 4 * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 4 * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖y ^ 4‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 4
          · exact norm_pow_le z 2
      _ ≤ ((2 * s) ^ 4 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 4) hP
            (norm_nonneg _) (by positivity)
  have h_y3Pz3 : ‖y ^ 3 * P * z ^ 3‖ ≤ (2 * s) ^ 3 * s ^ 2 * s ^ 3 :=
    calc ‖y ^ 3 * P * z ^ 3‖ ≤ ‖y ^ 3 * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 3 * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · calc _ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 3
          · exact norm_pow_le z 3
      _ ≤ ((2 * s) ^ 3 * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 3) hP
            (norm_nonneg _) (by positivity)
  have h_y2Pz4 : ‖y ^ 2 * P * z ^ 4‖ ≤ (2 * s) ^ 2 * s ^ 2 * s ^ 4 :=
    calc ‖y ^ 2 * P * z ^ 4‖ ≤ ‖y ^ 2 * P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 2 * ‖P‖) * ‖z‖ ^ 4 := by
          gcongr
          · calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 2
          · exact norm_pow_le z 4
      _ ≤ ((2 * s) ^ 2 * s ^ 2) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (norm_nonneg _) (by positivity)
  have h_yPz5 : ‖y * P * z ^ 5‖ ≤ 2 * s * s ^ 2 * s ^ 5 :=
    calc ‖y * P * z ^ 5‖ ≤ ‖y * P‖ * ‖z ^ 5‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ ^ 5 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 5
      _ ≤ (2 * s * s ^ 2) * s ^ 5 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 5)
            (by positivity) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz6 : ‖P * z ^ 6‖ ≤ s ^ 2 * s ^ 6 :=
    calc ‖P * z ^ 6‖ ≤ ‖P‖ * ‖z ^ 6‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 6 := by gcongr; exact norm_pow_le z 6
      _ ≤ s ^ 2 * s ^ 6 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 6)
          (by positivity) (by positivity)
  -- Sum via triangle inequality (6 norm_add_le applications)
  have ht1 := norm_add_le
    (y ^ 6 * P + y ^ 5 * P * z + y ^ 4 * P * z ^ 2 + y ^ 3 * P * z ^ 3 +
      y ^ 2 * P * z ^ 4 + y * P * z ^ 5) (P * z ^ 6)
  have ht2 := norm_add_le
    (y ^ 6 * P + y ^ 5 * P * z + y ^ 4 * P * z ^ 2 + y ^ 3 * P * z ^ 3 +
      y ^ 2 * P * z ^ 4) (y * P * z ^ 5)
  have ht3 := norm_add_le
    (y ^ 6 * P + y ^ 5 * P * z + y ^ 4 * P * z ^ 2 + y ^ 3 * P * z ^ 3)
    (y ^ 2 * P * z ^ 4)
  have ht4 := norm_add_le
    (y ^ 6 * P + y ^ 5 * P * z + y ^ 4 * P * z ^ 2) (y ^ 3 * P * z ^ 3)
  have ht5 := norm_add_le (y ^ 6 * P + y ^ 5 * P * z) (y ^ 4 * P * z ^ 2)
  have ht6 := norm_add_le (y ^ 6 * P) (y ^ 5 * P * z)
  nlinarith [pow_nonneg hs_nn 8]

/-- Norm bound for the 8-fold telescoping: given `‖y‖ ≤ 2s`, `‖z‖ ≤ s`,
`‖P‖ ≤ s²`, `‖y⁸ - z⁸‖ ≤ 255·s⁹`. Used for the future S₆ piece in the
deg-9-parent T2-F7e-octic discharge (analog of `norm_pow7_sub_zpow7_le` at
one degree higher).

Per-term bounds: `(2s)⁷·s² + (2s)⁶·s²·s + (2s)⁵·s²·s² + (2s)⁴·s²·s³ +
                 (2s)³·s²·s⁴ + (2s)²·s²·s⁵ + (2s)·s²·s⁶ + s²·s⁷
                = 128s⁹ + 64s⁹ + 32s⁹ + 16s⁹ + 8s⁹ + 4s⁹ + 2s⁹ + s⁹ = 255s⁹`. -/
private theorem norm_pow8_sub_zpow8_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 8 - (y - P) ^ 8‖ ≤ 255 * s ^ 9 := by
  rw [pow8_sub_zpow8_telescope]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- Eight terms, bounded individually.
  have h_y7P : ‖y ^ 7 * P‖ ≤ (2 * s) ^ 7 * s ^ 2 :=
    calc ‖y ^ 7 * P‖ ≤ ‖y ^ 7‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 7 * ‖P‖ := by gcongr; exact norm_pow_le y 7
      _ ≤ (2 * s) ^ 7 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 7) hP (by positivity) (by positivity)
  have h_y6Pz : ‖y ^ 6 * P * z‖ ≤ (2 * s) ^ 6 * s ^ 2 * s :=
    calc ‖y ^ 6 * P * z‖ ≤ ‖y ^ 6 * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 6 * ‖P‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖y ^ 6‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le y 6
      _ ≤ ((2 * s) ^ 6 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 6) hP
            (norm_nonneg _) (by positivity)
  have h_y5Pz2 : ‖y ^ 5 * P * z ^ 2‖ ≤ (2 * s) ^ 5 * s ^ 2 * s ^ 2 :=
    calc ‖y ^ 5 * P * z ^ 2‖ ≤ ‖y ^ 5 * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 5 * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖y ^ 5‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 5
          · exact norm_pow_le z 2
      _ ≤ ((2 * s) ^ 5 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 5) hP
            (norm_nonneg _) (by positivity)
  have h_y4Pz3 : ‖y ^ 4 * P * z ^ 3‖ ≤ (2 * s) ^ 4 * s ^ 2 * s ^ 3 :=
    calc ‖y ^ 4 * P * z ^ 3‖ ≤ ‖y ^ 4 * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 4 * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · calc _ ≤ ‖y ^ 4‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 4
          · exact norm_pow_le z 3
      _ ≤ ((2 * s) ^ 4 * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 4) hP
            (norm_nonneg _) (by positivity)
  have h_y3Pz4 : ‖y ^ 3 * P * z ^ 4‖ ≤ (2 * s) ^ 3 * s ^ 2 * s ^ 4 :=
    calc ‖y ^ 3 * P * z ^ 4‖ ≤ ‖y ^ 3 * P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 3 * ‖P‖) * ‖z‖ ^ 4 := by
          gcongr
          · calc _ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 3
          · exact norm_pow_le z 4
      _ ≤ ((2 * s) ^ 3 * s ^ 2) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 3) hP
            (norm_nonneg _) (by positivity)
  have h_y2Pz5 : ‖y ^ 2 * P * z ^ 5‖ ≤ (2 * s) ^ 2 * s ^ 2 * s ^ 5 :=
    calc ‖y ^ 2 * P * z ^ 5‖ ≤ ‖y ^ 2 * P‖ * ‖z ^ 5‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 2 * ‖P‖) * ‖z‖ ^ 5 := by
          gcongr
          · calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le y 2
          · exact norm_pow_le z 5
      _ ≤ ((2 * s) ^ 2 * s ^ 2) * s ^ 5 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 5)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (norm_nonneg _) (by positivity)
  have h_yPz6 : ‖y * P * z ^ 6‖ ≤ 2 * s * s ^ 2 * s ^ 6 :=
    calc ‖y * P * z ^ 6‖ ≤ ‖y * P‖ * ‖z ^ 6‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ ^ 6 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 6
      _ ≤ (2 * s * s ^ 2) * s ^ 6 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 6)
            (by positivity) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz7 : ‖P * z ^ 7‖ ≤ s ^ 2 * s ^ 7 :=
    calc ‖P * z ^ 7‖ ≤ ‖P‖ * ‖z ^ 7‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 7 := by gcongr; exact norm_pow_le z 7
      _ ≤ s ^ 2 * s ^ 7 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 7)
          (by positivity) (by positivity)
  -- Sum via triangle inequality (7 norm_add_le applications)
  have ht1 := norm_add_le
    (y ^ 7 * P + y ^ 6 * P * z + y ^ 5 * P * z ^ 2 + y ^ 4 * P * z ^ 3 +
      y ^ 3 * P * z ^ 4 + y ^ 2 * P * z ^ 5 + y * P * z ^ 6) (P * z ^ 7)
  have ht2 := norm_add_le
    (y ^ 7 * P + y ^ 6 * P * z + y ^ 5 * P * z ^ 2 + y ^ 4 * P * z ^ 3 +
      y ^ 3 * P * z ^ 4 + y ^ 2 * P * z ^ 5) (y * P * z ^ 6)
  have ht3 := norm_add_le
    (y ^ 7 * P + y ^ 6 * P * z + y ^ 5 * P * z ^ 2 + y ^ 4 * P * z ^ 3 +
      y ^ 3 * P * z ^ 4) (y ^ 2 * P * z ^ 5)
  have ht4 := norm_add_le
    (y ^ 7 * P + y ^ 6 * P * z + y ^ 5 * P * z ^ 2 + y ^ 4 * P * z ^ 3)
    (y ^ 3 * P * z ^ 4)
  have ht5 := norm_add_le
    (y ^ 7 * P + y ^ 6 * P * z + y ^ 5 * P * z ^ 2) (y ^ 4 * P * z ^ 3)
  have ht6 := norm_add_le (y ^ 7 * P + y ^ 6 * P * z) (y ^ 5 * P * z ^ 2)
  have ht7 := norm_add_le (y ^ 7 * P) (y ^ 6 * P * z)
  nlinarith [pow_nonneg hs_nn 9]

/-- Norm bound for `y² - z²` (2-fold telescoping) where `z = y - P`,
given `‖y‖ ≤ 2s`, `‖P‖ ≤ s²`, `‖z‖ ≤ s`. -/
private theorem norm_pow2_sub_zpow2_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 2 - (y - P) ^ 2‖ ≤ 3 * s ^ 3 := by
  have hY2_eq : y ^ 2 - (y - P) ^ 2 = y * P + P * (y - P) := by noncomm_ring
  rw [hY2_eq]
  have h_yP : ‖y * P‖ ≤ 2 * s * s ^ 2 :=
    calc ‖y * P‖ ≤ ‖y‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ 2 * s * s ^ 2 := mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz : ‖P * (y - P)‖ ≤ s ^ 2 * s :=
    calc ‖P * (y - P)‖ ≤ ‖P‖ * ‖y - P‖ := norm_mul_le _ _
      _ ≤ s ^ 2 * s := mul_le_mul hP hz (norm_nonneg _) (by positivity)
  calc ‖y * P + P * (y - P)‖ ≤ ‖y * P‖ + ‖P * (y - P)‖ := norm_add_le _ _
    _ ≤ 2 * s * s ^ 2 + s ^ 2 * s := by linarith
    _ = 3 * s ^ 3 := by ring

/-- Norm bound for `y³ - z³` (3-fold telescoping). -/
private theorem norm_pow3_sub_zpow3_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 3 - (y - P) ^ 3‖ ≤ 7 * s ^ 4 := by
  rw [pow3_sub_zpow3_telescope]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have h_y2P : ‖y ^ 2 * P‖ ≤ (2 * s) ^ 2 * s ^ 2 :=
    calc ‖y ^ 2 * P‖ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 2 * ‖P‖ := by gcongr; exact norm_pow_le y 2
      _ ≤ (2 * s) ^ 2 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (by positivity) (by positivity)
  have h_yPz : ‖y * P * z‖ ≤ 2 * s * s ^ 2 * s :=
    calc ‖y * P * z‖ ≤ ‖y * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (2 * s * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz2 : ‖P * z ^ 2‖ ≤ s ^ 2 * s ^ 2 :=
    calc ‖P * z ^ 2‖ ≤ ‖P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * s ^ 2 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
          (by positivity) (by positivity)
  have ht1 := norm_add_le (y ^ 2 * P + y * P * z) (P * z ^ 2)
  have ht2 := norm_add_le (y ^ 2 * P) (y * P * z)
  nlinarith

/-- Norm bound for `y⁴ - z⁴` (4-fold telescoping) where `z = y - P`,
given `‖y‖ ≤ 2s`, `‖P‖ ≤ s²`, `‖z‖ ≤ s`. Bounds: `(2s)³·s² + (2s)²·s²·s +
(2s)·s²·s² + s²·s³ = 8s⁵ + 4s⁵ + 2s⁵ + s⁵ = 15s⁵`. -/
private theorem norm_pow4_sub_zpow4_le (y P : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) :
    ‖y ^ 4 - (y - P) ^ 4‖ ≤ 15 * s ^ 5 := by
  rw [pow4_sub_zpow4_telescope]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have h_y3P : ‖y ^ 3 * P‖ ≤ (2 * s) ^ 3 * s ^ 2 :=
    calc ‖y ^ 3 * P‖ ≤ ‖y ^ 3‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖y‖ ^ 3 * ‖P‖ := by gcongr; exact norm_pow_le y 3
      _ ≤ (2 * s) ^ 3 * s ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 3) hP (by positivity) (by positivity)
  have h_y2Pz : ‖y ^ 2 * P * z‖ ≤ (2 * s) ^ 2 * s ^ 2 * s :=
    calc ‖y ^ 2 * P * z‖ ≤ ‖y ^ 2 * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y‖ ^ 2 * ‖P‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖y ^ 2‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le y 2
      _ ≤ ((2 * s) ^ 2 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hy 2) hP
            (norm_nonneg _) (by positivity)
  have h_yPz2 : ‖y * P * z ^ 2‖ ≤ 2 * s * s ^ 2 * s ^ 2 :=
    calc ‖y * P * z ^ 2‖ ≤ ‖y * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (2 * s * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hy hP (norm_nonneg _) (by positivity)
  have h_Pz3 : ‖P * z ^ 3‖ ≤ s ^ 2 * s ^ 3 :=
    calc ‖P * z ^ 3‖ ≤ ‖P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * ‖z‖ ^ 3 := by gcongr; exact norm_pow_le z 3
      _ ≤ s ^ 2 * s ^ 3 := mul_le_mul hP (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
          (by positivity) (by positivity)
  have ht1 := norm_add_le (y ^ 3 * P + y ^ 2 * P * z + y * P * z ^ 2) (P * z ^ 3)
  have ht2 := norm_add_le (y ^ 3 * P + y ^ 2 * P * z) (y * P * z ^ 2)
  have ht3 := norm_add_le (y ^ 3 * P) (y ^ 2 * P * z)
  nlinarith [pow_nonneg hs_nn 5]

/-- Norm bound for `y⁴ - z⁴ - y4_5` where `y4_5 = z³T₂ + z²T₂z + zT₂z² + T₂z³`,
given the BCH-context norm bounds. The bound is `31·s⁶`. -/
theorem norm_y4_sub_z4_sub_y4_5_le (y P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3)‖ ≤ 31 * s ^ 6 := by
  rw [y4_sub_z4_sub_y4_5_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- 7 terms to bound
  -- (y-P)^3 (P-T₂) etc.: ≤ s^3 * 5s^3 = 5s^6, four of these = 20s^6
  have h_z3PT : ‖z ^ 3 * (P - T₂)‖ ≤ s ^ 3 * (5 * s ^ 3) :=
    calc ‖z ^ 3 * (P - T₂)‖ ≤ ‖z ^ 3‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 3 * ‖P - T₂‖ := by gcongr; exact norm_pow_le z 3
      _ ≤ s ^ 3 * (5 * s ^ 3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
          hPmT₂ (norm_nonneg _) (by positivity)
  have h_z2PTz : ‖z ^ 2 * (P - T₂) * z‖ ≤ s ^ 2 * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z ^ 2 * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ (s ^ 2 * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂
            (norm_nonneg _) (by positivity)
  have h_zPTz2 : ‖z * (P - T₂) * z ^ 2‖ ≤ s * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖z * (P - T₂)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (s * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  have h_PTz3 : ‖(P - T₂) * z ^ 3‖ ≤ (5 * s ^ 3) * s ^ 3 :=
    calc _ ≤ ‖P - T₂‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ * ‖z‖ ^ 3 := by gcongr; exact norm_pow_le z 3
      _ ≤ (5 * s ^ 3) * s ^ 3 := mul_le_mul hPmT₂
          (pow_le_pow_left₀ (norm_nonneg _) hzn 3) (by positivity) (by positivity)
  -- (y³ - z³) P term
  have hy3z3 := norm_pow3_sub_zpow3_le y P hs_nn hy hz hP
  have h_y3z3P : ‖(y ^ 3 - z ^ 3) * P‖ ≤ (7 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖y ^ 3 - z ^ 3‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (7 * s ^ 4) * s ^ 2 :=
          mul_le_mul hy3z3 hP (norm_nonneg _) (by positivity)
  -- (y² - z²) P z term
  have hy2z2 := norm_pow2_sub_zpow2_le y P hs_nn hy hz hP
  have h_y2z2Pz : ‖(y ^ 2 - z ^ 2) * P * z‖ ≤ (3 * s ^ 3) * s ^ 2 * s :=
    calc _ ≤ ‖(y ^ 2 - z ^ 2) * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 2 - z ^ 2‖ * ‖P‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((3 * s ^ 3) * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy2z2 hP (norm_nonneg _) (by positivity)
  -- P · P · z² term (note: P*P*z² in the decomp formula)
  have h_PPz2 : ‖P * P * z ^ 2‖ ≤ s ^ 2 * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖P * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖P‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (s ^ 2 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hP hP (norm_nonneg _) (by positivity)
  -- Sum via triangle inequality (7 terms)
  have ht := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2 + (P - T₂) * z ^ 3 +
      (y ^ 3 - z ^ 3) * P + (y ^ 2 - z ^ 2) * P * z) (P * P * z ^ 2)
  have ht2 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2 + (P - T₂) * z ^ 3 +
      (y ^ 3 - z ^ 3) * P) ((y ^ 2 - z ^ 2) * P * z)
  have ht3 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2 + (P - T₂) * z ^ 3)
    ((y ^ 3 - z ^ 3) * P)
  have ht4 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z + z * (P - T₂) * z ^ 2)
    ((P - T₂) * z ^ 3)
  have ht5 := norm_add_le
    (z ^ 3 * (P - T₂) + z ^ 2 * (P - T₂) * z) (z * (P - T₂) * z ^ 2)
  have ht6 := norm_add_le (z ^ 3 * (P - T₂)) (z ^ 2 * (P - T₂) * z)
  nlinarith [pow_nonneg hs_nn 6]

/-- Algebraic decomposition of `y⁴ - z⁴ - y4_5 - y4_6` where `z = y - P`,
`y4_5 = z³T₂ + z²T₂z + zT₂z² + T₂z³` is the deg-5 leading contribution
to `y⁴ = (z + T₂ + T₃ + …)⁴`, and `y4_6` is the deg-6 contribution.

`y4_6` has 10 terms: 4 with `T₃` (the `(1,1,1,3)` perms `z^i·T₃·z^j`) plus
6 with `T₂²` (the `(1,1,2,2)` perms `z^i·T₂·z^j·T₂·z^k` with `i+j+k=2`).

Expresses the difference as 16 deg-7+ terms:
- 4 weight-1 terms `z^i·(P-T₂-T₃)·z^j` (the `T₃` correction completes `P-T₂` to `P-T₂-T₃`).
- 7 terms from `(y³-z³)·P − (z²T₂² + zT₂zT₂ + T₂z²T₂)`:
  `(y²-z²)·P²`, `z²·(P²-T₂²)`, `P²·z·P`,
  `z·(P-T₂)·z·P + z·T₂·z·(P-T₂)`,
  `(P-T₂)·z²·P + T₂·z²·(P-T₂)`.
- 4 terms from `(y²-z²)·P·z − (zT₂²z + T₂zT₂z)`:
  `P³·z`, `z·(P²-T₂²)·z`,
  `(P-T₂)·z·P·z + T₂·z·(P-T₂)·z`.
- 1 term from `P²·z² − T₂²·z²`: `(P²-T₂²)·z²`.

Each is bounded by ≤ 10·s⁷ (or less) in the BCH context where
`‖y‖ ≤ 2s, ‖z‖ ≤ s, ‖P‖ ≤ s², ‖T₂‖ ≤ s², ‖P-T₂‖ ≤ 5s³, ‖P-T₂-T₃‖ ≤ 5s⁴`. -/
private theorem y4_sub_z4_sub_y4_5_sub_y4_6_decomp (y P T₂ T₃ : 𝔸) :
    y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) -
      ((y - P) ^ 3 * T₃ + (y - P) ^ 2 * T₃ * (y - P) +
        (y - P) * T₃ * (y - P) ^ 2 + T₃ * (y - P) ^ 3 +
        (y - P) ^ 2 * T₂ ^ 2 + (y - P) * T₂ * (y - P) * T₂ +
        (y - P) * T₂ ^ 2 * (y - P) +
        T₂ * (y - P) ^ 2 * T₂ + T₂ * (y - P) * T₂ * (y - P) + T₂ ^ 2 * (y - P) ^ 2) =
    (y - P) ^ 3 * (P - T₂ - T₃) + (y - P) ^ 2 * (P - T₂ - T₃) * (y - P) +
      (y - P) * (P - T₂ - T₃) * (y - P) ^ 2 + (P - T₂ - T₃) * (y - P) ^ 3 +
    (y ^ 2 - (y - P) ^ 2) * P ^ 2 +
    (y - P) ^ 2 * (P ^ 2 - T₂ ^ 2) +
    P ^ 2 * (y - P) * P +
    (y - P) * (P - T₂) * (y - P) * P + (y - P) * T₂ * (y - P) * (P - T₂) +
    (P - T₂) * (y - P) ^ 2 * P + T₂ * (y - P) ^ 2 * (P - T₂) +
    P ^ 3 * (y - P) +
    (y - P) * (P ^ 2 - T₂ ^ 2) * (y - P) +
    (P - T₂) * (y - P) * P * (y - P) + T₂ * (y - P) * (P - T₂) * (y - P) +
    (P ^ 2 - T₂ ^ 2) * (y - P) ^ 2 := by
  noncomm_ring

/-- Algebraic decomposition of `y⁴ - z⁴ - y4_5 - y4_6 - y4_7` where `z = y - P`.

Extends `y4_sub_z4_sub_y4_5_sub_y4_6_decomp` by subtracting the deg-7 contribution
`y4_7` (20 terms from compositions `(k₁,k₂,k₃,k₄) ⊢ 7, kᵢ ≥ 1`):
- 4 with `T₄` at position `p` (the `(1,1,1,4)` perms)
- 12 with one `T₂` and one `T₃` at non-trivial positions (`(1,1,2,3)` perms)
- 4 with `T₂³` at three positions (`(1,2,2,2)` perms)

Each `y4_7` item is exactly the deg-7 leading of one of the 16 terms in the
septic decomposition; absorbing them yields 24 deg-8+ terms. Used as the
`S₃'` piece bound in the octic small-s discharge (analog of
`y4_sub_z4_sub_y4_5_sub_y4_6_decomp` at one degree higher). -/
private theorem y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_decomp
    (y P T₂ T₃ T₄ : 𝔸) :
    y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) -
      ((y - P) ^ 3 * T₃ + (y - P) ^ 2 * T₃ * (y - P) +
        (y - P) * T₃ * (y - P) ^ 2 + T₃ * (y - P) ^ 3 +
        (y - P) ^ 2 * T₂ ^ 2 + (y - P) * T₂ * (y - P) * T₂ +
        (y - P) * T₂ ^ 2 * (y - P) +
        T₂ * (y - P) ^ 2 * T₂ + T₂ * (y - P) * T₂ * (y - P) +
        T₂ ^ 2 * (y - P) ^ 2) -
      ((y - P) * (y - P) * (y - P) * T₄ +
        (y - P) * (y - P) * T₂ * T₃ +
        (y - P) * (y - P) * T₃ * T₂ +
        (y - P) * (y - P) * T₄ * (y - P) +
        (y - P) * T₂ * (y - P) * T₃ +
        (y - P) * T₂ * T₂ * T₂ +
        (y - P) * T₂ * T₃ * (y - P) +
        (y - P) * T₃ * (y - P) * T₂ +
        (y - P) * T₃ * T₂ * (y - P) +
        (y - P) * T₄ * (y - P) * (y - P) +
        T₂ * (y - P) * (y - P) * T₃ +
        T₂ * (y - P) * T₂ * T₂ +
        T₂ * (y - P) * T₃ * (y - P) +
        T₂ * T₂ * (y - P) * T₂ +
        T₂ * T₂ * T₂ * (y - P) +
        T₂ * T₃ * (y - P) * (y - P) +
        T₃ * (y - P) * (y - P) * T₂ +
        T₃ * (y - P) * T₂ * (y - P) +
        T₃ * T₂ * (y - P) * (y - P) +
        T₄ * (y - P) * (y - P) * (y - P)) =
    -- Group A: 4 (P-T₂-T₃-T₄) middle terms (absorbs 4 T₄-perms)
    (y - P) ^ 3 * (P - T₂ - T₃ - T₄) +
      (y - P) ^ 2 * (P - T₂ - T₃ - T₄) * (y - P) +
      (y - P) * (P - T₂ - T₃ - T₄) * (y - P) ^ 2 +
      (P - T₂ - T₃ - T₄) * (y - P) ^ 3 +
    -- Group B5: 4 terms from `(y²-z²)·P²` split (absorbs items z·T₂³, T₂·z·T₂²)
    (y - P) * (P ^ 3 - T₂ ^ 3) +
    T₂ * (y - P) * (P ^ 2 - T₂ ^ 2) +
    (P - T₂) * (y - P) * P ^ 2 +
    P ^ 4 +
    -- Group B6: 1 extended term (absorbs z²·T₂T₃, z²·T₃T₂)
    (y - P) ^ 2 * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) +
    -- Group B7: 3 terms from `P²·z·P` split (absorbs T₂²·z·T₂)
    T₂ ^ 2 * (y - P) * (P - T₂) +
    (P ^ 2 - T₂ ^ 2) * (y - P) * T₂ +
    (P ^ 2 - T₂ ^ 2) * (y - P) * (P - T₂) +
    -- Group B8: 2 terms (absorbs z·T₃·z·T₂)
    (y - P) * (P - T₂ - T₃) * (y - P) * T₂ +
    (y - P) * (P - T₂) * (y - P) * (P - T₂) +
    -- Group B9: 1 extended term (absorbs z·T₂·z·T₃)
    (y - P) * T₂ * (y - P) * (P - T₂ - T₃) +
    -- Group B10: 2 terms (absorbs T₃·z²·T₂)
    (P - T₂ - T₃) * (y - P) ^ 2 * T₂ +
    (P - T₂) * (y - P) ^ 2 * (P - T₂) +
    -- Group B11: 1 extended term (absorbs T₂·z²·T₃)
    T₂ * (y - P) ^ 2 * (P - T₂ - T₃) +
    -- Group B12: 1 extended term `(P³-T₂³)·z` (absorbs T₂³·z)
    (P ^ 3 - T₂ ^ 3) * (y - P) +
    -- Group B13: 1 extended term (absorbs z·T₂T₃·z, z·T₃T₂·z)
    (y - P) * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * (y - P) +
    -- Group B14: 2 terms (absorbs T₃·z·T₂·z)
    (P - T₂ - T₃) * (y - P) * T₂ * (y - P) +
    (P - T₂) * (y - P) * (P - T₂) * (y - P) +
    -- Group B15: 1 extended term (absorbs T₂·z·T₃·z)
    T₂ * (y - P) * (P - T₂ - T₃) * (y - P) +
    -- Group B16: 1 extended term (absorbs T₂T₃·z², T₃T₂·z²)
    (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * (y - P) ^ 2 := by
  noncomm_ring

/-- Algebraic decomposition of `y⁵ - z⁵ - y5_6` where `z = y - P` and
`y5_6 = z⁴T₂ + z³T₂z + z²T₂z² + zT₂z³ + T₂z⁴` is the deg-6 contribution
to `y⁵ = (z + T₂ + ...)⁵` (the (1,1,1,1,2) perms). Each term is deg-7+
in the BCH context. -/
private theorem y5_sub_z5_sub_y5_6_decomp (y P T₂ : 𝔸) :
    y ^ 5 - (y - P) ^ 5 -
      ((y - P) ^ 4 * T₂ + (y - P) ^ 3 * T₂ * (y - P) +
        (y - P) ^ 2 * T₂ * (y - P) ^ 2 + (y - P) * T₂ * (y - P) ^ 3 +
        T₂ * (y - P) ^ 4) =
      (y ^ 4 - (y - P) ^ 4) * P + (y - P) ^ 4 * (P - T₂) +
      (y ^ 3 - (y - P) ^ 3) * P * (y - P) + (y - P) ^ 3 * (P - T₂) * (y - P) +
      (y ^ 2 - (y - P) ^ 2) * P * (y - P) ^ 2 +
        (y - P) ^ 2 * (P - T₂) * (y - P) ^ 2 +
      P * P * (y - P) ^ 3 + (y - P) * (P - T₂) * (y - P) ^ 3 +
      (P - T₂) * (y - P) ^ 4 := by
  noncomm_ring

/-- Algebraic decomposition of `y⁵ - z⁵ - y5_6 - y5_7` where `z = y - P`.

Extends `y5_sub_z5_sub_y5_6_decomp` by subtracting the deg-7 contribution
`y5_7` (15 terms from compositions `(k₁,..,k₅) ⊢ 7, kᵢ ≥ 1`):
- 5 with T₃ at one position (`(1,1,1,1,3)` perms)
- 10 with T₂ at two positions (`(1,1,1,2,2)` perms)

Each `y5_7` item is the deg-7 leading of one of the 9 terms in the septic
decomposition. Absorbing yields 18 deg-8+ terms:
- 5 weight-1 (P-T₂-T₃) middle terms (absorb 5 T₃-perms).
- (y⁴-z⁴-y4_5)·P + 4 perms of y4_5·(P-T₂) (absorb 4 (T₂ at positions p,5) items).
- (y³-z³-y3_4)·P·z + 3 perms of y3_4·(P-T₂)·z (absorb 3 (T₂ at positions p,4) items).
- (y²-z²-y2_3)·P·z² + 2 perms of y2_3·(P-T₂)·z² (absorb 2 (T₂ at positions p,3) items).
- (P²-T₂²)·z³ (absorbs T₂²·z³). -/
private theorem y5_sub_z5_sub_y5_6_sub_y5_7_decomp (y P T₂ T₃ : 𝔸) :
    y ^ 5 - (y - P) ^ 5 -
      ((y - P) ^ 4 * T₂ + (y - P) ^ 3 * T₂ * (y - P) +
        (y - P) ^ 2 * T₂ * (y - P) ^ 2 + (y - P) * T₂ * (y - P) ^ 3 +
        T₂ * (y - P) ^ 4) -
      ((y - P) * (y - P) * (y - P) * (y - P) * T₃ +
        (y - P) * (y - P) * (y - P) * T₃ * (y - P) +
        (y - P) * (y - P) * T₃ * (y - P) * (y - P) +
        (y - P) * T₃ * (y - P) * (y - P) * (y - P) +
        T₃ * (y - P) * (y - P) * (y - P) * (y - P) +
        (y - P) * (y - P) * (y - P) * T₂ * T₂ +
        (y - P) * (y - P) * T₂ * (y - P) * T₂ +
        (y - P) * (y - P) * T₂ * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) * (y - P) * T₂ +
        (y - P) * T₂ * (y - P) * T₂ * (y - P) +
        (y - P) * T₂ * T₂ * (y - P) * (y - P) +
        T₂ * (y - P) * (y - P) * (y - P) * T₂ +
        T₂ * (y - P) * (y - P) * T₂ * (y - P) +
        T₂ * (y - P) * T₂ * (y - P) * (y - P) +
        T₂ * T₂ * (y - P) * (y - P) * (y - P)) =
    -- 5 (P-T₂-T₃) middle terms (absorbs 5 T₃-perms).
    (y - P) ^ 4 * (P - T₂ - T₃) +
    (y - P) ^ 3 * (P - T₂ - T₃) * (y - P) +
    (y - P) ^ 2 * (P - T₂ - T₃) * (y - P) ^ 2 +
    (y - P) * (P - T₂ - T₃) * (y - P) ^ 3 +
    (P - T₂ - T₃) * (y - P) ^ 4 +
    -- (y⁴-z⁴-y4_5)·P (1 compound term)
    (y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3)) * P +
    -- 4 perms of y4_5·(P-T₂)
    (y - P) ^ 3 * T₂ * (P - T₂) +
    (y - P) ^ 2 * T₂ * (y - P) * (P - T₂) +
    (y - P) * T₂ * (y - P) ^ 2 * (P - T₂) +
    T₂ * (y - P) ^ 3 * (P - T₂) +
    -- (y³-z³-y3_4)·P·z (1 compound term)
    (y ^ 3 - (y - P) ^ 3 -
      ((y - P) ^ 2 * T₂ + (y - P) * T₂ * (y - P) + T₂ * (y - P) ^ 2)) * P * (y - P) +
    -- 3 perms of y3_4·(P-T₂)·z
    (y - P) ^ 2 * T₂ * (P - T₂) * (y - P) +
    (y - P) * T₂ * (y - P) * (P - T₂) * (y - P) +
    T₂ * (y - P) ^ 2 * (P - T₂) * (y - P) +
    -- (y²-z²-y2_3)·P·z² (1 compound term)
    (y ^ 2 - (y - P) ^ 2 - ((y - P) * T₂ + T₂ * (y - P))) * P * (y - P) ^ 2 +
    -- 2 perms of y2_3·(P-T₂)·z²
    (y - P) * T₂ * (P - T₂) * (y - P) ^ 2 +
    T₂ * (y - P) * (P - T₂) * (y - P) ^ 2 +
    -- (P²-T₂²)·z³ (absorbs T₂²·z³)
    (P ^ 2 - T₂ ^ 2) * (y - P) ^ 3 := by
  noncomm_ring

/-- Norm bound for `y⁵ - z⁵ - y5_6`: each of the 9 terms is deg-7+;
total bound `≤ 51·s⁷`. Used in the small-s case of the septic remainder
(analog of `norm_y4_sub_z4_sub_y4_5_le` at one degree higher). -/
theorem norm_y5_sub_z5_sub_y5_6_le (y P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖y ^ 5 - (y - P) ^ 5 -
      ((y - P) ^ 4 * T₂ + (y - P) ^ 3 * T₂ * (y - P) +
        (y - P) ^ 2 * T₂ * (y - P) ^ 2 + (y - P) * T₂ * (y - P) ^ 3 +
        T₂ * (y - P) ^ 4)‖ ≤ 51 * s ^ 7 := by
  rw [y5_sub_z5_sub_y5_6_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have hy4z4 := norm_pow4_sub_zpow4_le y P hs_nn hy hz hP
  have h_y4z4P : ‖(y ^ 4 - z ^ 4) * P‖ ≤ 15 * s ^ 5 * s ^ 2 :=
    calc _ ≤ ‖y ^ 4 - z ^ 4‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ 15 * s ^ 5 * s ^ 2 := mul_le_mul hy4z4 hP (norm_nonneg _) (by positivity)
  have h_z4PT : ‖z ^ 4 * (P - T₂)‖ ≤ s ^ 4 * (5 * s ^ 3) :=
    calc ‖z ^ 4 * (P - T₂)‖ ≤ ‖z ^ 4‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 4 * ‖P - T₂‖ := by gcongr; exact norm_pow_le z 4
      _ ≤ s ^ 4 * (5 * s ^ 3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
          hPmT₂ (norm_nonneg _) (by positivity)
  have hy3z3 := norm_pow3_sub_zpow3_le y P hs_nn hy hz hP
  have h_y3z3Pz : ‖(y ^ 3 - z ^ 3) * P * z‖ ≤ 7 * s ^ 4 * s ^ 2 * s :=
    calc _ ≤ ‖(y ^ 3 - z ^ 3) * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 3 - z ^ 3‖ * ‖P‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (7 * s ^ 4 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy3z3 hP (norm_nonneg _) (by positivity)
  have h_z3PTz : ‖z ^ 3 * (P - T₂) * z‖ ≤ s ^ 3 * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z ^ 3 * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 3 * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 3‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 3
      _ ≤ (s ^ 3 * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3) hPmT₂
            (norm_nonneg _) (by positivity)
  have hy2z2 := norm_pow2_sub_zpow2_le y P hs_nn hy hz hP
  have h_y2z2Pz2 : ‖(y ^ 2 - z ^ 2) * P * z ^ 2‖ ≤ 3 * s ^ 3 * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(y ^ 2 - z ^ 2) * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 2 - z ^ 2‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ ((3 * s ^ 3) * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hy2z2 hP (norm_nonneg _) (by positivity)
  have h_z2PTz2 : ‖z ^ 2 * (P - T₂) * z ^ 2‖ ≤ s ^ 2 * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖z ^ 2 * (P - T₂)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 2
          · exact norm_pow_le z 2
      _ ≤ (s ^ 2 * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂
            (norm_nonneg _) (by positivity)
  have h_PPz3 : ‖P * P * z ^ 3‖ ≤ s ^ 2 * s ^ 2 * s ^ 3 :=
    calc _ ≤ ‖P * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖P‖ * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ (s ^ 2 * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hP hP (norm_nonneg _) (by positivity)
  have h_zPTz3 : ‖z * (P - T₂) * z ^ 3‖ ≤ s * (5 * s ^ 3) * s ^ 3 :=
    calc _ ≤ ‖z * (P - T₂)‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ (s * (5 * s ^ 3)) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  have h_PTz4 : ‖(P - T₂) * z ^ 4‖ ≤ (5 * s ^ 3) * s ^ 4 :=
    calc _ ≤ ‖P - T₂‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ * ‖z‖ ^ 4 := by gcongr; exact norm_pow_le z 4
      _ ≤ (5 * s ^ 3) * s ^ 4 := mul_le_mul hPmT₂
          (pow_le_pow_left₀ (norm_nonneg _) hzn 4) (by positivity) (by positivity)
  have ht1 := norm_add_le ((y ^ 4 - z ^ 4) * P + z ^ 4 * (P - T₂) +
    (y ^ 3 - z ^ 3) * P * z + z ^ 3 * (P - T₂) * z + (y ^ 2 - z ^ 2) * P * z ^ 2 +
    z ^ 2 * (P - T₂) * z ^ 2 + P * P * z ^ 3 + z * (P - T₂) * z ^ 3) ((P - T₂) * z ^ 4)
  have ht2 := norm_add_le ((y ^ 4 - z ^ 4) * P + z ^ 4 * (P - T₂) +
    (y ^ 3 - z ^ 3) * P * z + z ^ 3 * (P - T₂) * z + (y ^ 2 - z ^ 2) * P * z ^ 2 +
    z ^ 2 * (P - T₂) * z ^ 2 + P * P * z ^ 3) (z * (P - T₂) * z ^ 3)
  have ht3 := norm_add_le ((y ^ 4 - z ^ 4) * P + z ^ 4 * (P - T₂) +
    (y ^ 3 - z ^ 3) * P * z + z ^ 3 * (P - T₂) * z + (y ^ 2 - z ^ 2) * P * z ^ 2 +
    z ^ 2 * (P - T₂) * z ^ 2) (P * P * z ^ 3)
  have ht4 := norm_add_le ((y ^ 4 - z ^ 4) * P + z ^ 4 * (P - T₂) +
    (y ^ 3 - z ^ 3) * P * z + z ^ 3 * (P - T₂) * z + (y ^ 2 - z ^ 2) * P * z ^ 2)
    (z ^ 2 * (P - T₂) * z ^ 2)
  have ht5 := norm_add_le ((y ^ 4 - z ^ 4) * P + z ^ 4 * (P - T₂) +
    (y ^ 3 - z ^ 3) * P * z + z ^ 3 * (P - T₂) * z) ((y ^ 2 - z ^ 2) * P * z ^ 2)
  have ht6 := norm_add_le ((y ^ 4 - z ^ 4) * P + z ^ 4 * (P - T₂) +
    (y ^ 3 - z ^ 3) * P * z) (z ^ 3 * (P - T₂) * z)
  have ht7 := norm_add_le ((y ^ 4 - z ^ 4) * P + z ^ 4 * (P - T₂))
    ((y ^ 3 - z ^ 3) * P * z)
  have ht8 := norm_add_le ((y ^ 4 - z ^ 4) * P) (z ^ 4 * (P - T₂))
  nlinarith [pow_nonneg hs_nn 7]

/-- Algebraic decomposition of `y⁶ - z⁶ - y6_7` where `z = y - P` and
`y6_7 = z⁵T₂ + z⁴T₂z + z³T₂z² + z²T₂z³ + zT₂z⁴ + T₂z⁵` is the deg-7
contribution to `y⁶ = (z + T₂ + ...)⁶` (the (1,1,1,1,1,2) perms). Each
term is deg-8+ in the BCH context. Analog of `y5_sub_z5_sub_y5_6_decomp`
at one degree higher. -/
private theorem y6_sub_z6_sub_y6_7_decomp (y P T₂ : 𝔸) :
    y ^ 6 - (y - P) ^ 6 -
      ((y - P) ^ 5 * T₂ + (y - P) ^ 4 * T₂ * (y - P) +
        (y - P) ^ 3 * T₂ * (y - P) ^ 2 + (y - P) ^ 2 * T₂ * (y - P) ^ 3 +
        (y - P) * T₂ * (y - P) ^ 4 + T₂ * (y - P) ^ 5) =
      (y ^ 5 - (y - P) ^ 5) * P + (y - P) ^ 5 * (P - T₂) +
      (y ^ 4 - (y - P) ^ 4) * P * (y - P) + (y - P) ^ 4 * (P - T₂) * (y - P) +
      (y ^ 3 - (y - P) ^ 3) * P * (y - P) ^ 2 +
        (y - P) ^ 3 * (P - T₂) * (y - P) ^ 2 +
      (y ^ 2 - (y - P) ^ 2) * P * (y - P) ^ 3 +
        (y - P) ^ 2 * (P - T₂) * (y - P) ^ 3 +
      P * P * (y - P) ^ 4 + (y - P) * (P - T₂) * (y - P) ^ 4 +
      (P - T₂) * (y - P) ^ 5 := by
  noncomm_ring

/-- Norm bound for `y⁶ - z⁶ - y6_7`: each of the 11 terms is deg-8+;
total bound `≤ 87·s⁸`. Used in the small-s case of the octic remainder
(analog of `norm_y5_sub_z5_sub_y5_6_le` at one degree higher). -/
theorem norm_y6_sub_z6_sub_y6_7_le (y P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖y ^ 6 - (y - P) ^ 6 -
      ((y - P) ^ 5 * T₂ + (y - P) ^ 4 * T₂ * (y - P) +
        (y - P) ^ 3 * T₂ * (y - P) ^ 2 + (y - P) ^ 2 * T₂ * (y - P) ^ 3 +
        (y - P) * T₂ * (y - P) ^ 4 + T₂ * (y - P) ^ 5)‖ ≤ 87 * s ^ 8 := by
  rw [y6_sub_z6_sub_y6_7_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have hy5z5 := norm_pow5_sub_zpow5_le y P hs_nn hy hz hP
  have h_y5z5P : ‖(y ^ 5 - z ^ 5) * P‖ ≤ 31 * s ^ 6 * s ^ 2 :=
    calc _ ≤ ‖y ^ 5 - z ^ 5‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ 31 * s ^ 6 * s ^ 2 := mul_le_mul hy5z5 hP (norm_nonneg _) (by positivity)
  have h_z5PT : ‖z ^ 5 * (P - T₂)‖ ≤ s ^ 5 * (5 * s ^ 3) :=
    calc ‖z ^ 5 * (P - T₂)‖ ≤ ‖z ^ 5‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 5 * ‖P - T₂‖ := by gcongr; exact norm_pow_le z 5
      _ ≤ s ^ 5 * (5 * s ^ 3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 5)
          hPmT₂ (norm_nonneg _) (by positivity)
  have hy4z4 := norm_pow4_sub_zpow4_le y P hs_nn hy hz hP
  have h_y4z4Pz : ‖(y ^ 4 - z ^ 4) * P * z‖ ≤ 15 * s ^ 5 * s ^ 2 * s :=
    calc _ ≤ ‖(y ^ 4 - z ^ 4) * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 4 - z ^ 4‖ * ‖P‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (15 * s ^ 5 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy4z4 hP (norm_nonneg _) (by positivity)
  have h_z4PTz : ‖z ^ 4 * (P - T₂) * z‖ ≤ s ^ 4 * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z ^ 4 * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 4 * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 4‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 4
      _ ≤ (s ^ 4 * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 4) hPmT₂
            (norm_nonneg _) (by positivity)
  have hy3z3 := norm_pow3_sub_zpow3_le y P hs_nn hy hz hP
  have h_y3z3Pz2 : ‖(y ^ 3 - z ^ 3) * P * z ^ 2‖ ≤ 7 * s ^ 4 * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(y ^ 3 - z ^ 3) * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 3 - z ^ 3‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ ((7 * s ^ 4) * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hy3z3 hP (norm_nonneg _) (by positivity)
  have h_z3PTz2 : ‖z ^ 3 * (P - T₂) * z ^ 2‖ ≤ s ^ 3 * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖z ^ 3 * (P - T₂)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 3 * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖z ^ 3‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 3
          · exact norm_pow_le z 2
      _ ≤ (s ^ 3 * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3) hPmT₂
            (norm_nonneg _) (by positivity)
  have hy2z2 := norm_pow2_sub_zpow2_le y P hs_nn hy hz hP
  have h_y2z2Pz3 : ‖(y ^ 2 - z ^ 2) * P * z ^ 3‖ ≤ 3 * s ^ 3 * s ^ 2 * s ^ 3 :=
    calc _ ≤ ‖(y ^ 2 - z ^ 2) * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 2 - z ^ 2‖ * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ ((3 * s ^ 3) * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hy2z2 hP (norm_nonneg _) (by positivity)
  have h_z2PTz3 : ‖z ^ 2 * (P - T₂) * z ^ 3‖ ≤ s ^ 2 * (5 * s ^ 3) * s ^ 3 :=
    calc _ ≤ ‖z ^ 2 * (P - T₂)‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂‖) * ‖z‖ ^ 3 := by
          gcongr
          · calc _ ≤ ‖z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 2
          · exact norm_pow_le z 3
      _ ≤ (s ^ 2 * (5 * s ^ 3)) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂
            (norm_nonneg _) (by positivity)
  have h_PPz4 : ‖P * P * z ^ 4‖ ≤ s ^ 2 * s ^ 2 * s ^ 4 :=
    calc _ ≤ ‖P * P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖P‖ * ‖P‖) * ‖z‖ ^ 4 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 4
      _ ≤ (s ^ 2 * s ^ 2) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul hP hP (norm_nonneg _) (by positivity)
  have h_zPTz4 : ‖z * (P - T₂) * z ^ 4‖ ≤ s * (5 * s ^ 3) * s ^ 4 :=
    calc _ ≤ ‖z * (P - T₂)‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂‖) * ‖z‖ ^ 4 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 4
      _ ≤ (s * (5 * s ^ 3)) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  have h_PTz5 : ‖(P - T₂) * z ^ 5‖ ≤ (5 * s ^ 3) * s ^ 5 :=
    calc _ ≤ ‖P - T₂‖ * ‖z ^ 5‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ * ‖z‖ ^ 5 := by gcongr; exact norm_pow_le z 5
      _ ≤ (5 * s ^ 3) * s ^ 5 := mul_le_mul hPmT₂
          (pow_le_pow_left₀ (norm_nonneg _) hzn 5) (by positivity) (by positivity)
  have ht1 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z + z ^ 4 * (P - T₂) * z +
    (y ^ 3 - z ^ 3) * P * z ^ 2 + z ^ 3 * (P - T₂) * z ^ 2 +
    (y ^ 2 - z ^ 2) * P * z ^ 3 + z ^ 2 * (P - T₂) * z ^ 3 +
    P * P * z ^ 4 + z * (P - T₂) * z ^ 4) ((P - T₂) * z ^ 5)
  have ht2 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z + z ^ 4 * (P - T₂) * z +
    (y ^ 3 - z ^ 3) * P * z ^ 2 + z ^ 3 * (P - T₂) * z ^ 2 +
    (y ^ 2 - z ^ 2) * P * z ^ 3 + z ^ 2 * (P - T₂) * z ^ 3 +
    P * P * z ^ 4) (z * (P - T₂) * z ^ 4)
  have ht3 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z + z ^ 4 * (P - T₂) * z +
    (y ^ 3 - z ^ 3) * P * z ^ 2 + z ^ 3 * (P - T₂) * z ^ 2 +
    (y ^ 2 - z ^ 2) * P * z ^ 3 + z ^ 2 * (P - T₂) * z ^ 3) (P * P * z ^ 4)
  have ht4 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z + z ^ 4 * (P - T₂) * z +
    (y ^ 3 - z ^ 3) * P * z ^ 2 + z ^ 3 * (P - T₂) * z ^ 2 +
    (y ^ 2 - z ^ 2) * P * z ^ 3) (z ^ 2 * (P - T₂) * z ^ 3)
  have ht5 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z + z ^ 4 * (P - T₂) * z +
    (y ^ 3 - z ^ 3) * P * z ^ 2 + z ^ 3 * (P - T₂) * z ^ 2)
    ((y ^ 2 - z ^ 2) * P * z ^ 3)
  have ht6 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z + z ^ 4 * (P - T₂) * z +
    (y ^ 3 - z ^ 3) * P * z ^ 2) (z ^ 3 * (P - T₂) * z ^ 2)
  have ht7 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z + z ^ 4 * (P - T₂) * z)
    ((y ^ 3 - z ^ 3) * P * z ^ 2)
  have ht8 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂) +
    (y ^ 4 - z ^ 4) * P * z) (z ^ 4 * (P - T₂) * z)
  have ht9 := norm_add_le ((y ^ 5 - z ^ 5) * P + z ^ 5 * (P - T₂))
    ((y ^ 4 - z ^ 4) * P * z)
  have ht10 := norm_add_le ((y ^ 5 - z ^ 5) * P) (z ^ 5 * (P - T₂))
  nlinarith [pow_nonneg hs_nn 8]

set_option maxHeartbeats 4000000 in
/-- Algebraic decomposition of `y⁷ - z⁷ - y7_8` where `z = y - P` and
`y7_8 = z⁶T₂ + z⁵T₂z + z⁴T₂z² + z³T₂z³ + z²T₂z⁴ + zT₂z⁵ + T₂z⁶` is the
deg-8 contribution to `y⁷ = (z + T₂ + ...)⁷` (the (1,1,1,1,1,1,2) perms,
i.e., one T₂ in seven positions among 6 z's). Each term on the RHS is
deg-9+ in the BCH context. Analog of `y6_sub_z6_sub_y6_7_decomp` at one
degree higher (13 terms instead of 11). -/
private theorem y7_sub_z7_sub_y7_8_decomp (y P T₂ : 𝔸) :
    y ^ 7 - (y - P) ^ 7 -
      ((y - P) ^ 6 * T₂ + (y - P) ^ 5 * T₂ * (y - P) +
        (y - P) ^ 4 * T₂ * (y - P) ^ 2 + (y - P) ^ 3 * T₂ * (y - P) ^ 3 +
        (y - P) ^ 2 * T₂ * (y - P) ^ 4 + (y - P) * T₂ * (y - P) ^ 5 +
        T₂ * (y - P) ^ 6) =
      (y ^ 6 - (y - P) ^ 6) * P + (y - P) ^ 6 * (P - T₂) +
      (y ^ 5 - (y - P) ^ 5) * P * (y - P) +
        (y - P) ^ 5 * (P - T₂) * (y - P) +
      (y ^ 4 - (y - P) ^ 4) * P * (y - P) ^ 2 +
        (y - P) ^ 4 * (P - T₂) * (y - P) ^ 2 +
      (y ^ 3 - (y - P) ^ 3) * P * (y - P) ^ 3 +
        (y - P) ^ 3 * (P - T₂) * (y - P) ^ 3 +
      (y ^ 2 - (y - P) ^ 2) * P * (y - P) ^ 4 +
        (y - P) ^ 2 * (P - T₂) * (y - P) ^ 4 +
      P * P * (y - P) ^ 5 + (y - P) * (P - T₂) * (y - P) ^ 5 +
      (P - T₂) * (y - P) ^ 6 := by
  noncomm_ring

set_option maxHeartbeats 4000000 in
/-- Norm bound for `y⁷ - z⁷ - y7_8`: each of the 13 terms is deg-9+;
total bound `≤ 155·s⁹`. Used for the future S₆-nonic piece in the
deg-9-parent T2-F7e-octic discharge (analog of `norm_y6_sub_z6_sub_y6_7_le`
at one degree higher).

Per-term bounds: 63·s⁹ + 5·s⁹ + 31·s⁹ + 5·s⁹ + 15·s⁹ + 5·s⁹ + 7·s⁹ + 5·s⁹ +
                 3·s⁹ + 5·s⁹ + 1·s⁹ + 5·s⁹ + 5·s⁹ = 155·s⁹. -/
private theorem norm_y7_sub_z7_sub_y7_8_le (y P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖y ^ 7 - (y - P) ^ 7 -
      ((y - P) ^ 6 * T₂ + (y - P) ^ 5 * T₂ * (y - P) +
        (y - P) ^ 4 * T₂ * (y - P) ^ 2 + (y - P) ^ 3 * T₂ * (y - P) ^ 3 +
        (y - P) ^ 2 * T₂ * (y - P) ^ 4 + (y - P) * T₂ * (y - P) ^ 5 +
        T₂ * (y - P) ^ 6)‖ ≤ 155 * s ^ 9 := by
  rw [y7_sub_z7_sub_y7_8_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- (y^k - z^k)·P·z^(6-k) bounds via existing pow_k - z_k lemmas.
  have hy6z6 := norm_pow6_sub_zpow6_le y P hs_nn hy hz hP
  have h_y6z6P : ‖(y ^ 6 - z ^ 6) * P‖ ≤ 63 * s ^ 7 * s ^ 2 :=
    calc _ ≤ ‖y ^ 6 - z ^ 6‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ 63 * s ^ 7 * s ^ 2 := mul_le_mul hy6z6 hP (norm_nonneg _) (by positivity)
  have h_z6PT : ‖z ^ 6 * (P - T₂)‖ ≤ s ^ 6 * (5 * s ^ 3) :=
    calc ‖z ^ 6 * (P - T₂)‖ ≤ ‖z ^ 6‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 6 * ‖P - T₂‖ := by gcongr; exact norm_pow_le z 6
      _ ≤ s ^ 6 * (5 * s ^ 3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 6)
          hPmT₂ (norm_nonneg _) (by positivity)
  have hy5z5 := norm_pow5_sub_zpow5_le y P hs_nn hy hz hP
  have h_y5z5Pz : ‖(y ^ 5 - z ^ 5) * P * z‖ ≤ 31 * s ^ 6 * s ^ 2 * s :=
    calc _ ≤ ‖(y ^ 5 - z ^ 5) * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 5 - z ^ 5‖ * ‖P‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (31 * s ^ 6 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy5z5 hP (norm_nonneg _) (by positivity)
  have h_z5PTz : ‖z ^ 5 * (P - T₂) * z‖ ≤ s ^ 5 * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z ^ 5 * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 5 * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 5‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 5
      _ ≤ (s ^ 5 * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 5) hPmT₂
            (norm_nonneg _) (by positivity)
  have hy4z4 := norm_pow4_sub_zpow4_le y P hs_nn hy hz hP
  have h_y4z4Pz2 : ‖(y ^ 4 - z ^ 4) * P * z ^ 2‖ ≤ 15 * s ^ 5 * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(y ^ 4 - z ^ 4) * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 4 - z ^ 4‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ ((15 * s ^ 5) * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hy4z4 hP (norm_nonneg _) (by positivity)
  have h_z4PTz2 : ‖z ^ 4 * (P - T₂) * z ^ 2‖ ≤ s ^ 4 * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖z ^ 4 * (P - T₂)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 4 * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖z ^ 4‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 4
          · exact norm_pow_le z 2
      _ ≤ (s ^ 4 * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 4) hPmT₂
            (norm_nonneg _) (by positivity)
  have hy3z3 := norm_pow3_sub_zpow3_le y P hs_nn hy hz hP
  have h_y3z3Pz3 : ‖(y ^ 3 - z ^ 3) * P * z ^ 3‖ ≤ 7 * s ^ 4 * s ^ 2 * s ^ 3 :=
    calc _ ≤ ‖(y ^ 3 - z ^ 3) * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 3 - z ^ 3‖ * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ ((7 * s ^ 4) * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hy3z3 hP (norm_nonneg _) (by positivity)
  have h_z3PTz3 : ‖z ^ 3 * (P - T₂) * z ^ 3‖ ≤ s ^ 3 * (5 * s ^ 3) * s ^ 3 :=
    calc _ ≤ ‖z ^ 3 * (P - T₂)‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 3 * ‖P - T₂‖) * ‖z‖ ^ 3 := by
          gcongr
          · calc _ ≤ ‖z ^ 3‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 3
          · exact norm_pow_le z 3
      _ ≤ (s ^ 3 * (5 * s ^ 3)) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3) hPmT₂
            (norm_nonneg _) (by positivity)
  have hy2z2 := norm_pow2_sub_zpow2_le y P hs_nn hy hz hP
  have h_y2z2Pz4 : ‖(y ^ 2 - z ^ 2) * P * z ^ 4‖ ≤ 3 * s ^ 3 * s ^ 2 * s ^ 4 :=
    calc _ ≤ ‖(y ^ 2 - z ^ 2) * P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 2 - z ^ 2‖ * ‖P‖) * ‖z‖ ^ 4 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 4
      _ ≤ ((3 * s ^ 3) * s ^ 2) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul hy2z2 hP (norm_nonneg _) (by positivity)
  have h_z2PTz4 : ‖z ^ 2 * (P - T₂) * z ^ 4‖ ≤ s ^ 2 * (5 * s ^ 3) * s ^ 4 :=
    calc _ ≤ ‖z ^ 2 * (P - T₂)‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂‖) * ‖z‖ ^ 4 := by
          gcongr
          · calc _ ≤ ‖z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 2
          · exact norm_pow_le z 4
      _ ≤ (s ^ 2 * (5 * s ^ 3)) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂
            (norm_nonneg _) (by positivity)
  have h_PPz5 : ‖P * P * z ^ 5‖ ≤ s ^ 2 * s ^ 2 * s ^ 5 :=
    calc _ ≤ ‖P * P‖ * ‖z ^ 5‖ := norm_mul_le _ _
      _ ≤ (‖P‖ * ‖P‖) * ‖z‖ ^ 5 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 5
      _ ≤ (s ^ 2 * s ^ 2) * s ^ 5 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 5)
            (by positivity) (by positivity)
          exact mul_le_mul hP hP (norm_nonneg _) (by positivity)
  have h_zPTz5 : ‖z * (P - T₂) * z ^ 5‖ ≤ s * (5 * s ^ 3) * s ^ 5 :=
    calc _ ≤ ‖z * (P - T₂)‖ * ‖z ^ 5‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂‖) * ‖z‖ ^ 5 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 5
      _ ≤ (s * (5 * s ^ 3)) * s ^ 5 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 5)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  have h_PTz6 : ‖(P - T₂) * z ^ 6‖ ≤ (5 * s ^ 3) * s ^ 6 :=
    calc _ ≤ ‖P - T₂‖ * ‖z ^ 6‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ * ‖z‖ ^ 6 := by gcongr; exact norm_pow_le z 6
      _ ≤ (5 * s ^ 3) * s ^ 6 := mul_le_mul hPmT₂
          (pow_le_pow_left₀ (norm_nonneg _) hzn 6) (by positivity) (by positivity)
  -- Triangle inequality on the 13-term sum (12 norm_add_le applications).
  have ht1 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2 + z ^ 4 * (P - T₂) * z ^ 2 +
    (y ^ 3 - z ^ 3) * P * z ^ 3 + z ^ 3 * (P - T₂) * z ^ 3 +
    (y ^ 2 - z ^ 2) * P * z ^ 4 + z ^ 2 * (P - T₂) * z ^ 4 +
    P * P * z ^ 5 + z * (P - T₂) * z ^ 5) ((P - T₂) * z ^ 6)
  have ht2 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2 + z ^ 4 * (P - T₂) * z ^ 2 +
    (y ^ 3 - z ^ 3) * P * z ^ 3 + z ^ 3 * (P - T₂) * z ^ 3 +
    (y ^ 2 - z ^ 2) * P * z ^ 4 + z ^ 2 * (P - T₂) * z ^ 4 +
    P * P * z ^ 5) (z * (P - T₂) * z ^ 5)
  have ht3 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2 + z ^ 4 * (P - T₂) * z ^ 2 +
    (y ^ 3 - z ^ 3) * P * z ^ 3 + z ^ 3 * (P - T₂) * z ^ 3 +
    (y ^ 2 - z ^ 2) * P * z ^ 4 + z ^ 2 * (P - T₂) * z ^ 4) (P * P * z ^ 5)
  have ht4 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2 + z ^ 4 * (P - T₂) * z ^ 2 +
    (y ^ 3 - z ^ 3) * P * z ^ 3 + z ^ 3 * (P - T₂) * z ^ 3 +
    (y ^ 2 - z ^ 2) * P * z ^ 4) (z ^ 2 * (P - T₂) * z ^ 4)
  have ht5 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2 + z ^ 4 * (P - T₂) * z ^ 2 +
    (y ^ 3 - z ^ 3) * P * z ^ 3 + z ^ 3 * (P - T₂) * z ^ 3)
    ((y ^ 2 - z ^ 2) * P * z ^ 4)
  have ht6 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2 + z ^ 4 * (P - T₂) * z ^ 2 +
    (y ^ 3 - z ^ 3) * P * z ^ 3) (z ^ 3 * (P - T₂) * z ^ 3)
  have ht7 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2 + z ^ 4 * (P - T₂) * z ^ 2)
    ((y ^ 3 - z ^ 3) * P * z ^ 3)
  have ht8 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z +
    (y ^ 4 - z ^ 4) * P * z ^ 2) (z ^ 4 * (P - T₂) * z ^ 2)
  have ht9 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z + z ^ 5 * (P - T₂) * z)
    ((y ^ 4 - z ^ 4) * P * z ^ 2)
  have ht10 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂) +
    (y ^ 5 - z ^ 5) * P * z) (z ^ 5 * (P - T₂) * z)
  have ht11 := norm_add_le ((y ^ 6 - z ^ 6) * P + z ^ 6 * (P - T₂))
    ((y ^ 5 - z ^ 5) * P * z)
  have ht12 := norm_add_le ((y ^ 6 - z ^ 6) * P) (z ^ 6 * (P - T₂))
  -- Sum: 63 + 5 + 31 + 5 + 15 + 5 + 7 + 5 + 3 + 5 + 1 + 5 + 5 = 155 (in units of s⁹).
  nlinarith [pow_nonneg hs_nn 9]

/-- **I₂ residual decomposition**: pure ring identity in `(z, P, T₂, T₃)` for
`(z+P)³ - z³ - (z²T₂+zT₂z+T₂z²) - (z²T₃+zT₃z+T₃z²+zT₂²+T₂zT₂+T₂²z)`,
which when multiplied by `(3:𝕂)⁻¹` becomes `I₂ - corr₂ - corr₂_5`.

Each summand on the RHS has deg-6+ structure (since `P-T₂-T₃` has deg-4+,
`P²-T₂²` has deg-5+, `PzP-T₂zT₂` has deg-6+, `P³` has deg-6). -/
theorem I2_residual_decomp_eq (z P T₂ T₃ : 𝔸) :
    (z + P) ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
      (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) =
    z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z + (P - T₂ - T₃) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) +
    (P ^ 2 - T₂ ^ 2) * z + P ^ 3 := by
  noncomm_ring

/-- **I₂ septic residual decomposition**: extends `I2_residual_decomp_eq`
by subtracting the deg-6 leading part `y3_6 = (3 T₄ terms) + (6 T₂·T₃
permutations) + T₂³` to give a pure ring identity in `(z, P, T₂, T₃, T₄)`
where each RHS term is deg-7+.

Pairings:
- `(3 T₄ terms)` extend the 3 weight-1 (P-T₂-T₃) terms into (P-T₂-T₃-T₄).
- `(6 T₂·T₃ perms)` are absorbed into the 3 weight-2 (P²-T₂²) compound
  forms, giving `z(P²-T₂²-T₂T₃-T₃T₂)`, `(PzP-T₂zT₂-T₂zT₃-T₃zT₂)`,
  `(P²-T₂²-T₂T₃-T₃T₂)z`.
- `T₂³` is absorbed into `P³`, giving `P³ - T₂³` (deg-7+ via telescoping).

Each summand on the RHS is deg-7+ in the BCH context.
Proof: `noncomm_ring` (pure ring identity, no scalar coefficients). -/
private theorem I2_septic_residual_decomp_eq (z P T₂ T₃ T₄ : 𝔸) :
    (z + P) ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
      (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
      (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
        z * T₂ * T₃ + z * T₃ * T₂ +
        T₂ * z * T₃ + T₃ * z * T₂ +
        T₂ * T₃ * z + T₃ * T₂ * z +
        T₂ ^ 3) =
    z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
      (P - T₂ - T₃ - T₄) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) +
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂) +
    (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z +
    (P ^ 3 - T₂ ^ 3) := by
  noncomm_ring

/-- **I₂ octic residual decomposition**: extends `I2_septic_residual_decomp_eq`
by subtracting the deg-7 leading part `y3_7` (15 terms: 3 with T₅, 6 with
T₂·T₄ + T₄·T₂ perms, 3 with T₃² perms, 3 with T₂²·T₃ perms) to give a pure
ring identity in `(z, P, T₂, T₃, T₄, T₅)` where each RHS term is deg-8+.

Pairings (additions on top of septic):
- 3 weight-1 terms `z^i·(P-T₂-T₃-T₄)·z^j` extend to `z^i·(P-T₂-T₃-T₄-T₅)·z^j`.
- `z·T₂·T₄` and `z·T₄·T₂` + `z·T₃²` get absorbed into
  `z·(P² - T₂² - T₂T₃ - T₃T₂)` → `z·(P² - T₂² - T₂T₃ - T₃T₂ - T₂T₄ - T₃² - T₄T₂)`.
- Conjugates `(...)·z` and `T_aux·z·T_aux` get the analogous extensions.
- `T₂²·T₃`, `T₂·T₃·T₂`, `T₃·T₂²` get absorbed into `P³`:
  `(P³ - T₂³)` → `(P³ - T₂³ - T₂²·T₃ - T₂·T₃·T₂ - T₃·T₂²)`.

Each RHS summand is deg-8+ in the BCH context.
Proof: `noncomm_ring` (pure ring identity, no scalar coefficients). -/
theorem I2_octic_residual_decomp_eq (z P T₂ T₃ T₄ T₅ : 𝔸) :
    (z + P) ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
      (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
      (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
        z * T₂ * T₃ + z * T₃ * T₂ +
        T₂ * z * T₃ + T₃ * z * T₂ +
        T₂ * T₃ * z + T₃ * T₂ * z +
        T₂ ^ 3) -
      (z ^ 2 * T₅ + z * T₅ * z + T₅ * z ^ 2 +
        z * T₂ * T₄ + z * T₃ * T₃ + z * T₄ * T₂ +
        T₂ * z * T₄ + T₃ * z * T₃ + T₄ * z * T₂ +
        T₂ * T₄ * z + T₃ * T₃ * z + T₄ * T₂ * z +
        T₂ * T₂ * T₃ + T₂ * T₃ * T₂ + T₃ * T₂ * T₂) =
    z ^ 2 * (P - T₂ - T₃ - T₄ - T₅) + z * (P - T₂ - T₃ - T₄ - T₅) * z +
      (P - T₂ - T₃ - T₄ - T₅) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂) +
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
         T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂) +
    (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂) * z +
    (P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2) := by
  noncomm_ring

/-- **I₂ nonic residual decomposition**: extends `I2_octic_residual_decomp_eq`
by subtracting the deg-8 leading part (21 new terms) to give a pure ring
identity in `(z, P, T₂, T₃, T₄, T₅, T₆)` where each RHS term is deg-9+.

Pairings (additions on top of octic):
- 3 weight-1 middle terms `z^i·(P-T₂-T₃-T₄-T₅)·z^j` extend to
  `z^i·(P-T₂-T₃-T₄-T₅-T₆)·z^j`.
- `z·T₂·T₅`, `z·T₃·T₄`, `z·T₄·T₃`, `z·T₅·T₂` get absorbed into
  `z·(P² - T₂² - T₂T₃ - T₃T₂ - T₂T₄ - T₃² - T₄T₂)` →
  `z·(P² - T₂² - T₂T₃ - T₃T₂ - T₂T₄ - T₃² - T₄T₂ - T₂T₅ - T₃T₄ - T₄T₃ - T₅T₂)`.
- Sandwich `T₂zT₅`, `T₃zT₄`, `T₄zT₃`, `T₅zT₂` absorbed into the PzP residual.
- Conjugates `(...)·z` get the analogous extension.
- `T₂²T₄`, `T₂T₄T₂`, `T₄T₂²`, `T₂T₃²`, `T₃T₂T₃`, `T₃²T₂` (6 deg-8 P³ perms)
  absorbed into `(P³ - T₂³ - T₂²T₃ - T₂T₃T₂ - T₃T₂²)` →
  `(P³ - T₂³ - T₂²T₃ - T₂T₃T₂ - T₃T₂² - T₂²T₄ - T₂T₄T₂ - T₄T₂² -
        T₂T₃² - T₃T₂T₃ - T₃²T₂)`.

Each RHS summand is deg-9+ in the BCH context.
Proof: `noncomm_ring` (pure ring identity, no scalar coefficients). -/
theorem I2_nonic_residual_decomp_eq (z P T₂ T₃ T₄ T₅ T₆ : 𝔸) :
    (z + P) ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) -
      (z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z) -
      (z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
        z * T₂ * T₃ + z * T₃ * T₂ +
        T₂ * z * T₃ + T₃ * z * T₂ +
        T₂ * T₃ * z + T₃ * T₂ * z +
        T₂ ^ 3) -
      (z ^ 2 * T₅ + z * T₅ * z + T₅ * z ^ 2 +
        z * T₂ * T₄ + z * T₃ * T₃ + z * T₄ * T₂ +
        T₂ * z * T₄ + T₃ * z * T₃ + T₄ * z * T₂ +
        T₂ * T₄ * z + T₃ * T₃ * z + T₄ * T₂ * z +
        T₂ * T₂ * T₃ + T₂ * T₃ * T₂ + T₃ * T₂ * T₂) -
      (z ^ 2 * T₆ + z * T₆ * z + T₆ * z ^ 2 +
        z * T₂ * T₅ + z * T₃ * T₄ + z * T₄ * T₃ + z * T₅ * T₂ +
        T₂ * z * T₅ + T₃ * z * T₄ + T₄ * z * T₃ + T₅ * z * T₂ +
        T₂ * T₅ * z + T₃ * T₄ * z + T₄ * T₃ * z + T₅ * T₂ * z +
        T₂ * T₂ * T₄ + T₂ * T₄ * T₂ + T₄ * T₂ * T₂ +
        T₂ * T₃ * T₃ + T₃ * T₂ * T₃ + T₃ * T₃ * T₂) =
    z ^ 2 * (P - T₂ - T₃ - T₄ - T₅ - T₆) +
      z * (P - T₂ - T₃ - T₄ - T₅ - T₆) * z +
      (P - T₂ - T₃ - T₄ - T₅ - T₆) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂ -
         T₂ * T₅ - T₃ * T₄ - T₄ * T₃ - T₅ * T₂) +
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ -
         T₂ * z * T₄ - T₃ * z * T₃ - T₄ * z * T₂ -
         T₂ * z * T₅ - T₃ * z * T₄ - T₄ * z * T₃ - T₅ * z * T₂) +
    (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂ -
         T₂ * T₄ - T₃ * T₃ - T₄ * T₂ -
         T₂ * T₅ - T₃ * T₄ - T₄ * T₃ - T₅ * T₂) * z +
    (P ^ 3 - T₂ ^ 3 - T₂ ^ 2 * T₃ - T₂ * T₃ * T₂ - T₃ * T₂ ^ 2 -
         T₂ ^ 2 * T₄ - T₂ * T₄ * T₂ - T₄ * T₂ ^ 2 -
         T₂ * T₃ ^ 2 - T₃ * T₂ * T₃ - T₃ ^ 2 * T₂) := by
  noncomm_ring

set_option maxHeartbeats 4000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **I₁ residual decomposition** (pure algebraic identity in (ea, eb, a, b)):
expresses `(I₁ in quartic_id form) - corr₁ - corr₁_5` as a sum of 7 deg-6+ terms.

Proof: ×720 scalar clearing + dsimp (unfold let-bindings) + simp distribution
+ noncomm_ring. Mirrors the pattern of `quartic_identity` and
`sextic_pure_identity`. -/
theorem I1_residual_decomp_eq (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let P : 𝔸 := ea * eb - 1 - (a + b)
    let z : 𝔸 := a + b
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
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
    let R : 𝔸 := T₃ - E₁ - E₂ - Q + T₄
    -- LHS: I₁ (quartic_identity form) - corr₁ - corr₁_5
    (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
        (2 : 𝕂)⁻¹ • P ^ 2) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
      (2 : 𝕂)⁻¹ • W5 =
    -- RHS: 7 deg-6+ terms
    H₁ + H₂ + a * G₂ + G₁ * b +
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
    (2 : 𝕂)⁻¹ • (z * R + R * z) +
    (2 : 𝕂)⁻¹ • (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) := by
  -- KEY: dsimp only unfolds the let-bindings (transparent reduction)
  dsimp only
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **R algebraic identity** for the I₁ residual bound.
Expresses `R = T₃ - E₁ - E₂ - Q + T₄` (the deg-5+ part of `-(E_i+Q) + T₃ + T₄`)
as `R = -(G₁ + G₂ + a·F₂ + F₁·b + E₁·E₂ + ½·E₁·b² + ½·a²·E₂)`. -/
theorem R_eq_neg_deg5_residual (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    T₃ - E₁ - E₂ - Q + T₄ =
    -(G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂)) := by
  dsimp only
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **R + T₅ algebraic decomposition**: extends `R_eq_neg_deg5_residual` by
canceling the deg-5 leading R₅ = -T₅. Each RHS piece is deg-6+ in s.
Foundation for the combined `(z·R+R·z) + T22 + T_extra` bound at deg-7+. -/
theorem R_plus_T5_eq_neg_deg6_residual (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    T₃ - E₁ - E₂ - Q + T₄ + T₅ =
    -(H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (F₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂)) := by
  have hR := R_eq_neg_deg5_residual 𝕂 ea eb a b
  dsimp only at hR ⊢
  -- linear_combination leaves a residual where 12⁻¹ and 2⁻¹·6⁻¹ appear as
  -- different scalar expressions; match_scalars + ring normalizes them.
  linear_combination (norm := (simp only [pow_succ, pow_zero, one_mul,
    smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]; match_scalars <;> ring)) hR

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **R + T₅ + T₆ algebraic decomposition**: extends `R_plus_T5_eq_neg_deg6_residual`
by canceling the deg-6 leading R₆ = -T₆. Each RHS piece is deg-7+ in s.

The deg-7 cancellation arises from:
- `H₁_d6 + H₂_d6 = a⁶/720 + b⁶/720`
- `aG₂_d6 + G₁b_d6 = ab⁵/120 + a⁵b/120`
- `E₁E₂_d6 = a³b³/36`
- `½F₁b²_d6 + ½a²F₂_d6 = a⁴b²/48 + a²b⁴/48`
- Sum = T₆ ✓

Decomposition uses `E₁ = F₁ + a³/6, E₂ = F₂ + b³/6, H_i = I_i + i⁶/720` etc.
to absorb deg-6 contributions, leaving 9 deg-7+ residuals:
- `I_a + I_b`: top exp-tail
- `a*H₂ + H₁*b`: 1-monomial × deg-6 tail
- `F₁·F₂ + ⅙·F₁·b³ + ⅙·a³·F₂`: the deg-7 expansion of E₁E₂_d≥7
- `½·G₁·b² + ½·a²·G₂`: deg-7 mid-degree

Foundation for the future I1 octic chain. -/
theorem R_plus_T5_plus_T6_eq_neg_deg7_residual (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let I_a : 𝔸 := H₁ - (720 : 𝕂)⁻¹ • a ^ 6
    let I_b : 𝔸 := H₂ - (720 : 𝕂)⁻¹ • b ^ 6
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let T₆ : 𝔸 := (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6
    T₃ - E₁ - E₂ - Q + T₄ + T₅ + T₆ =
    -(I_a + I_b + a * H₂ + H₁ * b +
      F₁ * F₂ + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * F₂) +
      (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * G₂)) := by
  have hR := R_plus_T5_eq_neg_deg6_residual 𝕂 ea eb a b
  dsimp only at hR ⊢
  linear_combination (norm := (simp only [pow_succ, pow_zero, one_mul,
    smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]; match_scalars <;> ring)) hR

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **R + T₅ + T₆ + T₇ algebraic decomposition**: extends
`R_plus_T5_plus_T6_eq_neg_deg7_residual` by canceling the deg-7 leading R₇ = -T₇.
Each RHS piece is deg-8+ in s.

The deg-7 cancellation arises from promoting each term in the deg-7 residual by
one tail level (F→G, G→H, H→I, I→J), with the subtracted monomials summing to
exactly T₇:
- `I_a → J_a`: subtract a⁷/5040
- `I_b → J_b`: subtract b⁷/5040
- `a·H₂ → a·I_b`: subtract a·b⁶/720
- `H₁·b → I_a·b`: subtract a⁶·b/720
- `F₁·F₂` stays (already deg-8+)
- `⅙·F₁·b³ → ⅙·G₁·b³`: subtract a⁴b³/144
- `⅙·a³·F₂ → ⅙·a³·G₂`: subtract a³b⁴/144
- `½·G₁·b² → ½·H₁·b²`: subtract a⁵b²/240
- `½·a²·G₂ → ½·a²·H₂`: subtract a²b⁵/240
- Sum of subtractions = T₇ ✓

Foundation for the future deg-9-parent T2-F7e-octic discharge (deg-8 analog of
the session 24 R₅, session 29 R₆ cancellations at one degree higher). -/
theorem R_plus_T5_plus_T6_plus_T7_eq_neg_deg8_residual (𝕂 : Type*) [RCLike 𝕂]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let I_a : 𝔸 := H₁ - (720 : 𝕂)⁻¹ • a ^ 6
    let I_b : 𝔸 := H₂ - (720 : 𝕂)⁻¹ • b ^ 6
    let J_a : 𝔸 := I_a - (5040 : 𝕂)⁻¹ • a ^ 7
    let J_b : 𝔸 := I_b - (5040 : 𝕂)⁻¹ • b ^ 7
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let T₆ : 𝔸 := (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6
    let T₇ : 𝔸 := (5040 : 𝕂)⁻¹ • a ^ 7 + (720 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (240 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (144 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (144 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (240 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (720 : 𝕂)⁻¹ • (a * b ^ 6) + (5040 : 𝕂)⁻¹ • b ^ 7
    T₃ - E₁ - E₂ - Q + T₄ + T₅ + T₆ + T₇ =
    -(J_a + J_b + a * I_b + I_a * b +
      F₁ * F₂ + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * G₂) +
      (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * H₂)) := by
  have hR := R_plus_T5_plus_T6_eq_neg_deg7_residual 𝕂 ea eb a b
  dsimp only at hR ⊢
  linear_combination (norm := (simp only [pow_succ, pow_zero, one_mul,
    smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]; match_scalars <;> ring)) hR

set_option maxHeartbeats 8000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **I₁ septic residual decomposition** (pure algebraic identity in (ea, eb, a, b)):
extends `I1_residual_decomp_eq` by subtracting `corr₁_6 = ½·W6`, expressing
`(I₁ in quartic_id form) - corr₁ - corr₁_5 - corr₁_6` as 12 deg-7+ terms.

The 7 monomial parts of `½·W6` pair with the deg-6 leading parts of the
existing I1_residual_decomp_eq's RHS:
- `(720)⁻¹·a⁶` from `½·W6` cancels `(720)⁻¹·a⁶` in `H₁`, leaving
  `I_a := H₁ - (720)⁻¹·a⁶` (deg-7+, bounded by `α⁷` via level-7 exp tail).
- `(120)⁻¹·a⁵·b ← G₁·b → H₁·b` (deg-7).
- `(48)⁻¹·a⁴·b² ← ½·F₁·b² → ½·G₁·b²` (deg-7).
- `(36)⁻¹·a³·b³ ← E₁·E₂ → (1/6)·a³·F₂ + (1/6)·F₁·b³ + F₁·F₂` (deg-7+).
- `(48)⁻¹·a²·b⁴ ← ½·a²·F₂ → ½·a²·G₂` (deg-7).
- `(120)⁻¹·a·b⁵ ← a·G₂ → a·H₂` (deg-7).
- `(720)⁻¹·b⁶ ← H₂ → I_b := H₂ - (720)⁻¹·b⁶` (deg-7+).

Plus: the non-monomial part of W6 (= `z·T₅ + T₂·T₄ + T₃² + T₄·T₂ + T₅·z`)
gets added back as an extra cluster `(2)⁻¹·(z·T₅ + T₂·T₄ + T₃² + T₄·T₂ + T₅·z)`.

Proof: `match_scalars <;> ring` (mirrors I1_residual_decomp_eq's pattern). -/
theorem I1_septic_residual_decomp_eq (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let I_a : 𝔸 := H₁ - (720 : 𝕂)⁻¹ • a ^ 6
    let I_b : 𝔸 := H₂ - (720 : 𝕂)⁻¹ • b ^ 6
    let P : 𝔸 := ea * eb - 1 - (a + b)
    let z : 𝔸 := a + b
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂)
    let W6 : 𝔸 := (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
        (360 : 𝕂)⁻¹ • b ^ 6 -
        (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z)
    let R : 𝔸 := T₃ - E₁ - E₂ - Q + T₄
    -- LHS: I₁ (quartic_identity form) - corr₁ - corr₁_5 - corr₁_6
    (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
        (2 : 𝕂)⁻¹ • P ^ 2) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
      (2 : 𝕂)⁻¹ • W5 -
      (2 : 𝕂)⁻¹ • W6 =
    -- RHS: 12 deg-7+ terms (combined into 9 cluster expressions)
    I_a + I_b + a * H₂ + H₁ * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
    (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) + (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) +
    (2 : 𝕂)⁻¹ • (z * R + R * z) +
    (2 : 𝕂)⁻¹ • (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
    (2 : 𝕂)⁻¹ • (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) := by
  dsimp only
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

set_option maxHeartbeats 16000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **I₁ octic residual decomposition** (pure algebraic identity in (ea, eb, a, b)):
extends `I1_septic_residual_decomp_eq` by additionally subtracting
`corr₁_7 = ½·W7`, expressing
`(I₁ in quartic_id form) - corr₁ - corr₁_5 - corr₁_6 - corr₁_7`
as 13 deg-8+ terms (a one-degree-higher promotion of the septic RHS).

Promotions of the 9 "easy" septic RHS terms (each gains one exp-tail level):
- `I_a → J_a := I_a − a⁷/5040` (the deg-7 monomial `a⁷/5040` paired with
  `½·(2520)⁻¹·a⁷` part of `½·W7`).
- `I_b → J_b := I_b − b⁷/5040` (similarly).
- `a·H₂ → a·I_b` (cancels `a·b⁶/720`).
- `H₁·b → I_a·b` (cancels `a⁶·b/720`).
- `½·a²·G₂ → ½·a²·H₂` (cancels `a²·b⁵/240`).
- `½·G₁·b² → ½·H₁·b²` (cancels `a⁵·b²/240`).
- `⅙·a³·F₂ → ⅙·a³·G₂` (cancels `a³·b⁴/144`).
- `⅙·F₁·b³ → ⅙·G₁·b³` (cancels `a⁴·b³/144`).
- `F₁·F₂` unchanged (deg-8+ leading already).

Plus the non-monomial part of W7 (`z·T₆ + T₂·T₅ + T₃·T₄ + T₄·T₃ + T₅·T₂ + T₆·z`)
gets added back as a NEW cluster `½·(z·T₆ + T₂·T₅ + T₃·T₄ + T₄·T₃ + T₅·T₂ + T₆·z)`,
alongside the existing septic-level cluster `½·(z·T₅ + T₂·T₄ + T₃² + T₄·T₂ + T₅·z)`.

The three "tricky" clusters `½·(z·R+R·z) + ½·(T₂²−P²+T₂T₃+T₃T₂) +
½·(z·T₅+T₂·T₄+T₃²+T₄·T₂+T₅·z) + ½·(z·T₆+T₂·T₅+T₃·T₄+T₄·T₃+T₅·T₂+T₆·z)`
have individual deg-6 or deg-7 leading parts, but combine to deg-8+ via the
R+T₅+T₆ identity (`R_plus_T5_plus_T6_eq_neg_deg7_residual`), to be
exploited in the future `norm_combined_tricky_octic_le`.

Proof: `match_scalars <;> ring` (mirrors I1_septic_residual_decomp_eq's pattern). -/
theorem I1_octic_residual_decomp_eq (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (ea eb a b : 𝔸) :
    let D₁ : 𝔸 := ea - 1 - a
    let D₂ : 𝔸 := eb - 1 - b
    let E₁ : 𝔸 := D₁ - (2 : 𝕂)⁻¹ • a ^ 2
    let E₂ : 𝔸 := D₂ - (2 : 𝕂)⁻¹ • b ^ 2
    let F₁ : 𝔸 := E₁ - (6 : 𝕂)⁻¹ • a ^ 3
    let F₂ : 𝔸 := E₂ - (6 : 𝕂)⁻¹ • b ^ 3
    let G₁ : 𝔸 := F₁ - (24 : 𝕂)⁻¹ • a ^ 4
    let G₂ : 𝔸 := F₂ - (24 : 𝕂)⁻¹ • b ^ 4
    let H₁ : 𝔸 := G₁ - (120 : 𝕂)⁻¹ • a ^ 5
    let H₂ : 𝔸 := G₂ - (120 : 𝕂)⁻¹ • b ^ 5
    let I_a : 𝔸 := H₁ - (720 : 𝕂)⁻¹ • a ^ 6
    let I_b : 𝔸 := H₂ - (720 : 𝕂)⁻¹ • b ^ 6
    let J_a : 𝔸 := I_a - (5040 : 𝕂)⁻¹ • a ^ 7
    let J_b : 𝔸 := I_b - (5040 : 𝕂)⁻¹ • b ^ 7
    let P : 𝔸 := ea * eb - 1 - (a + b)
    let z : 𝔸 := a + b
    let Q : 𝔸 := a * D₂ + D₁ * b + D₁ * D₂
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let T₆ : 𝔸 := (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂)
    let W6 : 𝔸 := (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
        (360 : 𝕂)⁻¹ • b ^ 6 -
        (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z)
    let W7 : 𝔸 := (2520 : 𝕂)⁻¹ • a ^ 7 + (360 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (120 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (72 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (72 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (120 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (360 : 𝕂)⁻¹ • (a * b ^ 6) + (2520 : 𝕂)⁻¹ • b ^ 7 -
        (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z)
    let R : 𝔸 := T₃ - E₁ - E₂ - Q + T₄
    -- LHS: I₁ (quartic_identity form) - corr₁ - corr₁_5 - corr₁_6 - corr₁_7
    (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
        (2 : 𝕂)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
        (2 : 𝕂)⁻¹ • P ^ 2) -
      ((24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃ + T₃ * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2) -
      (2 : 𝕂)⁻¹ • W5 -
      (2 : 𝕂)⁻¹ • W6 -
      (2 : 𝕂)⁻¹ • W7 =
    -- RHS: 13 deg-8+ terms (combined into 10 cluster expressions)
    J_a + J_b + a * I_b + I_a * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
    (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) + (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) +
    (2 : 𝕂)⁻¹ • (z * R + R * z) +
    (2 : 𝕂)⁻¹ • (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
    (2 : 𝕂)⁻¹ • (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) +
    (2 : 𝕂)⁻¹ • (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z) := by
  dsimp only
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_neg, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-- Norm bound `‖I₁ residual (RHS form)‖ ≤ 20·s⁶` from precomputed component bounds.
This is the I₁ residual bound from precomputed individual norm bounds.
Combined with I1_residual_decomp_eq (commit 2fccfa8), gives
`‖I₁ - corr₁ - corr₁_5‖ ≤ 20·s⁶` where `s ≤ 1/10`.

The decomp RHS: H₁+H₂+a·G₂+G₁·b+(E₁E₂+½a²F₂+½F₁b²)+½(z·R+R·z)+½(T₂²-P²+T₂T₃+T₃T₂).
Per-term: 1+1+1+1+1+½+½+6+7.5 = 19.5 ≤ 20. -/
theorem norm_I1_residual_RHS_le (a b z H₁ H₂ G₁ G₂ F₁ F₂ E₁ E₂ R T22 : 𝔸)
    {s : ℝ} (hs_nn : 0 ≤ s)
    (hH₁_le : ‖H₁‖ ≤ s ^ 6) (hH₂_le : ‖H₂‖ ≤ s ^ 6)
    (h_aG₂_le : ‖a * G₂‖ ≤ s ^ 6) (h_G₁b_le : ‖G₁ * b‖ ≤ s ^ 6)
    (h_E₁E₂_le : ‖E₁ * E₂‖ ≤ s ^ 6)
    (h_a2F₂_le : ‖a ^ 2 * F₂‖ ≤ s ^ 6) (h_F₁b2_le : ‖F₁ * b ^ 2‖ ≤ s ^ 6)
    (h_zRpRz_le : ‖z * R + R * z‖ ≤ 12 * s ^ 6)
    (h_T22_le : ‖T22‖ ≤ 15 * s ^ 6) :
    ‖H₁ + H₂ + a * G₂ + G₁ * b +
      (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
      (2 : 𝕂)⁻¹ • (z * R + R * z) +
      (2 : 𝕂)⁻¹ • T22‖ ≤ 20 * s ^ 6 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_a2F2_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * F₂)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * F₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2F₂_le (by norm_num)
      _ = s ^ 6 / 2 := by ring
  have h_F1b2_smul : ‖(2 : 𝕂)⁻¹ • (F₁ * b ^ 2)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖F₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_F₁b2_le (by norm_num)
      _ = s ^ 6 / 2 := by ring
  have h_zRpRz_smul : ‖(2 : 𝕂)⁻¹ • (z * R + R * z)‖ ≤ 6 * s ^ 6 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖z * R + R * z‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (12 * s ^ 6) := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_zRpRz_le (by norm_num)
      _ = 6 * s ^ 6 := by ring
  have h_T22_smul : ‖(2 : 𝕂)⁻¹ • T22‖ ≤ 15 * s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖T22‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (15 * s ^ 6) := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_T22_le (by norm_num)
      _ = 15 * s ^ 6 / 2 := by ring
  -- Triangle inequality on the 9-term sum
  -- Outer: (H₁+H₂+a*G₂+G₁*b) + inner_3 + ½(zR+Rz) + ½T22
  -- Inner_3 = E₁*E₂ + ½(a²*F₂) + ½(F₁*b²)
  have h_inner3 : ‖E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) +
      (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)‖ ≤ s ^ 6 + s ^ 6 / 2 + s ^ 6 / 2 := by
    have hi1 := norm_add_le (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂))
      ((2 : 𝕂)⁻¹ • (F₁ * b ^ 2))
    have hi2 := norm_add_le (E₁ * E₂) ((2 : 𝕂)⁻¹ • (a ^ 2 * F₂))
    linarith
  -- Outer chain: 4 + inner + 2 = 7 norm_add_le applications
  have ha1 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b +
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) +
    (2 : 𝕂)⁻¹ • (z * R + R * z)) ((2 : 𝕂)⁻¹ • T22)
  have ha2 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b +
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)))
    ((2 : 𝕂)⁻¹ • (z * R + R * z))
  have ha3 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b)
    (E₁ * E₂ + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂) + (2 : 𝕂)⁻¹ • (F₁ * b ^ 2))
  have ha4 := norm_add_le (H₁ + H₂ + a * G₂) (G₁ * b)
  have ha5 := norm_add_le (H₁ + H₂) (a * G₂)
  have ha6 := norm_add_le H₁ H₂
  -- Sum: 1+1+1+1 + (1+½+½) + 6 + 7.5 = 19.5 ≤ 20
  linarith [pow_nonneg hs_nn 6]

set_option maxHeartbeats 4000000 in
/-- Norm bound for the RHS of `I1_septic_residual_decomp_eq`.

Given precomputed bounds for the 9 "easy" pieces (each ≤ s⁷) and one
COMBINED bound for the three "tricky" pieces
(`‖z·R+R·z + T22 + T_extra‖ ≤ C·s⁷`), bounds the RHS by `(7 + C/2)·s⁷`.

The combined parameterization is essential: each individual piece
(z·R+R·z, T22, T_extra) is naturally deg-6, NOT deg-7. Only the SUM
is deg-7+ via the cancellations in `norm_combined_tricky_le`.

Per-term contributions (in units of s⁷):
- 4 outer terms (I_a + I_b + a·H₂ + H₁·b) → 4·s⁷.
- Inner cluster `(1/6)·a³F₂ + (1/6)·F₁b³ + F₁F₂` → (1/6 + 1/6 + 1) = 4/3·s⁷.
- Two `(1/2)•` smul'd terms (a²G₂, G₁b²) → 1/2 + 1/2 = 1·s⁷.
- Combined `(1/2)•` smul'd tricky → C/2·s⁷.
- Total: 4 + 4/3 + 1 + C/2 = 19/3 + C/2 ≤ 7 + C/2. -/
theorem norm_I1_septic_residual_RHS_le (a b z I_a I_b H₁ H₂ F₁ F₂ G₁ G₂ R T22
    T_extra : 𝔸)
    {s C : ℝ} (hs_nn : 0 ≤ s) (hC_nn : 0 ≤ C)
    (hI_a_le : ‖I_a‖ ≤ s ^ 7) (hI_b_le : ‖I_b‖ ≤ s ^ 7)
    (h_aH₂_le : ‖a * H₂‖ ≤ s ^ 7) (h_H₁b_le : ‖H₁ * b‖ ≤ s ^ 7)
    (h_a3F₂_le : ‖a ^ 3 * F₂‖ ≤ s ^ 7)
    (h_F₁b3_le : ‖F₁ * b ^ 3‖ ≤ s ^ 7)
    (h_F₁F₂_le : ‖F₁ * F₂‖ ≤ s ^ 7)
    (h_a2G₂_le : ‖a ^ 2 * G₂‖ ≤ s ^ 7)
    (h_G₁b2_le : ‖G₁ * b ^ 2‖ ≤ s ^ 7)
    (h_combined_le : ‖z * R + R * z + T22 + T_extra‖ ≤ C * s ^ 7) :
    ‖I_a + I_b + a * H₂ + H₁ * b +
      ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
      (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) + (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) +
      (2 : 𝕂)⁻¹ • (z * R + R * z) +
      (2 : 𝕂)⁻¹ • T22 +
      (2 : 𝕂)⁻¹ • T_extra‖ ≤ (7 + C / 2) * s ^ 7 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Re-associate to group the 3 smul'd tricky terms together.
  have h_assoc :
      I_a + I_b + a * H₂ + H₁ * b +
        ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
        (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) + (2 : 𝕂)⁻¹ • (G₁ * b ^ 2) +
        (2 : 𝕂)⁻¹ • (z * R + R * z) + (2 : 𝕂)⁻¹ • T22 +
        (2 : 𝕂)⁻¹ • T_extra =
      (I_a + I_b + a * H₂ + H₁ * b +
        ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
        (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) + (2 : 𝕂)⁻¹ • (G₁ * b ^ 2)) +
      ((2 : 𝕂)⁻¹ • (z * R + R * z) + (2 : 𝕂)⁻¹ • T22 +
        (2 : 𝕂)⁻¹ • T_extra) := by abel
  -- Combine the 3 smul terms into one.
  have h_smul_combine : (2 : 𝕂)⁻¹ • (z * R + R * z) + (2 : 𝕂)⁻¹ • T22 +
      (2 : 𝕂)⁻¹ • T_extra = (2 : 𝕂)⁻¹ • (z * R + R * z + T22 + T_extra) := by
    rw [← smul_add, ← smul_add]
  rw [h_assoc, h_smul_combine]
  -- Smul-prefixed bounds.
  have h_a3F2_smul : ‖(6 : 𝕂)⁻¹ • (a ^ 3 * F₂)‖ ≤ s ^ 7 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖a ^ 3 * F₂‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 7 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_a3F₂_le (by norm_num)
      _ = s ^ 7 / 6 := by ring
  have h_F1b3_smul : ‖(6 : 𝕂)⁻¹ • (F₁ * b ^ 3)‖ ≤ s ^ 7 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖F₁ * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 7 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_F₁b3_le (by norm_num)
      _ = s ^ 7 / 6 := by ring
  have h_a2G2_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * G₂)‖ ≤ s ^ 7 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * G₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 7 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2G₂_le (by norm_num)
      _ = s ^ 7 / 2 := by ring
  have h_G1b2_smul : ‖(2 : 𝕂)⁻¹ • (G₁ * b ^ 2)‖ ≤ s ^ 7 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖G₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 7 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_G₁b2_le (by norm_num)
      _ = s ^ 7 / 2 := by ring
  have h_combined_smul : ‖(2 : 𝕂)⁻¹ • (z * R + R * z + T22 + T_extra)‖ ≤
      C * s ^ 7 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖z * R + R * z + T22 + T_extra‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (C * s ^ 7) := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_combined_le (by norm_num)
      _ = C * s ^ 7 / 2 := by ring
  -- Inner 3-term cluster: (1/6)·a³F₂ + (1/6)·F₁b³ + F₁F₂ ≤ s⁷/6 + s⁷/6 + s⁷ = (4/3)·s⁷.
  have h_inner : ‖(6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂‖ ≤
      s ^ 7 / 6 + s ^ 7 / 6 + s ^ 7 := by
    have hi1 := norm_add_le ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3)) (F₁ * F₂)
    have hi2 := norm_add_le ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂)) ((6 : 𝕂)⁻¹ • (F₁ * b ^ 3))
    linarith
  -- Triangle inequality on the (outer 7) + (combined smul'd 3) split.
  -- Outer = I_a + I_b + a·H₂ + H₁·b + inner_3 + ½a²G₂ + ½G₁b²
  -- Total: 4·s⁷ + 4/3·s⁷ + s⁷ = 19/3·s⁷
  have ha_main := norm_add_le (I_a + I_b + a * H₂ + H₁ * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
    (2 : 𝕂)⁻¹ • (a ^ 2 * G₂) + (2 : 𝕂)⁻¹ • (G₁ * b ^ 2))
    ((2 : 𝕂)⁻¹ • (z * R + R * z + T22 + T_extra))
  have ha1 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂) +
    (2 : 𝕂)⁻¹ • (a ^ 2 * G₂)) ((2 : 𝕂)⁻¹ • (G₁ * b ^ 2))
  have ha2 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂))
    ((2 : 𝕂)⁻¹ • (a ^ 2 * G₂))
  have ha3 := norm_add_le (I_a + I_b + a * H₂ + H₁ * b)
    ((6 : 𝕂)⁻¹ • (a ^ 3 * F₂) + (6 : 𝕂)⁻¹ • (F₁ * b ^ 3) + F₁ * F₂)
  have ha4 := norm_add_le (I_a + I_b + a * H₂) (H₁ * b)
  have ha5 := norm_add_le (I_a + I_b) (a * H₂)
  have ha6 := norm_add_le I_a I_b
  -- Sum: 4·s⁷ + 4/3·s⁷ + 1·s⁷ + C/2·s⁷ = 19/3·s⁷ + C/2·s⁷ ≤ 7·s⁷ + C/2·s⁷.
  nlinarith [pow_nonneg hs_nn 7]

set_option maxHeartbeats 4000000 in
/-- Norm bound for the RHS of `I1_octic_residual_decomp_eq`.

Given precomputed bounds for the 9 "easy" pieces (each ≤ s⁸) and one
COMBINED bound for the four "tricky" pieces
(`‖z·R+R·z + T22 + T_extra + T_extra2‖ ≤ C·s⁸`), bounds the RHS by `(7 + C/2)·s⁸`.

The combined parameterization is essential: each individual piece
(z·R+R·z, T22, T_extra, T_extra2) is naturally deg-6 or deg-7, NOT deg-8.
Only the SUM is deg-8+ via the cancellations in `norm_combined_tricky_octic_le`
(R+T₅+T₆ identity + P²_deg≥8 decomposition).

Per-term contributions (in units of s⁸):
- 4 outer terms (J_a + J_b + a·I_b + I_a·b) → 4·s⁸.
- Inner cluster `(1/6)·a³G₂ + (1/6)·G₁b³ + F₁F₂` → (1/6 + 1/6 + 1) = 4/3·s⁸.
- Two `(1/2)•` smul'd terms (a²H₂, H₁b²) → 1/2 + 1/2 = 1·s⁸.
- Combined `(1/2)•` smul'd tricky → C/2·s⁸.
- Total: 4 + 4/3 + 1 + C/2 = 19/3 + C/2 ≤ 7 + C/2.

Direct analog of `norm_I1_septic_residual_RHS_le` at one degree higher. -/
theorem norm_I1_octic_residual_RHS_le (a b z J_a J_b I_a I_b H₁ H₂ G₁ G₂
    F₁ F₂ R T22 T_extra T_extra2 : 𝔸)
    {s C : ℝ} (hs_nn : 0 ≤ s) (hC_nn : 0 ≤ C)
    (hJ_a_le : ‖J_a‖ ≤ s ^ 8) (hJ_b_le : ‖J_b‖ ≤ s ^ 8)
    (h_aI_b_le : ‖a * I_b‖ ≤ s ^ 8) (h_I_ab_le : ‖I_a * b‖ ≤ s ^ 8)
    (h_a3G₂_le : ‖a ^ 3 * G₂‖ ≤ s ^ 8)
    (h_G₁b3_le : ‖G₁ * b ^ 3‖ ≤ s ^ 8)
    (h_F₁F₂_le : ‖F₁ * F₂‖ ≤ s ^ 8)
    (h_a2H₂_le : ‖a ^ 2 * H₂‖ ≤ s ^ 8)
    (h_H₁b2_le : ‖H₁ * b ^ 2‖ ≤ s ^ 8)
    (h_combined_le : ‖z * R + R * z + T22 + T_extra + T_extra2‖ ≤ C * s ^ 8) :
    ‖J_a + J_b + a * I_b + I_a * b +
      ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
      (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) + (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) +
      (2 : 𝕂)⁻¹ • (z * R + R * z) +
      (2 : 𝕂)⁻¹ • T22 +
      (2 : 𝕂)⁻¹ • T_extra +
      (2 : 𝕂)⁻¹ • T_extra2‖ ≤ (7 + C / 2) * s ^ 8 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h6eq : ‖(6 : 𝕂)⁻¹‖ = (6 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  -- Re-associate to group the 4 smul'd tricky terms together.
  have h_assoc :
      J_a + J_b + a * I_b + I_a * b +
        ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
        (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) + (2 : 𝕂)⁻¹ • (H₁ * b ^ 2) +
        (2 : 𝕂)⁻¹ • (z * R + R * z) + (2 : 𝕂)⁻¹ • T22 +
        (2 : 𝕂)⁻¹ • T_extra + (2 : 𝕂)⁻¹ • T_extra2 =
      (J_a + J_b + a * I_b + I_a * b +
        ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
        (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) + (2 : 𝕂)⁻¹ • (H₁ * b ^ 2)) +
      ((2 : 𝕂)⁻¹ • (z * R + R * z) + (2 : 𝕂)⁻¹ • T22 +
        (2 : 𝕂)⁻¹ • T_extra + (2 : 𝕂)⁻¹ • T_extra2) := by abel
  -- Combine the 4 smul terms into one.
  have h_smul_combine : (2 : 𝕂)⁻¹ • (z * R + R * z) + (2 : 𝕂)⁻¹ • T22 +
      (2 : 𝕂)⁻¹ • T_extra + (2 : 𝕂)⁻¹ • T_extra2 =
      (2 : 𝕂)⁻¹ • (z * R + R * z + T22 + T_extra + T_extra2) := by
    rw [← smul_add, ← smul_add, ← smul_add]
  rw [h_assoc, h_smul_combine]
  -- Smul-prefixed bounds.
  have h_a3G2_smul : ‖(6 : 𝕂)⁻¹ • (a ^ 3 * G₂)‖ ≤ s ^ 8 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖a ^ 3 * G₂‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 8 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_a3G₂_le (by norm_num)
      _ = s ^ 8 / 6 := by ring
  have h_G1b3_smul : ‖(6 : 𝕂)⁻¹ • (G₁ * b ^ 3)‖ ≤ s ^ 8 / 6 := by
    calc _ ≤ ‖(6 : 𝕂)⁻¹‖ * ‖G₁ * b ^ 3‖ := norm_smul_le _ _
      _ ≤ (6 : ℝ)⁻¹ * s ^ 8 := by
          rw [h6eq]; exact mul_le_mul_of_nonneg_left h_G₁b3_le (by norm_num)
      _ = s ^ 8 / 6 := by ring
  have h_a2H2_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * H₂)‖ ≤ s ^ 8 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * H₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 8 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2H₂_le (by norm_num)
      _ = s ^ 8 / 2 := by ring
  have h_H1b2_smul : ‖(2 : 𝕂)⁻¹ • (H₁ * b ^ 2)‖ ≤ s ^ 8 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖H₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 8 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_H₁b2_le (by norm_num)
      _ = s ^ 8 / 2 := by ring
  have h_combined_smul : ‖(2 : 𝕂)⁻¹ • (z * R + R * z + T22 + T_extra + T_extra2)‖ ≤
      C * s ^ 8 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖z * R + R * z + T22 + T_extra + T_extra2‖ :=
            norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (C * s ^ 8) := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_combined_le (by norm_num)
      _ = C * s ^ 8 / 2 := by ring
  -- Inner 3-term cluster: (1/6)·a³G₂ + (1/6)·G₁b³ + F₁F₂ ≤ s⁸/6 + s⁸/6 + s⁸ = (4/3)·s⁸.
  have h_inner :
      ‖(6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂‖ ≤
      s ^ 8 / 6 + s ^ 8 / 6 + s ^ 8 := by
    have hi1 := norm_add_le ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3))
      (F₁ * F₂)
    have hi2 := norm_add_le ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂)) ((6 : 𝕂)⁻¹ • (G₁ * b ^ 3))
    linarith
  -- Triangle inequality on the (outer 7) + (combined smul'd) split.
  -- Outer = J_a + J_b + a·I_b + I_a·b + inner_3 + ½a²H₂ + ½H₁b²
  -- Total: 4·s⁸ + 4/3·s⁸ + 1·s⁸ = 19/3·s⁸
  have ha_main := norm_add_le (J_a + J_b + a * I_b + I_a * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
    (2 : 𝕂)⁻¹ • (a ^ 2 * H₂) + (2 : 𝕂)⁻¹ • (H₁ * b ^ 2))
    ((2 : 𝕂)⁻¹ • (z * R + R * z + T22 + T_extra + T_extra2))
  have ha1 := norm_add_le (J_a + J_b + a * I_b + I_a * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂) +
    (2 : 𝕂)⁻¹ • (a ^ 2 * H₂)) ((2 : 𝕂)⁻¹ • (H₁ * b ^ 2))
  have ha2 := norm_add_le (J_a + J_b + a * I_b + I_a * b +
    ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂))
    ((2 : 𝕂)⁻¹ • (a ^ 2 * H₂))
  have ha3 := norm_add_le (J_a + J_b + a * I_b + I_a * b)
    ((6 : 𝕂)⁻¹ • (a ^ 3 * G₂) + (6 : 𝕂)⁻¹ • (G₁ * b ^ 3) + F₁ * F₂)
  have ha4 := norm_add_le (J_a + J_b + a * I_b) (I_a * b)
  have ha5 := norm_add_le (J_a + J_b) (a * I_b)
  have ha6 := norm_add_le J_a J_b
  -- Sum: 4·s⁸ + 4/3·s⁸ + 1·s⁸ + C/2·s⁸ = 19/3·s⁸ + C/2·s⁸ ≤ 7·s⁸ + C/2·s⁸.
  nlinarith [pow_nonneg hs_nn 8]

/-- Norm bound for the RHS of `I2_septic_residual_decomp_eq`.

Given precomputed bounds for the 4 input pieces (with parameterized constants
K_PmT4, K_P2, K_PzP, K_P3), bounds the RHS by `(3·K_PmT4 + 2·K_P2 + K_PzP + K_P3)·s⁷`.

Per-term contributions:
- 3 weight-1 (P-T₂-T₃-T₄) middle terms: each ≤ K_PmT4·s⁷.
- 2 compound `z·(P²-T₂²-T₂T₃-T₃T₂)`-style terms: each ≤ K_P2·s⁷.
- 1 sandwich `PzP-T₂zT₂-T₂zT₃-T₃zT₂` term: ≤ K_PzP·s⁷.
- 1 (P³ - T₂³) term: ≤ K_P3·s⁷.

The user supplies the parameterized bounds; this wrapper combines via
triangle inequality. -/
theorem norm_I2_septic_residual_RHS_le (z P T₂ T₃ T₄ : 𝔸)
    {s K_PmT4 K_P2 K_PzP K_P3 : ℝ} (hs_nn : 0 ≤ s)
    (hK_PmT4_nn : 0 ≤ K_PmT4) (hK_P2_nn : 0 ≤ K_P2)
    (hK_PzP_nn : 0 ≤ K_PzP) (hK_P3_nn : 0 ≤ K_P3)
    (hz : ‖z‖ ≤ s)
    (hPmT4_le : ‖P - T₂ - T₃ - T₄‖ ≤ K_PmT4 * s ^ 5)
    (hP2_etc_le : ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ ≤ K_P2 * s ^ 6)
    (hPzP_etc_le :
        ‖P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂‖ ≤ K_PzP * s ^ 7)
    (hP3_le : ‖P ^ 3 - T₂ ^ 3‖ ≤ K_P3 * s ^ 7) :
    ‖z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
      (P - T₂ - T₃ - T₄) * z ^ 2 +
      z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) +
      (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂) +
      (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z +
      (P ^ 3 - T₂ ^ 3)‖ ≤
      (3 * K_PmT4 + 2 * K_P2 + K_PzP + K_P3) * s ^ 7 := by
  -- Bound each of the 7 outer terms.
  have h1 : ‖z ^ 2 * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 2 * (K_PmT4 * s ^ 5) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P - T₂ - T₃ - T₄‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (K_PmT4 * s ^ 5) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz 2)
          hPmT4_le (norm_nonneg _) (by positivity)
  have h2 : ‖z * (P - T₂ - T₃ - T₄) * z‖ ≤ s * (K_PmT4 * s ^ 5) * s :=
    calc _ ≤ ‖z * (P - T₂ - T₃ - T₄)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃ - T₄‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (K_PmT4 * s ^ 5)) * s := by
          apply mul_le_mul _ hz (norm_nonneg _) (by positivity)
          exact mul_le_mul hz hPmT4_le (norm_nonneg _) (by positivity)
  have h3 : ‖(P - T₂ - T₃ - T₄) * z ^ 2‖ ≤ (K_PmT4 * s ^ 5) * s ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃ - T₄‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (K_PmT4 * s ^ 5) * s ^ 2 := mul_le_mul hPmT4_le
          (pow_le_pow_left₀ (norm_nonneg _) hz 2) (by positivity) (by positivity)
  have h4 : ‖z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂)‖ ≤ s * (K_P2 * s ^ 6) :=
    calc _ ≤ ‖z‖ * ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ := norm_mul_le _ _
      _ ≤ s * (K_P2 * s ^ 6) := mul_le_mul hz hP2_etc_le (norm_nonneg _) (by positivity)
  have h6 : ‖(P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z‖ ≤ (K_P2 * s ^ 6) * s :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (K_P2 * s ^ 6) * s := mul_le_mul hP2_etc_le hz (norm_nonneg _) (by positivity)
  -- Sum 7 terms via triangle inequality (6 norm_add_le).
  have ha1 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
    (P - T₂ - T₃ - T₄) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) +
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂) +
    (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z) (P ^ 3 - T₂ ^ 3)
  have ha2 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
    (P - T₂ - T₃ - T₄) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) +
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂))
    ((P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z)
  have ha3 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
    (P - T₂ - T₃ - T₄) * z ^ 2 +
    z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂))
    (P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂)
  have ha4 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z +
    (P - T₂ - T₃ - T₄) * z ^ 2) (z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂))
  have ha5 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄) + z * (P - T₂ - T₃ - T₄) * z)
    ((P - T₂ - T₃ - T₄) * z ^ 2)
  have ha6 := norm_add_le (z ^ 2 * (P - T₂ - T₃ - T₄)) (z * (P - T₂ - T₃ - T₄) * z)
  -- Sum: 3·K_PmT4 + 2·K_P2 + K_PzP + K_P3 (in units of s⁷).
  nlinarith [pow_nonneg hs_nn 7]

/-- Norm bound `‖T₂² - P² + T₂T₃ + T₃T₂‖ ≤ 15·s⁶`. Decomposition uses
`P² - T₂² - T₂T₃ - T₃T₂ = (P-T₂-T₃)·P + T₂·(P-T₂-T₃) + T₃·(P-T₂)`. -/
theorem norm_T22_sub_P2_etc_le (P T₂ T₃ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂‖ ≤ 15 * s ^ 6 := by
  have heq : T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂ =
      -((P - T₂ - T₃) * P + T₂ * (P - T₂ - T₃) + T₃ * (P - T₂)) := by noncomm_ring
  rw [heq, norm_neg]
  have h1 : ‖(P - T₂ - T₃) * P‖ ≤ (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (5 * s ^ 4) * s ^ 2 := mul_le_mul hPmT₂mT₃ hP (norm_nonneg _) (by positivity)
  have h2 : ‖T₂ * (P - T₂ - T₃)‖ ≤ s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖T₂‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ s ^ 2 * (5 * s ^ 4) := mul_le_mul hT₂ hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have h3 : ‖T₃ * (P - T₂)‖ ≤ s ^ 3 * (5 * s ^ 3) :=
    calc _ ≤ ‖T₃‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ s ^ 3 * (5 * s ^ 3) := mul_le_mul hT₃ hPmT₂ (norm_nonneg _) (by positivity)
  have ha1 := norm_add_le ((P - T₂ - T₃) * P + T₂ * (P - T₂ - T₃)) (T₃ * (P - T₂))
  have ha2 := norm_add_le ((P - T₂ - T₃) * P) (T₂ * (P - T₂ - T₃))
  linarith [pow_nonneg hs_nn 6]

/-- Norm bound `‖R-residual sum‖ ≤ 6·s⁵` from precomputed component bounds.
The 7 terms come from R_eq_neg_deg5_residual: G₁+G₂+a·F₂+F₁·b+E₁·E₂+½E₁b²+½a²E₂. -/
theorem norm_R_residual_sum_le (G₁ G₂ F₁ F₂ E₁ E₂ a b : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hG₁_le : ‖G₁‖ ≤ s ^ 5) (hG₂_le : ‖G₂‖ ≤ s ^ 5)
    (h_aF₂_le : ‖a * F₂‖ ≤ s ^ 5) (h_F₁b_le : ‖F₁ * b‖ ≤ s ^ 5)
    (h_E₁E₂_le : ‖E₁ * E₂‖ ≤ s ^ 6)
    (h_E₁b2_le : ‖E₁ * b ^ 2‖ ≤ s ^ 5)
    (h_a2E₂_le : ‖a ^ 2 * E₂‖ ≤ s ^ 5) :
    ‖G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (E₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * E₂)‖ ≤ 6 * s ^ 5 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_smul1 : ‖(2 : 𝕂)⁻¹ • (E₁ * b ^ 2)‖ ≤ s ^ 5 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖E₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 5 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_E₁b2_le (by norm_num)
      _ = s ^ 5 / 2 := by ring
  have h_smul2 : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * E₂)‖ ≤ s ^ 5 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * E₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 5 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2E₂_le (by norm_num)
      _ = s ^ 5 / 2 := by ring
  have hs6 : s ^ 6 ≤ s ^ 5 / 10 := by
    have h_eq : s ^ 6 = s ^ 5 * s := by ring
    rw [h_eq]
    have : s ^ 5 * s ≤ s ^ 5 * (1 / 10) := by
      apply mul_le_mul_of_nonneg_left hs_small (pow_nonneg hs_nn 5)
    linarith
  have ha1 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂ +
    (2 : 𝕂)⁻¹ • (E₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * E₂))
  have ha2 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b + E₁ * E₂)
    ((2 : 𝕂)⁻¹ • (E₁ * b ^ 2))
  have ha3 := norm_add_le (G₁ + G₂ + a * F₂ + F₁ * b) (E₁ * E₂)
  have ha4 := norm_add_le (G₁ + G₂ + a * F₂) (F₁ * b)
  have ha5 := norm_add_le (G₁ + G₂) (a * F₂)
  have ha6 := norm_add_le G₁ G₂
  linarith [pow_nonneg hs_nn 5, pow_nonneg hs_nn 6]

/-- Norm bound `‖R+T₅ residual sum‖ ≤ 6·s⁶` from precomputed component bounds.
The 7 terms come from `R_plus_T5_eq_neg_deg6_residual`:
H₁+H₂+a·G₂+G₁·b+E₁·E₂+½·F₁·b²+½·a²·F₂. Analog of `norm_R_residual_sum_le`
at one degree higher; all inputs are already deg-6, so no `s ≤ 1/10`
constraint is needed. -/
theorem norm_R_plus_T5_residual_sum_le (H₁ H₂ G₁ G₂ F₁ F₂ E₁ E₂ a b : 𝔸)
    {s : ℝ} (hs_nn : 0 ≤ s)
    (hH₁_le : ‖H₁‖ ≤ s ^ 6) (hH₂_le : ‖H₂‖ ≤ s ^ 6)
    (h_aG₂_le : ‖a * G₂‖ ≤ s ^ 6) (h_G₁b_le : ‖G₁ * b‖ ≤ s ^ 6)
    (h_E₁E₂_le : ‖E₁ * E₂‖ ≤ s ^ 6)
    (h_F₁b2_le : ‖F₁ * b ^ 2‖ ≤ s ^ 6)
    (h_a2F₂_le : ‖a ^ 2 * F₂‖ ≤ s ^ 6) :
    ‖H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂ +
      (2 : 𝕂)⁻¹ • (F₁ * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * F₂)‖ ≤ 6 * s ^ 6 := by
  have h2eq : ‖(2 : 𝕂)⁻¹‖ = (2 : ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have h_F1b2_smul : ‖(2 : 𝕂)⁻¹ • (F₁ * b ^ 2)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖F₁ * b ^ 2‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_F₁b2_le (by norm_num)
      _ = s ^ 6 / 2 := by ring
  have h_a2F2_smul : ‖(2 : 𝕂)⁻¹ • (a ^ 2 * F₂)‖ ≤ s ^ 6 / 2 := by
    calc _ ≤ ‖(2 : 𝕂)⁻¹‖ * ‖a ^ 2 * F₂‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * s ^ 6 := by
          rw [h2eq]; exact mul_le_mul_of_nonneg_left h_a2F₂_le (by norm_num)
      _ = s ^ 6 / 2 := by ring
  have ha1 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂ +
    (2 : 𝕂)⁻¹ • (F₁ * b ^ 2)) ((2 : 𝕂)⁻¹ • (a ^ 2 * F₂))
  have ha2 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b + E₁ * E₂)
    ((2 : 𝕂)⁻¹ • (F₁ * b ^ 2))
  have ha3 := norm_add_le (H₁ + H₂ + a * G₂ + G₁ * b) (E₁ * E₂)
  have ha4 := norm_add_le (H₁ + H₂ + a * G₂) (G₁ * b)
  have ha5 := norm_add_le (H₁ + H₂) (a * G₂)
  have ha6 := norm_add_le H₁ H₂
  -- Total: 5·s⁶ + s⁶/2 + s⁶/2 = 6·s⁶
  linarith [pow_nonneg hs_nn 6]

/-- Norm bound for `‖PzP - T₂zT₂‖ ≤ 13·s⁶` for small s (`s < 1/10`).
Splits via `P = T₂ + (P-T₂)` into 3 terms each bounded by Cs⁶. -/
private theorem norm_PzP_sub_T2zT2_le (z P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_small : s ≤ 1 / 10) (hz : ‖z‖ ≤ s) (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖P * z * P - T₂ * z * T₂‖ ≤ 13 * s ^ 6 := by
  have heq : P * z * P - T₂ * z * T₂ =
      T₂ * z * (P - T₂) + (P - T₂) * z * T₂ + (P - T₂) * z * (P - T₂) := by
    have hP : P = T₂ + (P - T₂) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  have ht1 : ‖T₂ * z * (P - T₂)‖ ≤ s ^ 2 * s * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hz (norm_nonneg _) (by positivity)
  have ht2 : ‖(P - T₂) * z * T₂‖ ≤ (5 * s ^ 3) * s * s ^ 2 :=
    calc _ ≤ ‖(P - T₂) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ hz (norm_nonneg _) (by positivity)
  have ht3 : ‖(P - T₂) * z * (P - T₂)‖ ≤ (5 * s ^ 3) * s * (5 * s ^ 3) :=
    calc _ ≤ ‖(P - T₂) * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ hz (norm_nonneg _) (by positivity)
  have hadd1 := norm_add_le (T₂ * z * (P - T₂) + (P - T₂) * z * T₂)
    ((P - T₂) * z * (P - T₂))
  have hadd2 := norm_add_le (T₂ * z * (P - T₂)) ((P - T₂) * z * T₂)
  -- Total: 5s⁶ + 5s⁶ + 25s⁷ ≤ 5 + 5 + 25·(1/10)·s⁶ = 12.5s⁶ ≤ 13s⁶
  nlinarith [pow_nonneg hs_nn 6, pow_nonneg hs_nn 7]

/-- Norm bound for `‖PzP - T₂zT₂ - T₂zT₃ - T₃zT₂‖ ≤ 13·s⁷` for small s
(`s ≤ 1/10`). Decomposes via `P = T₂ + T₃ + (P-T₂-T₃)` into 6 terms.
The "I2 sandwich" piece for the septic residual; provides K_PzP = 13. -/
theorem norm_PzP_sub_T2zT2_etc_le (z P T₂ T₃ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_small : s ≤ 1 / 10) (hz : ‖z‖ ≤ s) (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hT₃ : ‖T₃‖ ≤ s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂‖ ≤ 13 * s ^ 7 := by
  have heq : P * z * P - T₂ * z * T₂ - T₂ * z * T₃ - T₃ * z * T₂ =
      T₂ * z * (P - T₂ - T₃) + T₃ * z * T₃ + T₃ * z * (P - T₂ - T₃) +
      (P - T₂ - T₃) * z * T₂ + (P - T₂ - T₃) * z * T₃ +
      (P - T₂ - T₃) * z * (P - T₂ - T₃) := by
    have hP : P = T₂ + T₃ + (P - T₂ - T₃) := by abel
    rw [hP]; noncomm_ring
  rw [heq]
  have h1 : ‖T₂ * z * (P - T₂ - T₃)‖ ≤ s ^ 2 * s * (5 * s ^ 4) :=
    calc _ ≤ ‖T₂ * z‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖) * ‖P - T₂ - T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hz (norm_nonneg _) (by positivity)
  have h2 : ‖T₃ * z * T₃‖ ≤ s ^ 3 * s * s ^ 3 :=
    calc _ ≤ ‖T₃ * z‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖z‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * s) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hz (norm_nonneg _) (by positivity)
  have h3 : ‖T₃ * z * (P - T₂ - T₃)‖ ≤ s ^ 3 * s * (5 * s ^ 4) :=
    calc _ ≤ ‖T₃ * z‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₃‖ * ‖z‖) * ‖P - T₂ - T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 3 * s) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₃ hz (norm_nonneg _) (by positivity)
  have h4 : ‖(P - T₂ - T₃) * z * T₂‖ ≤ (5 * s ^ 4) * s * s ^ 2 :=
    calc _ ≤ ‖(P - T₂ - T₃) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃‖ * ‖z‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 4) * s) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ hz (norm_nonneg _) (by positivity)
  have h5 : ‖(P - T₂ - T₃) * z * T₃‖ ≤ (5 * s ^ 4) * s * s ^ 3 :=
    calc _ ≤ ‖(P - T₂ - T₃) * z‖ * ‖T₃‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃‖ * ‖z‖) * ‖T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 4) * s) * s ^ 3 := by
          apply mul_le_mul _ hT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ hz (norm_nonneg _) (by positivity)
  have h6 : ‖(P - T₂ - T₃) * z * (P - T₂ - T₃)‖ ≤ (5 * s ^ 4) * s * (5 * s ^ 4) :=
    calc _ ≤ ‖(P - T₂ - T₃) * z‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃‖ * ‖z‖) * ‖P - T₂ - T₃‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 4) * s) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ hz (norm_nonneg _) (by positivity)
  -- Triangle inequality (5 norm_add_le's chained left-to-right)
  have ha1 := norm_add_le (T₂ * z * (P - T₂ - T₃) + T₃ * z * T₃ + T₃ * z * (P - T₂ - T₃) +
    (P - T₂ - T₃) * z * T₂ + (P - T₂ - T₃) * z * T₃) ((P - T₂ - T₃) * z * (P - T₂ - T₃))
  have ha2 := norm_add_le (T₂ * z * (P - T₂ - T₃) + T₃ * z * T₃ + T₃ * z * (P - T₂ - T₃) +
    (P - T₂ - T₃) * z * T₂) ((P - T₂ - T₃) * z * T₃)
  have ha3 := norm_add_le (T₂ * z * (P - T₂ - T₃) + T₃ * z * T₃ + T₃ * z * (P - T₂ - T₃))
    ((P - T₂ - T₃) * z * T₂)
  have ha4 := norm_add_le (T₂ * z * (P - T₂ - T₃) + T₃ * z * T₃) (T₃ * z * (P - T₂ - T₃))
  have ha5 := norm_add_le (T₂ * z * (P - T₂ - T₃)) (T₃ * z * T₃)
  -- Sum of bounds: 5s⁷ + s⁷ + 5s⁸ + 5s⁷ + 5s⁸ + 25s⁹ = 11s⁷ + 10s⁸ + 25s⁹.
  -- For s ≤ 1/10: ≤ 11s⁷ + 1·s⁷ + 0.25·s⁷ = 12.25·s⁷ ≤ 13·s⁷.
  nlinarith [pow_nonneg hs_nn 7, pow_nonneg hs_nn 8, pow_nonneg hs_nn 9,
    mul_nonneg (pow_nonneg hs_nn 7) hs_nn,
    mul_nonneg (pow_nonneg hs_nn 7) (sq_nonneg s)]

set_option maxHeartbeats 4000000 in
/-- **Combined tricky bound** for the I1 septic residual.
The sum of the three "tricky" pieces `(z·R+R·z) + T22 + T_extra`
where T22 = T₂² - P² + T₂T₃ + T₃T₂ and T_extra = z·T₅ + T₂T₄ + T₃² + T₄T₂ + T₅z.
Individually, each piece is deg-6, NOT deg-7 — but the SUM is deg-7+ via:
- `R₅ = -T₅` (deg-5 cancellation): combining z·R+R·z with z·T₅+T₅z gives
  z·(R+T₅) + (R+T₅)·z, which is deg-7+ via `‖R+T₅‖ ≤ 6·s⁶`.
- Algebraic identity `P² = T₂² + (T₂T₃+T₃T₂) + (T₂T₄+T₃²+T₄T₂) + P²_deg≥7`:
  the deg-≤6 contributions of T22 + T_extra cancel with the deg-≤6 of P²,
  leaving -P²_deg≥7 which is deg-7+ via D₅ := P-T₂-T₃-T₄.

Bound: ‖combined‖ ≤ 12·s⁷ (z·(R+T₅) part) + ~16·s⁷ (P²_deg≥7) ≤ 28·s⁷
for `s ≤ 1/10`. -/
theorem norm_combined_tricky_le (z P R T₂ T₃ T₄ T₅ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hz : ‖z‖ ≤ s) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3)
    (hT₄ : ‖T₄‖ ≤ s ^ 4)
    (hRT5 : ‖R + T₅‖ ≤ 6 * s ^ 6)
    (hD5 : ‖P - T₂ - T₃ - T₄‖ ≤ 6 * s ^ 5) :
    ‖z * R + R * z + (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z)‖ ≤ 28 * s ^ 7 := by
  -- Algebraic identity: combined = z·(R+T₅) + (R+T₅)·z - P²_deg≥7,
  -- where P²_deg≥7 unfolds via D₅ = P-T₂-T₃-T₄.
  have heq : z * R + R * z + (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) =
      z * (R + T₅) + (R + T₅) * z -
      (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
        (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 +
        T₃ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₃ +
        T₄ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₄ +
        (P - T₂ - T₃ - T₄) ^ 2) := by
    noncomm_ring
  rw [heq]
  -- z·(R+T₅) and (R+T₅)·z bounds (each ≤ 6·s⁷).
  have h_zRT5 : ‖z * (R + T₅)‖ ≤ s * (6 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hz hRT5 (norm_nonneg _) hs_nn)
  have h_RT5z : ‖(R + T₅) * z‖ ≤ (6 * s ^ 6) * s :=
    (norm_mul_le _ _).trans (mul_le_mul hRT5 hz (norm_nonneg _) (by positivity))
  -- 10 components of P²_deg≥7
  have h_T3T4 : ‖T₃ * T₄‖ ≤ s ^ 3 * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hT₄ (norm_nonneg _) (by positivity))
  have h_T4T3 : ‖T₄ * T₃‖ ≤ s ^ 4 * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hT₃ (norm_nonneg _) (by positivity))
  have h_T2D5 : ‖T₂ * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 2 * (6 * s ^ 5) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₂ hD5 (norm_nonneg _) (by positivity))
  have h_D5T2 : ‖(P - T₂ - T₃ - T₄) * T₂‖ ≤ (6 * s ^ 5) * s ^ 2 :=
    (norm_mul_le _ _).trans (mul_le_mul hD5 hT₂ (norm_nonneg _) (by positivity))
  have h_T4_2 : ‖T₄ ^ 2‖ ≤ s ^ 4 * s ^ 4 :=
    calc _ ≤ ‖T₄‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₄ 2
      _ = s ^ 4 * s ^ 4 := by ring
  have h_T3D5 : ‖T₃ * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 3 * (6 * s ^ 5) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hD5 (norm_nonneg _) (by positivity))
  have h_D5T3 : ‖(P - T₂ - T₃ - T₄) * T₃‖ ≤ (6 * s ^ 5) * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hD5 hT₃ (norm_nonneg _) (by positivity))
  have h_T4D5 : ‖T₄ * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 4 * (6 * s ^ 5) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hD5 (norm_nonneg _) (by positivity))
  have h_D5T4 : ‖(P - T₂ - T₃ - T₄) * T₄‖ ≤ (6 * s ^ 5) * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hD5 hT₄ (norm_nonneg _) (by positivity))
  have h_D5_2 : ‖(P - T₂ - T₃ - T₄) ^ 2‖ ≤ (6 * s ^ 5) ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄‖ ^ 2 := norm_pow_le _ _
      _ ≤ (6 * s ^ 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD5 2
  -- Triangle inequality: ‖A - B‖ ≤ ‖A‖ + ‖B‖.
  have h_main := norm_sub_le (z * (R + T₅) + (R + T₅) * z)
    (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 +
     T₃ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₃ +
     T₄ * (P - T₂ - T₃ - T₄) + (P - T₂ - T₃ - T₄) * T₄ + (P - T₂ - T₃ - T₄) ^ 2)
  -- A = z·(R+T₅) + (R+T₅)·z ≤ 12·s⁷
  have hA := norm_add_le (z * (R + T₅)) ((R + T₅) * z)
  -- B = sum of 10 terms ≤ ~16·s⁷ for s ≤ 1/10
  have hB1 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₃ + T₄ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₄) ((P - T₂ - T₃ - T₄) ^ 2)
  have hB2 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₃ + T₄ * (P - T₂ - T₃ - T₄))
    ((P - T₂ - T₃ - T₄) * T₄)
  have hB3 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₃) (T₄ * (P - T₂ - T₃ - T₄))
  have hB4 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2 + T₃ * (P - T₂ - T₃ - T₄))
    ((P - T₂ - T₃ - T₄) * T₃)
  have hB5 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂ + T₄ ^ 2) (T₃ * (P - T₂ - T₃ - T₄))
  have hB6 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄) +
    (P - T₂ - T₃ - T₄) * T₂) (T₄ ^ 2)
  have hB7 := norm_add_le (T₃ * T₄ + T₄ * T₃ + T₂ * (P - T₂ - T₃ - T₄))
    ((P - T₂ - T₃ - T₄) * T₂)
  have hB8 := norm_add_le (T₃ * T₄ + T₄ * T₃) (T₂ * (P - T₂ - T₃ - T₄))
  have hB9 := norm_add_le (T₃ * T₄) (T₄ * T₃)
  -- s⁸ ≤ s⁷/10, s⁹ ≤ s⁷/100, s¹⁰ ≤ s⁷/1000
  have hs8 : s ^ 8 ≤ s ^ 7 / 10 := by
    have h_eq : s ^ 8 = s ^ 7 * s := by ring
    rw [h_eq]; nlinarith [pow_nonneg hs_nn 7]
  have hs9 : s ^ 9 ≤ s ^ 7 / 100 := by
    have h_eq : s ^ 9 = s ^ 7 * (s * s) := by ring
    rw [h_eq]
    have hs2 : s * s ≤ 1 / 100 := by nlinarith
    nlinarith [pow_nonneg hs_nn 7]
  have hs10 : s ^ 10 ≤ s ^ 7 / 1000 := by
    have h_eq : s ^ 10 = s ^ 7 * (s * s * s) := by ring
    rw [h_eq]
    have hs3 : s * s * s ≤ 1 / 1000 := by nlinarith
    nlinarith [pow_nonneg hs_nn 7, mul_nonneg hs_nn hs_nn,
      mul_nonneg (mul_nonneg hs_nn hs_nn) hs_nn]
  -- Combined sum:
  -- A: 6·s⁷ + 6·s⁷ = 12·s⁷
  -- B: s⁷ + s⁷ + 6·s⁷ + 6·s⁷ + s⁸ + 6·s⁸ + 6·s⁸ + 6·s⁹ + 6·s⁹ + 36·s¹⁰
  --   = 14·s⁷ + 13·s⁸ + 12·s⁹ + 36·s¹⁰
  --   ≤ 14·s⁷ + 1.3·s⁷ + 0.12·s⁷ + 0.036·s⁷ ≈ 15.5·s⁷ for s ≤ 1/10
  -- Total: ≤ 27.5 → 28·s⁷
  nlinarith [pow_nonneg hs_nn 7]

set_option maxHeartbeats 4000000 in
/-- **Combined tricky bound (octic)** for the I1 octic residual.
The sum of the four "tricky" pieces `(z·R+R·z) + T22 + T_extra + T_extra2`
where
  - T22 = T₂² - P² + T₂T₃ + T₃T₂
  - T_extra = z·T₅ + T₂T₄ + T₃² + T₄T₂ + T₅z
  - T_extra2 = z·T₆ + T₂T₅ + T₃T₄ + T₄T₃ + T₅T₂ + T₆z
Individually, each piece is deg-6 or deg-7, NOT deg-8 — but the SUM is deg-8+ via:
- `R + T₅ + T₆` is deg-7+ (`R_plus_T5_plus_T6_eq_neg_deg7_residual`): combining
  z·R+R·z with z·T₅+T₅z and z·T₆+T₆z gives z·(R+T₅+T₆) + (R+T₅+T₆)·z,
  which is deg-8+ via `‖R+T₅+T₆‖ ≤ 7·s⁷`.
- Algebraic identity
  `P² = T₂² + (T₂T₃+T₃T₂) + (T₂T₄+T₃²+T₄T₂) + (T₂T₅+T₃T₄+T₄T₃+T₅T₂) + P²_deg≥8`:
  the deg-≤7 contributions of T22 + T_extra + T_extra2 cancel with the deg-≤7
  of P², leaving -P²_deg≥8 (15 terms) which is deg-8+ via D₆ := P-T₂-T₃-T₄-T₅.

Bound: ‖combined‖ ≤ 14·s⁸ (z·(R+T₅+T₆) part) + ~17·s⁸ (P²_deg≥8) ≤ 35·s⁸
for `s ≤ 1/10`. Analog of `norm_combined_tricky_le` at one degree higher. -/
theorem norm_combined_tricky_octic_le (z P R T₂ T₃ T₄ T₅ T₆ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hz : ‖z‖ ≤ s) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3)
    (hT₄ : ‖T₄‖ ≤ s ^ 4) (hT₅ : ‖T₅‖ ≤ s ^ 5)
    (hRT5T6 : ‖R + T₅ + T₆‖ ≤ 7 * s ^ 7)
    (hD6 : ‖P - T₂ - T₃ - T₄ - T₅‖ ≤ 6 * s ^ 6) :
    ‖z * R + R * z + (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) +
      (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z)‖ ≤ 35 * s ^ 8 := by
  -- Algebraic identity: combined = z·(R+T₅+T₆) + (R+T₅+T₆)·z - P²_deg≥8,
  -- where P²_deg≥8 unfolds via D₆ = P-T₂-T₃-T₄-T₅ (15 terms).
  have heq : z * R + R * z + (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) +
      (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z) =
      z * (R + T₅ + T₆) + (R + T₅ + T₆) * z -
      (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
        T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
        T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
        T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
        T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄ +
        T₅ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₅ +
        (P - T₂ - T₃ - T₄ - T₅) ^ 2) := by
    noncomm_ring
  rw [heq]
  -- z·(R+T₅+T₆) and (R+T₅+T₆)·z bounds (each ≤ 7·s⁸).
  have h_zRT5T6 : ‖z * (R + T₅ + T₆)‖ ≤ s * (7 * s ^ 7) :=
    (norm_mul_le _ _).trans (mul_le_mul hz hRT5T6 (norm_nonneg _) hs_nn)
  have h_RT5T6z : ‖(R + T₅ + T₆) * z‖ ≤ (7 * s ^ 7) * s :=
    (norm_mul_le _ _).trans (mul_le_mul hRT5T6 hz (norm_nonneg _) (by positivity))
  -- 15 components of P²_deg≥8
  have h_T3T5 : ‖T₃ * T₅‖ ≤ s ^ 3 * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hT₅ (norm_nonneg _) (by positivity))
  have h_T5T3 : ‖T₅ * T₃‖ ≤ s ^ 5 * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hT₃ (norm_nonneg _) (by positivity))
  have h_T4_2 : ‖T₄ ^ 2‖ ≤ s ^ 4 * s ^ 4 :=
    calc _ ≤ ‖T₄‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₄ 2
      _ = s ^ 4 * s ^ 4 := by ring
  have h_T4T5 : ‖T₄ * T₅‖ ≤ s ^ 4 * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hT₅ (norm_nonneg _) (by positivity))
  have h_T5T4 : ‖T₅ * T₄‖ ≤ s ^ 5 * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hT₄ (norm_nonneg _) (by positivity))
  have h_T5_2 : ‖T₅ ^ 2‖ ≤ s ^ 5 * s ^ 5 :=
    calc _ ≤ ‖T₅‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₅ 2
      _ = s ^ 5 * s ^ 5 := by ring
  have h_T2D6 : ‖T₂ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 2 * (6 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₂ hD6 (norm_nonneg _) (by positivity))
  have h_D6T2 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₂‖ ≤ (6 * s ^ 6) * s ^ 2 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₂ (norm_nonneg _) (by positivity))
  have h_T3D6 : ‖T₃ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 3 * (6 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hD6 (norm_nonneg _) (by positivity))
  have h_D6T3 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₃‖ ≤ (6 * s ^ 6) * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₃ (norm_nonneg _) (by positivity))
  have h_T4D6 : ‖T₄ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 4 * (6 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hD6 (norm_nonneg _) (by positivity))
  have h_D6T4 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₄‖ ≤ (6 * s ^ 6) * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₄ (norm_nonneg _) (by positivity))
  have h_T5D6 : ‖T₅ * (P - T₂ - T₃ - T₄ - T₅)‖ ≤ s ^ 5 * (6 * s ^ 6) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hD6 (norm_nonneg _) (by positivity))
  have h_D6T5 : ‖(P - T₂ - T₃ - T₄ - T₅) * T₅‖ ≤ (6 * s ^ 6) * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hD6 hT₅ (norm_nonneg _) (by positivity))
  have h_D6_2 : ‖(P - T₂ - T₃ - T₄ - T₅) ^ 2‖ ≤ (6 * s ^ 6) ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄ - T₅‖ ^ 2 := norm_pow_le _ _
      _ ≤ (6 * s ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD6 2
  -- Triangle inequality: ‖A - B‖ ≤ ‖A‖ + ‖B‖.
  have h_main := norm_sub_le (z * (R + T₅ + T₆) + (R + T₅ + T₆) * z)
    (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
     T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
     T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
     T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
     T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄ +
     T₅ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₅ +
     (P - T₂ - T₃ - T₄ - T₅) ^ 2)
  -- A = z·(R+T₅+T₆) + (R+T₅+T₆)·z ≤ 14·s⁸
  have hA := norm_add_le (z * (R + T₅ + T₆)) ((R + T₅ + T₆) * z)
  -- B = sum of 15 deg-8+ terms (each successively bounded via norm_add_le)
  have hB1 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₅)
    ((P - T₂ - T₃ - T₄ - T₅) ^ 2)
  have hB2 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅))
    ((P - T₂ - T₃ - T₄ - T₅) * T₅)
  have hB3 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₄)
    (T₅ * (P - T₂ - T₃ - T₄ - T₅))
  have hB4 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅))
    ((P - T₂ - T₃ - T₄ - T₅) * T₄)
  have hB5 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₃)
    (T₄ * (P - T₂ - T₃ - T₄ - T₅))
  have hB6 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅))
    ((P - T₂ - T₃ - T₄ - T₅) * T₃)
  have hB7 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅) + (P - T₂ - T₃ - T₄ - T₅) * T₂)
    (T₃ * (P - T₂ - T₃ - T₄ - T₅))
  have hB8 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅))
    ((P - T₂ - T₃ - T₄ - T₅) * T₂)
  have hB9 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄ + T₅ ^ 2) (T₂ * (P - T₂ - T₃ - T₄ - T₅))
  have hB10 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 +
    T₄ * T₅ + T₅ * T₄) (T₅ ^ 2)
  have hB11 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2 + T₄ * T₅) (T₅ * T₄)
  have hB12 := norm_add_le (T₃ * T₅ + T₅ * T₃ + T₄ ^ 2) (T₄ * T₅)
  have hB13 := norm_add_le (T₃ * T₅ + T₅ * T₃) (T₄ ^ 2)
  have hB14 := norm_add_le (T₃ * T₅) (T₅ * T₃)
  -- s⁹ ≤ s⁸/10, s¹⁰ ≤ s⁸/100, s¹¹ ≤ s⁸/1000, s¹² ≤ s⁸/10000
  have hs9 : s ^ 9 ≤ s ^ 8 / 10 := by
    have h_eq : s ^ 9 = s ^ 8 * s := by ring
    rw [h_eq]; nlinarith [pow_nonneg hs_nn 8]
  have hs10 : s ^ 10 ≤ s ^ 8 / 100 := by
    have h_eq : s ^ 10 = s ^ 8 * (s * s) := by ring
    rw [h_eq]
    have hs2 : s * s ≤ 1 / 100 := by nlinarith
    nlinarith [pow_nonneg hs_nn 8]
  have hs11 : s ^ 11 ≤ s ^ 8 / 1000 := by
    have h_eq : s ^ 11 = s ^ 8 * (s * s * s) := by ring
    rw [h_eq]
    have hs3 : s * s * s ≤ 1 / 1000 := by nlinarith
    nlinarith [pow_nonneg hs_nn 8, mul_nonneg hs_nn hs_nn,
      mul_nonneg (mul_nonneg hs_nn hs_nn) hs_nn]
  have hs12 : s ^ 12 ≤ s ^ 8 / 10000 := by
    have h_eq : s ^ 12 = s ^ 8 * (s * s) * (s * s) := by ring
    rw [h_eq]
    have hs2 : s * s ≤ 1 / 100 := by nlinarith
    have hss_nn : 0 ≤ s * s := mul_nonneg hs_nn hs_nn
    have h_s8s2 : s ^ 8 * (s * s) ≤ s ^ 8 * (1 / 100) :=
      mul_le_mul_of_nonneg_left hs2 (pow_nonneg hs_nn 8)
    have h_s8s2_nn : 0 ≤ s ^ 8 * (s * s) := mul_nonneg (pow_nonneg hs_nn 8) hss_nn
    have h_full : s ^ 8 * (s * s) * (s * s) ≤ (s ^ 8 * (1 / 100)) * (1 / 100) := by
      apply mul_le_mul h_s8s2 hs2 hss_nn
      positivity
    linarith
  -- Combined sum:
  -- A: 7·s⁸ + 7·s⁸ = 14·s⁸
  -- B (deg-8): T₃T₅ + T₅T₃ + T₄² + T₂D₆ + D₆T₂ = s⁸ + s⁸ + s⁸ + 6s⁸ + 6s⁸ = 15·s⁸
  -- B (deg-9): T₄T₅ + T₅T₄ + T₃D₆ + D₆T₃ = s⁹ + s⁹ + 6s⁹ + 6s⁹ = 14·s⁹ ≤ 1.4·s⁸
  -- B (deg-10): T₅² + T₄D₆ + D₆T₄ = s¹⁰ + 6s¹⁰ + 6s¹⁰ = 13·s¹⁰ ≤ 0.13·s⁸
  -- B (deg-11): T₅D₆ + D₆T₅ = 6s¹¹ + 6s¹¹ = 12·s¹¹ ≤ 0.012·s⁸
  -- B (deg-12): D₆² = 36·s¹² ≤ 0.0036·s⁸
  -- Total: 14 + 15 + 1.4 + 0.13 + 0.012 + 0.0036 ≈ 30.55·s⁸ ≤ 35·s⁸
  nlinarith [pow_nonneg hs_nn 8]

set_option maxHeartbeats 16000000 in
/-- **Nonic combined tricky bound** (deg-9 analog of `norm_combined_tricky_octic_le`).

Bounds the combined cluster
`z·R + R·z + (T₂²-P²+T₂T₃+T₃T₂) + (z·T₅+T₂T₄+T₃²+T₄T₂+T₅z) +
 (z·T₆+T₂T₅+T₃T₄+T₄T₃+T₅T₂+T₆z) + (z·T₇+T₂T₆+T₃T₅+T₄²+T₅T₃+T₆T₂+T₇z)`
by `35·s⁹` for `s ≤ 1/10`.

Algebraic identity: combined = `z·(R+T₅+T₆+T₇) + (R+T₅+T₆+T₇)·z − P²_deg≥9`
where P²_deg≥9 unfolds via `D₇ := P - T₂ - T₃ - T₄ - T₅ - T₆` into 21 deg-9+
terms (10 T·T products with i+j ≥ 9, 10 T·D₇ products, D₇²).

Per-degree contributions to the residual sum:
- deg 9: 4·s⁹ (T₃T₆+T₆T₃+T₄T₅+T₅T₄) + 14·s⁹ (T₂·D₇+D₇·T₂ each ≤ 7·s⁹) = 18·s⁹
- deg 10: 3·s¹⁰ + 14·s¹⁰ = 17·s¹⁰ ≤ 1.7·s⁹
- deg 11: 2·s¹¹ + 14·s¹¹ = 16·s¹¹ ≤ 0.16·s⁹
- deg 12: 1·s¹² + 14·s¹² = 15·s¹² ≤ 0.015·s⁹
- deg 13: 14·s¹³ ≤ 0.0014·s⁹
- deg 14: 49·s¹⁴ ≤ 0.00049·s⁹
- Total residual ≈ 19.88·s⁹

Plus z·(R+T₅+T₆+T₇) + (R+T₅+T₆+T₇)·z ≤ 14·s⁹. Grand total ≈ 33.88·s⁹ ≤ 35·s⁹.

Forward-looking infrastructure for the eventual deg-9-parent T2-F7e-octic
discharge (analog of the session-31 octic version at one degree higher). -/
private theorem norm_combined_tricky_nonic_le (z P R T₂ T₃ T₄ T₅ T₆ T₇ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_small : s ≤ 1 / 10)
    (hz : ‖z‖ ≤ s) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hT₃ : ‖T₃‖ ≤ s ^ 3)
    (hT₄ : ‖T₄‖ ≤ s ^ 4) (hT₅ : ‖T₅‖ ≤ s ^ 5) (hT₆ : ‖T₆‖ ≤ s ^ 6)
    (hRT5T6T7 : ‖R + T₅ + T₆ + T₇‖ ≤ 7 * s ^ 8)
    (hD7 : ‖P - T₂ - T₃ - T₄ - T₅ - T₆‖ ≤ 7 * s ^ 7) :
    ‖z * R + R * z + (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) +
      (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z) +
      (z * T₇ + T₂ * T₆ + T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₆ * T₂ + T₇ * z)‖ ≤ 35 * s ^ 9 := by
  -- Algebraic identity: combined = z·(R+T₅+T₆+T₇) + (R+T₅+T₆+T₇)·z - P²_deg≥9,
  -- where P²_deg≥9 unfolds via D₇ = P-T₂-T₃-T₄-T₅-T₆ (21 terms).
  have heq : z * R + R * z + (T₂ ^ 2 - P ^ 2 + T₂ * T₃ + T₃ * T₂) +
      (z * T₅ + T₂ * T₄ + T₃ * T₃ + T₄ * T₂ + T₅ * z) +
      (z * T₆ + T₂ * T₅ + T₃ * T₄ + T₄ * T₃ + T₅ * T₂ + T₆ * z) +
      (z * T₇ + T₂ * T₆ + T₃ * T₅ + T₄ ^ 2 + T₅ * T₃ + T₆ * T₂ + T₇ * z) =
      z * (R + T₅ + T₆ + T₇) + (R + T₅ + T₆ + T₇) * z -
      (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
        T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
        T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
        T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
        T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
        T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄ +
        T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₅ +
        T₆ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₆ +
        (P - T₂ - T₃ - T₄ - T₅ - T₆) ^ 2) := by
    noncomm_ring
  rw [heq]
  -- z·(R+T₅+T₆+T₇) and (R+T₅+T₆+T₇)·z bounds (each ≤ 7·s⁹).
  have h_zRT5T6T7 : ‖z * (R + T₅ + T₆ + T₇)‖ ≤ s * (7 * s ^ 8) :=
    (norm_mul_le _ _).trans (mul_le_mul hz hRT5T6T7 (norm_nonneg _) hs_nn)
  have h_RT5T6T7z : ‖(R + T₅ + T₆ + T₇) * z‖ ≤ (7 * s ^ 8) * s :=
    (norm_mul_le _ _).trans (mul_le_mul hRT5T6T7 hz (norm_nonneg _) (by positivity))
  -- 21 components of P²_deg≥9
  -- T_i*T_j products (i,j ≤ 6, i+j ≥ 9)
  have h_T3T6 : ‖T₃ * T₆‖ ≤ s ^ 3 * s ^ 6 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hT₆ (norm_nonneg _) (by positivity))
  have h_T6T3 : ‖T₆ * T₃‖ ≤ s ^ 6 * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₆ hT₃ (norm_nonneg _) (by positivity))
  have h_T4T5 : ‖T₄ * T₅‖ ≤ s ^ 4 * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hT₅ (norm_nonneg _) (by positivity))
  have h_T5T4 : ‖T₅ * T₄‖ ≤ s ^ 5 * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hT₄ (norm_nonneg _) (by positivity))
  have h_T4T6 : ‖T₄ * T₆‖ ≤ s ^ 4 * s ^ 6 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hT₆ (norm_nonneg _) (by positivity))
  have h_T6T4 : ‖T₆ * T₄‖ ≤ s ^ 6 * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₆ hT₄ (norm_nonneg _) (by positivity))
  have h_T5_2 : ‖T₅ ^ 2‖ ≤ s ^ 5 * s ^ 5 :=
    calc _ ≤ ‖T₅‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₅ 2
      _ = s ^ 5 * s ^ 5 := by ring
  have h_T5T6 : ‖T₅ * T₆‖ ≤ s ^ 5 * s ^ 6 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hT₆ (norm_nonneg _) (by positivity))
  have h_T6T5 : ‖T₆ * T₅‖ ≤ s ^ 6 * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hT₆ hT₅ (norm_nonneg _) (by positivity))
  have h_T6_2 : ‖T₆ ^ 2‖ ≤ s ^ 6 * s ^ 6 :=
    calc _ ≤ ‖T₆‖ ^ 2 := norm_pow_le _ _
      _ ≤ (s ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT₆ 2
      _ = s ^ 6 * s ^ 6 := by ring
  -- T_i*D₇ and D₇*T_i products (D₇ = P-T₂-T₃-T₄-T₅-T₆, ‖D₇‖ ≤ 7·s⁷)
  have h_T2D7 : ‖T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆)‖ ≤ s ^ 2 * (7 * s ^ 7) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₂ hD7 (norm_nonneg _) (by positivity))
  have h_D7T2 : ‖(P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂‖ ≤ (7 * s ^ 7) * s ^ 2 :=
    (norm_mul_le _ _).trans (mul_le_mul hD7 hT₂ (norm_nonneg _) (by positivity))
  have h_T3D7 : ‖T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆)‖ ≤ s ^ 3 * (7 * s ^ 7) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₃ hD7 (norm_nonneg _) (by positivity))
  have h_D7T3 : ‖(P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃‖ ≤ (7 * s ^ 7) * s ^ 3 :=
    (norm_mul_le _ _).trans (mul_le_mul hD7 hT₃ (norm_nonneg _) (by positivity))
  have h_T4D7 : ‖T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆)‖ ≤ s ^ 4 * (7 * s ^ 7) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₄ hD7 (norm_nonneg _) (by positivity))
  have h_D7T4 : ‖(P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄‖ ≤ (7 * s ^ 7) * s ^ 4 :=
    (norm_mul_le _ _).trans (mul_le_mul hD7 hT₄ (norm_nonneg _) (by positivity))
  have h_T5D7 : ‖T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆)‖ ≤ s ^ 5 * (7 * s ^ 7) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₅ hD7 (norm_nonneg _) (by positivity))
  have h_D7T5 : ‖(P - T₂ - T₃ - T₄ - T₅ - T₆) * T₅‖ ≤ (7 * s ^ 7) * s ^ 5 :=
    (norm_mul_le _ _).trans (mul_le_mul hD7 hT₅ (norm_nonneg _) (by positivity))
  have h_T6D7 : ‖T₆ * (P - T₂ - T₃ - T₄ - T₅ - T₆)‖ ≤ s ^ 6 * (7 * s ^ 7) :=
    (norm_mul_le _ _).trans (mul_le_mul hT₆ hD7 (norm_nonneg _) (by positivity))
  have h_D7T6 : ‖(P - T₂ - T₃ - T₄ - T₅ - T₆) * T₆‖ ≤ (7 * s ^ 7) * s ^ 6 :=
    (norm_mul_le _ _).trans (mul_le_mul hD7 hT₆ (norm_nonneg _) (by positivity))
  have h_D7_2 : ‖(P - T₂ - T₃ - T₄ - T₅ - T₆) ^ 2‖ ≤ (7 * s ^ 7) ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄ - T₅ - T₆‖ ^ 2 := norm_pow_le _ _
      _ ≤ (7 * s ^ 7) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD7 2
  -- Triangle inequality: ‖A - B‖ ≤ ‖A‖ + ‖B‖.
  have h_main := norm_sub_le (z * (R + T₅ + T₆ + T₇) + (R + T₅ + T₆ + T₇) * z)
    (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
      T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
      T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
      T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
      T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
      T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄ +
      T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₅ +
      T₆ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₆ +
      (P - T₂ - T₃ - T₄ - T₅ - T₆) ^ 2)
  -- A = z·(R+T₅+T₆+T₇) + (R+T₅+T₆+T₇)·z
  have hA := norm_add_le (z * (R + T₅ + T₆ + T₇)) ((R + T₅ + T₆ + T₇) * z)
  -- B = sum of 21 deg-9+ terms
  -- Telescope via norm_add_le 20 times.
  have hB1 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₅ +
    T₆ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₆)
    ((P - T₂ - T₃ - T₄ - T₅ - T₆) ^ 2)
  have hB2 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₅ +
    T₆ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
    ((P - T₂ - T₃ - T₄ - T₅ - T₆) * T₆)
  have hB3 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₅)
    (T₆ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
  have hB4 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄ +
    T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
    ((P - T₂ - T₃ - T₄ - T₅ - T₆) * T₅)
  have hB5 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄)
    (T₅ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
  have hB6 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃ +
    T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
    ((P - T₂ - T₃ - T₄ - T₅ - T₆) * T₄)
  have hB7 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃)
    (T₄ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
  have hB8 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂ +
    T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
    ((P - T₂ - T₃ - T₄ - T₅ - T₆) * T₃)
  have hB9 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆) + (P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂)
    (T₃ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
  have hB10 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 +
    T₅ * T₆ + T₆ * T₅ + T₆ ^ 2 +
    T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
    ((P - T₂ - T₃ - T₄ - T₅ - T₆) * T₂)
  have hB11 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 + T₅ * T₆ + T₆ * T₅ + T₆ ^ 2)
    (T₂ * (P - T₂ - T₃ - T₄ - T₅ - T₆))
  have hB12 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 + T₅ * T₆ + T₆ * T₅) (T₆ ^ 2)
  have hB13 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2 + T₅ * T₆) (T₆ * T₅)
  have hB14 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄ + T₅ ^ 2) (T₅ * T₆)
  have hB15 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ +
    T₄ * T₆ + T₆ * T₄) (T₅ ^ 2)
  have hB16 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄ + T₄ * T₆)
    (T₆ * T₄)
  have hB17 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅ + T₅ * T₄) (T₄ * T₆)
  have hB18 := norm_add_le (T₃ * T₆ + T₆ * T₃ + T₄ * T₅) (T₅ * T₄)
  have hB19 := norm_add_le (T₃ * T₆ + T₆ * T₃) (T₄ * T₅)
  have hB20 := norm_add_le (T₃ * T₆) (T₆ * T₃)
  -- s^k ≤ s^9 / 10^(k-9) folding (uses s ≤ 1/10)
  have hs10 : s ^ 10 ≤ s ^ 9 / 10 := by
    have h_eq : s ^ 10 = s ^ 9 * s := by ring
    rw [h_eq]; nlinarith [pow_nonneg hs_nn 9]
  have hs11 : s ^ 11 ≤ s ^ 9 / 100 := by
    have h_eq : s ^ 11 = s ^ 9 * (s * s) := by ring
    rw [h_eq]
    have hs2 : s * s ≤ 1 / 100 := by nlinarith
    nlinarith [pow_nonneg hs_nn 9]
  have hs12 : s ^ 12 ≤ s ^ 9 / 1000 := by
    have h_eq : s ^ 12 = s ^ 9 * (s * s * s) := by ring
    rw [h_eq]
    have hs3 : s * s * s ≤ 1 / 1000 := by nlinarith
    nlinarith [pow_nonneg hs_nn 9, mul_nonneg hs_nn hs_nn,
      mul_nonneg (mul_nonneg hs_nn hs_nn) hs_nn]
  have hs13 : s ^ 13 ≤ s ^ 9 / 10000 := by
    have h_eq : s ^ 13 = s ^ 9 * (s * s) * (s * s) := by ring
    rw [h_eq]
    have hs2 : s * s ≤ 1 / 100 := by nlinarith
    have hss_nn : 0 ≤ s * s := mul_nonneg hs_nn hs_nn
    have h_s9s2 : s ^ 9 * (s * s) ≤ s ^ 9 * (1 / 100) :=
      mul_le_mul_of_nonneg_left hs2 (pow_nonneg hs_nn 9)
    have h_s9s2_nn : 0 ≤ s ^ 9 * (s * s) := mul_nonneg (pow_nonneg hs_nn 9) hss_nn
    have h_full : s ^ 9 * (s * s) * (s * s) ≤ (s ^ 9 * (1 / 100)) * (1 / 100) := by
      apply mul_le_mul h_s9s2 hs2 hss_nn
      positivity
    linarith
  have hs14 : s ^ 14 ≤ s ^ 9 / 100000 := by
    have h_eq : s ^ 14 = s ^ 9 * (s * s) * (s * s) * s := by ring
    rw [h_eq]
    have hs2 : s * s ≤ 1 / 100 := by nlinarith
    have hss_nn : 0 ≤ s * s := mul_nonneg hs_nn hs_nn
    have h_s9s2 : s ^ 9 * (s * s) ≤ s ^ 9 * (1 / 100) :=
      mul_le_mul_of_nonneg_left hs2 (pow_nonneg hs_nn 9)
    have h_s9s2_nn : 0 ≤ s ^ 9 * (s * s) := mul_nonneg (pow_nonneg hs_nn 9) hss_nn
    have h_full : s ^ 9 * (s * s) * (s * s) ≤ (s ^ 9 * (1 / 100)) * (1 / 100) := by
      apply mul_le_mul h_s9s2 hs2 hss_nn
      positivity
    have h_full_nn : 0 ≤ s ^ 9 * (s * s) * (s * s) :=
      mul_nonneg h_s9s2_nn hss_nn
    have h_with_s : s ^ 9 * (s * s) * (s * s) * s ≤ (s ^ 9 * (1 / 100) * (1 / 100)) * (1 / 10) := by
      apply mul_le_mul h_full _ hs_nn _
      · linarith
      · positivity
    linarith
  -- Combined sum:
  -- A: 7·s⁹ + 7·s⁹ = 14·s⁹
  -- B (deg-9): 4·s⁹ + 14·s⁹ = 18·s⁹
  -- B (deg-10): 3·s¹⁰ + 14·s¹⁰ = 17·s¹⁰ ≤ 1.7·s⁹
  -- B (deg-11): 2·s¹¹ + 14·s¹¹ = 16·s¹¹ ≤ 0.16·s⁹
  -- B (deg-12): 1·s¹² + 14·s¹² = 15·s¹² ≤ 0.015·s⁹
  -- B (deg-13): 14·s¹³ ≤ 0.0014·s⁹
  -- B (deg-14): 49·s¹⁴ ≤ 0.00049·s⁹
  -- Total: 14 + 18 + 1.7 + 0.16 + 0.015 + 0.0014 + 0.0005 ≈ 33.88·s⁹ ≤ 35·s⁹
  nlinarith [pow_nonneg hs_nn 9]

/-- Norm bound for `‖P² - T₂²‖ ≤ 10·s⁵` via `P² - T₂² = (P-T₂)P + T₂(P-T₂)`. -/
theorem norm_P2_sub_T22_le (P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖P ^ 2 - T₂ ^ 2‖ ≤ 10 * s ^ 5 := by
  have heq : P ^ 2 - T₂ ^ 2 = (P - T₂) * P + T₂ * (P - T₂) := by noncomm_ring
  rw [heq]
  have ht1 : ‖(P - T₂) * P‖ ≤ (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖P - T₂‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (5 * s ^ 3) * s ^ 2 := mul_le_mul hPmT₂ hP (norm_nonneg _) (by positivity)
  have ht2 : ‖T₂ * (P - T₂)‖ ≤ s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ s ^ 2 * (5 * s ^ 3) := mul_le_mul hT₂ hPmT₂ (norm_nonneg _) (by positivity)
  have hadd := norm_add_le ((P - T₂) * P) (T₂ * (P - T₂))
  nlinarith [pow_nonneg hs_nn 5]

/-- Norm bound for `‖P³ - T₂³‖ ≤ 15·s⁷` via the 3-fold telescoping
`P³ - T₂³ = (P-T₂)·P² + T₂·(P-T₂)·P + T₂²·(P-T₂)`. Each term ≤ 5·s³·s⁴ = 5·s⁷
(or symmetric). Used in the I2 septic residual bound. -/
theorem norm_P3_sub_T23_le (P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2) (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖P ^ 3 - T₂ ^ 3‖ ≤ 15 * s ^ 7 := by
  have heq : P ^ 3 - T₂ ^ 3 =
      (P - T₂) * P ^ 2 + T₂ * (P - T₂) * P + T₂ ^ 2 * (P - T₂) := by noncomm_ring
  rw [heq]
  have ht1 : ‖(P - T₂) * P ^ 2‖ ≤ (5 * s ^ 3) * (s ^ 2) ^ 2 :=
    calc _ ≤ ‖P - T₂‖ * ‖P ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ * ‖P‖ ^ 2 := by gcongr; exact norm_pow_le P 2
      _ ≤ (5 * s ^ 3) * (s ^ 2) ^ 2 := mul_le_mul hPmT₂
          (pow_le_pow_left₀ (norm_nonneg _) hP 2) (by positivity) (by positivity)
  have ht2 : ‖T₂ * (P - T₂) * P‖ ≤ s ^ 2 * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖T₂ * (P - T₂)‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖P - T₂‖) * ‖P‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ hP (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hPmT₂ (norm_nonneg _) (by positivity)
  have ht3 : ‖T₂ ^ 2 * (P - T₂)‖ ≤ (s ^ 2) ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂ ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ‖T₂‖ ^ 2 * ‖P - T₂‖ := by gcongr; exact norm_pow_le T₂ 2
      _ ≤ (s ^ 2) ^ 2 * (5 * s ^ 3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hT₂ 2)
          hPmT₂ (norm_nonneg _) (by positivity)
  have hadd1 := norm_add_le ((P - T₂) * P ^ 2 + T₂ * (P - T₂) * P) (T₂ ^ 2 * (P - T₂))
  have hadd2 := norm_add_le ((P - T₂) * P ^ 2) (T₂ * (P - T₂) * P)
  nlinarith [pow_nonneg hs_nn 7]

set_option maxHeartbeats 4000000 in
/-- Norm bound for `y⁴ - z⁴ - y4_5 - y4_6`: each of the 16 terms in the
decomposition is deg-7+; total bound `≤ 85·s⁷`. Used in the small-s case
of the septic remainder (the `S₃'` piece of `pieceB_septic_decomp`,
analog of `norm_y4_sub_z4_sub_y4_5_le` at one degree higher).

Per-term bounds: 4 (P-T₂-T₃) terms ≤ 20·s⁷, 7 (y³-z³)P-deg-7 terms ≤ 34·s⁷,
4 (y²-z²)Pz-deg-7 terms ≤ 21·s⁷, 1 P²z²-deg-7 term ≤ 10·s⁷. -/
theorem norm_y4_sub_z4_sub_y4_5_sub_y4_6_le (y P T₂ T₃ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) -
      ((y - P) ^ 3 * T₃ + (y - P) ^ 2 * T₃ * (y - P) +
        (y - P) * T₃ * (y - P) ^ 2 + T₃ * (y - P) ^ 3 +
        (y - P) ^ 2 * T₂ ^ 2 + (y - P) * T₂ * (y - P) * T₂ +
        (y - P) * T₂ ^ 2 * (y - P) +
        T₂ * (y - P) ^ 2 * T₂ + T₂ * (y - P) * T₂ * (y - P) +
        T₂ ^ 2 * (y - P) ^ 2)‖ ≤ 85 * s ^ 7 := by
  rw [y4_sub_z4_sub_y4_5_sub_y4_6_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- Helper lemmas
  have hy2z2 := norm_pow2_sub_zpow2_le y P hs_nn hy hz hP
  have hP2T22 := norm_P2_sub_T22_le P T₂ hs_nn hP hT₂ hPmT₂
  -- A: 4 weight-1 (P-T₂-T₃) middle terms, each ≤ 5·s⁷
  have hA1 : ‖z ^ 3 * (P - T₂ - T₃)‖ ≤ s ^ 3 * (5 * s ^ 4) :=
    calc _ ≤ ‖z ^ 3‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 3 * ‖P - T₂ - T₃‖ := by gcongr; exact norm_pow_le z 3
      _ ≤ s ^ 3 * (5 * s ^ 4) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
          hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have hA2 : ‖z ^ 2 * (P - T₂ - T₃) * z‖ ≤ s ^ 2 * (5 * s ^ 4) * s :=
    calc _ ≤ ‖z ^ 2 * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂ - T₃‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ (s ^ 2 * (5 * s ^ 4)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  have hA3 : ‖z * (P - T₂ - T₃) * z ^ 2‖ ≤ s * (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖z * (P - T₂ - T₃)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (s * (5 * s ^ 4)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have hA4 : ‖(P - T₂ - T₃) * z ^ 3‖ ≤ (5 * s ^ 4) * s ^ 3 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ * ‖z‖ ^ 3 := by gcongr; exact norm_pow_le z 3
      _ ≤ (5 * s ^ 4) * s ^ 3 := mul_le_mul hPmT₂mT₃
          (pow_le_pow_left₀ (norm_nonneg _) hzn 3) (by positivity) (by positivity)
  -- B5: (y² - z²) · P² ≤ 3·s³ · (s²)² = 3·s⁷
  have hB5 : ‖(y ^ 2 - z ^ 2) * P ^ 2‖ ≤ (3 * s ^ 3) * (s ^ 2) ^ 2 :=
    calc _ ≤ ‖y ^ 2 - z ^ 2‖ * ‖P ^ 2‖ := norm_mul_le _ _
      _ ≤ (3 * s ^ 3) * ‖P‖ ^ 2 := by
          gcongr
          exact norm_pow_le P 2
      _ ≤ (3 * s ^ 3) * (s ^ 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (norm_nonneg _) hP 2
  -- B6: z² · (P² - T₂²) ≤ s² · 10·s⁵ = 10·s⁷
  have hB6 : ‖z ^ 2 * (P ^ 2 - T₂ ^ 2)‖ ≤ s ^ 2 * (10 * s ^ 5) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P ^ 2 - T₂ ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P ^ 2 - T₂ ^ 2‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (10 * s ^ 5) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
          hP2T22 (norm_nonneg _) (by positivity)
  -- B7: P² · z · P ≤ (s²)² · s · s² = s⁷
  have hB7 : ‖P ^ 2 * z * P‖ ≤ (s ^ 2) ^ 2 * s * s ^ 2 :=
    calc _ ≤ ‖P ^ 2 * z‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (‖P‖ ^ 2 * ‖z‖) * ‖P‖ := by
          gcongr
          calc _ ≤ ‖P ^ 2‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le P 2
      _ ≤ ((s ^ 2) ^ 2 * s) * s ^ 2 := by
          apply mul_le_mul _ hP (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hP 2) hzn
            (norm_nonneg _) (by positivity)
  -- B8: z · (P-T₂) · z · P ≤ s · 5·s³ · s · s² = 5·s⁷
  have hB8 : ‖z * (P - T₂) * z * P‖ ≤ s * (5 * s ^ 3) * s * s ^ 2 :=
    calc _ ≤ ‖z * (P - T₂) * z‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ * ‖P - T₂‖) * ‖z‖) * ‖P‖ := by
          gcongr
          calc _ ≤ ‖z * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (5 * s ^ 3) * s) * s ^ 2 := by
          apply mul_le_mul _ hP (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  -- B9: z · T₂ · z · (P-T₂) ≤ s · s² · s · 5·s³ = 5·s⁷
  have hB9 : ‖z * T₂ * z * (P - T₂)‖ ≤ s * s ^ 2 * s * (5 * s ^ 3) :=
    calc _ ≤ ‖z * T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ * ‖T₂‖) * ‖z‖) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖z * T₂‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * s ^ 2 * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity)
  -- B10: (P-T₂) · z² · P ≤ 5·s³ · s² · s² = 5·s⁷
  have hB10 : ‖(P - T₂) * z ^ 2 * P‖ ≤ (5 * s ^ 3) * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(P - T₂) * z ^ 2‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖ ^ 2) * ‖P‖ := by
          gcongr
          calc _ ≤ ‖P - T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ ((5 * s ^ 3) * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ hP (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
  -- B11: T₂ · z² · (P-T₂) ≤ s² · s² · 5·s³ = 5·s⁷
  have hB11 : ‖T₂ * z ^ 2 * (P - T₂)‖ ≤ s ^ 2 * s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂ * z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖ ^ 2) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ (s ^ 2 * s ^ 2) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
  -- C12: P³ · z ≤ (s²)³ · s = s⁷
  have hC12 : ‖P ^ 3 * z‖ ≤ (s ^ 2) ^ 3 * s :=
    calc _ ≤ ‖P ^ 3‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ‖P‖ ^ 3 * ‖z‖ := by gcongr; exact norm_pow_le P 3
      _ ≤ (s ^ 2) ^ 3 * s := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hP 3)
          hzn (norm_nonneg _) (by positivity)
  -- C13: z · (P² - T₂²) · z ≤ s · 10·s⁵ · s = 10·s⁷
  have hC13 : ‖z * (P ^ 2 - T₂ ^ 2) * z‖ ≤ s * (10 * s ^ 5) * s :=
    calc _ ≤ ‖z * (P ^ 2 - T₂ ^ 2)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P ^ 2 - T₂ ^ 2‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (10 * s ^ 5)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hP2T22 (norm_nonneg _) (by positivity)
  -- C14: (P-T₂) · z · P · z ≤ 5·s³ · s · s² · s = 5·s⁷
  have hC14 : ‖(P - T₂) * z * P * z‖ ≤ (5 * s ^ 3) * s * s ^ 2 * s :=
    calc _ ≤ ‖(P - T₂) * z * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ((‖P - T₂‖ * ‖z‖) * ‖P‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖(P - T₂) * z‖ * ‖P‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hP (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ hzn (norm_nonneg _) (by positivity)
  -- C15: T₂ · z · (P-T₂) · z ≤ s² · s · 5·s³ · s = 5·s⁷
  have hC15 : ‖T₂ * z * (P - T₂) * z‖ ≤ s ^ 2 * s * (5 * s ^ 3) * s :=
    calc _ ≤ ‖T₂ * z * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ((‖T₂‖ * ‖z‖) * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((s ^ 2 * s) * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hzn (norm_nonneg _) (by positivity)
  -- D16: (P² - T₂²) · z² ≤ 10·s⁵ · s² = 10·s⁷
  have hD16 : ‖(P ^ 2 - T₂ ^ 2) * z ^ 2‖ ≤ (10 * s ^ 5) * s ^ 2 :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P ^ 2 - T₂ ^ 2‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (10 * s ^ 5) * s ^ 2 := mul_le_mul hP2T22
          (pow_le_pow_left₀ (norm_nonneg _) hzn 2) (by positivity) (by positivity)
  -- Triangle inequality (15 norm_add_le applications, 16 terms)
  set t1 : 𝔸 := z ^ 3 * (P - T₂ - T₃)
  set t2 : 𝔸 := z ^ 2 * (P - T₂ - T₃) * z
  set t3 : 𝔸 := z * (P - T₂ - T₃) * z ^ 2
  set t4 : 𝔸 := (P - T₂ - T₃) * z ^ 3
  set t5 : 𝔸 := (y ^ 2 - z ^ 2) * P ^ 2
  set t6 : 𝔸 := z ^ 2 * (P ^ 2 - T₂ ^ 2)
  set t7 : 𝔸 := P ^ 2 * z * P
  set t8 : 𝔸 := z * (P - T₂) * z * P
  set t9 : 𝔸 := z * T₂ * z * (P - T₂)
  set t10 : 𝔸 := (P - T₂) * z ^ 2 * P
  set t11 : 𝔸 := T₂ * z ^ 2 * (P - T₂)
  set t12 : 𝔸 := P ^ 3 * z
  set t13 : 𝔸 := z * (P ^ 2 - T₂ ^ 2) * z
  set t14 : 𝔸 := (P - T₂) * z * P * z
  set t15 : 𝔸 := T₂ * z * (P - T₂) * z
  set t16 : 𝔸 := (P ^ 2 - T₂ ^ 2) * z ^ 2
  -- Cumulative sum bounds via repeated norm_add_le
  have ht_15 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15) t16
  have ht_14 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14) t15
  have ht_13 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13) t14
  have ht_12 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12) t13
  have ht_11 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11) t12
  have ht_10 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11
  have ht_9 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10
  have ht_8 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9
  have ht_7 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have ht_6 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7
  have ht_5 := norm_add_le (t1 + t2 + t3 + t4 + t5) t6
  have ht_4 := norm_add_le (t1 + t2 + t3 + t4) t5
  have ht_3 := norm_add_le (t1 + t2 + t3) t4
  have ht_2 := norm_add_le (t1 + t2) t3
  have ht_1 := norm_add_le t1 t2
  nlinarith [pow_nonneg hs_nn 7]

set_option maxHeartbeats 4000000 in
/-- Norm bound for `y⁴ - z⁴ - y4_5 - y4_6 - y4_7`: each of the 24 terms in the
decomposition is deg-8+; total bound `≤ 285·s⁸` (assuming `s ≤ 1`). Used as
the `S₃'` inner piece bound in the octic small-s discharge (analog of
`norm_y4_sub_z4_sub_y4_5_sub_y4_6_le` at one degree higher).

Each `y4_7` item is exactly the deg-7 leading of one of the 16 existing
septic-decomp terms; absorbing them yields 24 deg-8+ terms. The single term
`(P²-T₂²)·z·(P-T₂)` (B7-3) is natively `s⁹`, requiring `s ≤ 1` to coalesce. -/
theorem norm_y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_le (y P T₂ T₃ T₄ : 𝔸)
    {s : ℝ} (hs_nn : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4)
    (hPmT₂mT₃mT₄ : ‖P - T₂ - T₃ - T₄‖ ≤ 6 * s ^ 5)
    (hP2T22 : ‖P ^ 2 - T₂ ^ 2‖ ≤ 10 * s ^ 5)
    (hP2_etc : ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ ≤ 15 * s ^ 6)
    (hP3_T23 : ‖P ^ 3 - T₂ ^ 3‖ ≤ 15 * s ^ 7) :
    ‖y ^ 4 - (y - P) ^ 4 -
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) -
      ((y - P) ^ 3 * T₃ + (y - P) ^ 2 * T₃ * (y - P) +
        (y - P) * T₃ * (y - P) ^ 2 + T₃ * (y - P) ^ 3 +
        (y - P) ^ 2 * T₂ ^ 2 + (y - P) * T₂ * (y - P) * T₂ +
        (y - P) * T₂ ^ 2 * (y - P) +
        T₂ * (y - P) ^ 2 * T₂ + T₂ * (y - P) * T₂ * (y - P) +
        T₂ ^ 2 * (y - P) ^ 2) -
      ((y - P) * (y - P) * (y - P) * T₄ +
        (y - P) * (y - P) * T₂ * T₃ +
        (y - P) * (y - P) * T₃ * T₂ +
        (y - P) * (y - P) * T₄ * (y - P) +
        (y - P) * T₂ * (y - P) * T₃ +
        (y - P) * T₂ * T₂ * T₂ +
        (y - P) * T₂ * T₃ * (y - P) +
        (y - P) * T₃ * (y - P) * T₂ +
        (y - P) * T₃ * T₂ * (y - P) +
        (y - P) * T₄ * (y - P) * (y - P) +
        T₂ * (y - P) * (y - P) * T₃ +
        T₂ * (y - P) * T₂ * T₂ +
        T₂ * (y - P) * T₃ * (y - P) +
        T₂ * T₂ * (y - P) * T₂ +
        T₂ * T₂ * T₂ * (y - P) +
        T₂ * T₃ * (y - P) * (y - P) +
        T₃ * (y - P) * (y - P) * T₂ +
        T₃ * (y - P) * T₂ * (y - P) +
        T₃ * T₂ * (y - P) * (y - P) +
        T₄ * (y - P) * (y - P) * (y - P))‖ ≤ 285 * s ^ 8 := by
  rw [y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- Per-term bounds (24 terms).
  -- A1-A4: z^i · (P-T₂-T₃-T₄) · z^j with i+j=3, each ≤ 6·s⁸.
  have hA1 : ‖z ^ 3 * (P - T₂ - T₃ - T₄)‖ ≤ s ^ 3 * (6 * s ^ 5) :=
    calc _ ≤ ‖z ^ 3‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 3 * ‖P - T₂ - T₃ - T₄‖ := by gcongr; exact norm_pow_le z 3
      _ ≤ s ^ 3 * (6 * s ^ 5) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
          hPmT₂mT₃mT₄ (norm_nonneg _) (by positivity)
  have hA2 : ‖z ^ 2 * (P - T₂ - T₃ - T₄) * z‖ ≤ s ^ 2 * (6 * s ^ 5) * s :=
    calc _ ≤ ‖z ^ 2 * (P - T₂ - T₃ - T₄)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂ - T₃ - T₄‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃ - T₄‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ (s ^ 2 * (6 * s ^ 5)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂mT₃mT₄
            (norm_nonneg _) (by positivity)
  have hA3 : ‖z * (P - T₂ - T₃ - T₄) * z ^ 2‖ ≤ s * (6 * s ^ 5) * s ^ 2 :=
    calc _ ≤ ‖z * (P - T₂ - T₃ - T₄)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃ - T₄‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (s * (6 * s ^ 5)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂mT₃mT₄ (norm_nonneg _) (by positivity)
  have hA4 : ‖(P - T₂ - T₃ - T₄) * z ^ 3‖ ≤ (6 * s ^ 5) * s ^ 3 :=
    calc _ ≤ ‖P - T₂ - T₃ - T₄‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃ - T₄‖ * ‖z‖ ^ 3 := by gcongr; exact norm_pow_le z 3
      _ ≤ (6 * s ^ 5) * s ^ 3 := mul_le_mul hPmT₂mT₃mT₄
          (pow_le_pow_left₀ (norm_nonneg _) hzn 3) (by positivity) (by positivity)
  -- B5-1: z · (P³-T₂³) ≤ s · 15·s⁷ = 15·s⁸
  have hB5_1 : ‖z * (P ^ 3 - T₂ ^ 3)‖ ≤ s * (15 * s ^ 7) :=
    calc _ ≤ ‖z‖ * ‖P ^ 3 - T₂ ^ 3‖ := norm_mul_le _ _
      _ ≤ s * (15 * s ^ 7) := mul_le_mul hzn hP3_T23 (norm_nonneg _) (by positivity)
  -- B5-2: T₂ · z · (P²-T₂²) ≤ s² · s · 10·s⁵ = 10·s⁸
  have hB5_2 : ‖T₂ * z * (P ^ 2 - T₂ ^ 2)‖ ≤ s ^ 2 * s * (10 * s ^ 5) :=
    calc _ ≤ ‖T₂ * z‖ * ‖P ^ 2 - T₂ ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖) * ‖P ^ 2 - T₂ ^ 2‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * (10 * s ^ 5) := by
          apply mul_le_mul _ hP2T22 (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hzn (norm_nonneg _) (by positivity)
  -- B5-3: (P-T₂) · z · P² ≤ 5·s³ · s · s⁴ = 5·s⁸
  have hB5_3 : ‖(P - T₂) * z * P ^ 2‖ ≤ (5 * s ^ 3) * s * (s ^ 2) ^ 2 :=
    calc _ ≤ ‖(P - T₂) * z‖ * ‖P ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖) * ‖P‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le P 2
      _ ≤ ((5 * s ^ 3) * s) * (s ^ 2) ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hP 2)
            (by positivity) (by positivity)
          exact mul_le_mul hPmT₂ hzn (norm_nonneg _) (by positivity)
  -- B5-4: P⁴ ≤ (s²)⁴ = s⁸
  have hB5_4 : ‖P ^ 4‖ ≤ (s ^ 2) ^ 4 :=
    calc _ ≤ ‖P‖ ^ 4 := norm_pow_le P 4
      _ ≤ (s ^ 2) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hP 4
  -- B6: z² · (P²-T₂²-T₂T₃-T₃T₂) ≤ s² · 15·s⁶ = 15·s⁸
  have hB6 : ‖z ^ 2 * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂)‖ ≤ s ^ 2 * (15 * s ^ 6) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (15 * s ^ 6) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
          hP2_etc (norm_nonneg _) (by positivity)
  -- B7-1: T₂² · z · (P-T₂) ≤ (s²)² · s · 5·s³ = 5·s⁸
  have hB7_1 : ‖T₂ ^ 2 * z * (P - T₂)‖ ≤ (s ^ 2) ^ 2 * s * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂ ^ 2 * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ ^ 2 * ‖z‖) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖T₂ ^ 2‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le T₂ 2
      _ ≤ ((s ^ 2) ^ 2 * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hT₂ 2) hzn
            (norm_nonneg _) (by positivity)
  -- B7-2: (P²-T₂²) · z · T₂ ≤ 10·s⁵ · s · s² = 10·s⁸
  have hB7_2 : ‖(P ^ 2 - T₂ ^ 2) * z * T₂‖ ≤ (10 * s ^ 5) * s * s ^ 2 :=
    calc _ ≤ ‖(P ^ 2 - T₂ ^ 2) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P ^ 2 - T₂ ^ 2‖ * ‖z‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((10 * s ^ 5) * s) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hP2T22 hzn (norm_nonneg _) (by positivity)
  -- B7-3: (P²-T₂²) · z · (P-T₂) ≤ 10·s⁵ · s · 5·s³ = 50·s⁹ ≤ 50·s⁸ (via s ≤ 1)
  have hB7_3 : ‖(P ^ 2 - T₂ ^ 2) * z * (P - T₂)‖ ≤ (10 * s ^ 5) * s * (5 * s ^ 3) :=
    calc _ ≤ ‖(P ^ 2 - T₂ ^ 2) * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖P ^ 2 - T₂ ^ 2‖ * ‖z‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((10 * s ^ 5) * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hP2T22 hzn (norm_nonneg _) (by positivity)
  -- B8-1: z · (P-T₂-T₃) · z · T₂ ≤ s · 5·s⁴ · s · s² = 5·s⁸
  have hB8_1 : ‖z * (P - T₂ - T₃) * z * T₂‖ ≤ s * (5 * s ^ 4) * s * s ^ 2 :=
    calc _ ≤ ‖z * (P - T₂ - T₃) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ * ‖P - T₂ - T₃‖) * ‖z‖) * ‖T₂‖ := by
          gcongr
          calc _ ≤ ‖z * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((s * (5 * s ^ 4)) * s) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hPmT₂mT₃ (norm_nonneg _) (by positivity)
  -- B8-2: z · (P-T₂) · z · (P-T₂) ≤ s · 5·s³ · s · 5·s³ = 25·s⁸
  have hB8_2 : ‖z * (P - T₂) * z * (P - T₂)‖ ≤ s * (5 * s ^ 3) * s * (5 * s ^ 3) :=
    calc _ ≤ ‖z * (P - T₂) * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ * ‖P - T₂‖) * ‖z‖) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖z * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((s * (5 * s ^ 3)) * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  -- B9: z · T₂ · z · (P-T₂-T₃) ≤ s · s² · s · 5·s⁴ = 5·s⁸
  have hB9 : ‖z * T₂ * z * (P - T₂ - T₃)‖ ≤ s * s ^ 2 * s * (5 * s ^ 4) :=
    calc _ ≤ ‖z * T₂ * z‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ * ‖T₂‖) * ‖z‖) * ‖P - T₂ - T₃‖ := by
          gcongr
          calc _ ≤ ‖z * T₂‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((s * s ^ 2) * s) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity)
  -- B10-1: (P-T₂-T₃) · z² · T₂ ≤ 5·s⁴ · s² · s² = 5·s⁸
  have hB10_1 : ‖(P - T₂ - T₃) * z ^ 2 * T₂‖ ≤ (5 * s ^ 4) * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(P - T₂ - T₃) * z ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂ - T₃‖ * ‖z‖ ^ 2) * ‖T₂‖ := by
          gcongr
          calc _ ≤ ‖P - T₂ - T₃‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ ((5 * s ^ 4) * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
  -- B10-2: (P-T₂) · z² · (P-T₂) ≤ 5·s³ · s² · 5·s³ = 25·s⁸
  have hB10_2 : ‖(P - T₂) * z ^ 2 * (P - T₂)‖ ≤ (5 * s ^ 3) * s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖(P - T₂) * z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖ ^ 2) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖P - T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ ((5 * s ^ 3) * s ^ 2) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
  -- B11: T₂ · z² · (P-T₂-T₃) ≤ s² · s² · 5·s⁴ = 5·s⁸
  have hB11 : ‖T₂ * z ^ 2 * (P - T₂ - T₃)‖ ≤ s ^ 2 * s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖T₂ * z ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖ ^ 2) * ‖P - T₂ - T₃‖ := by
          gcongr
          calc _ ≤ ‖T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ (s ^ 2 * s ^ 2) * (5 * s ^ 4) := by
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
  -- B12: (P³-T₂³) · z ≤ 15·s⁷ · s = 15·s⁸
  have hB12 : ‖(P ^ 3 - T₂ ^ 3) * z‖ ≤ (15 * s ^ 7) * s :=
    calc _ ≤ ‖P ^ 3 - T₂ ^ 3‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (15 * s ^ 7) * s := mul_le_mul hP3_T23 hzn (norm_nonneg _) (by positivity)
  -- B13: z · (P²-T₂²-T₂T₃-T₃T₂) · z ≤ s · 15·s⁶ · s = 15·s⁸
  have hB13 : ‖z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z‖ ≤ s * (15 * s ^ 6) * s :=
    calc _ ≤ ‖z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖) * ‖z‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ (s * (15 * s ^ 6)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hP2_etc (norm_nonneg _) (by positivity)
  -- B14-1: (P-T₂-T₃) · z · T₂ · z ≤ 5·s⁴ · s · s² · s = 5·s⁸
  have hB14_1 : ‖(P - T₂ - T₃) * z * T₂ * z‖ ≤ (5 * s ^ 4) * s * s ^ 2 * s :=
    calc _ ≤ ‖(P - T₂ - T₃) * z * T₂‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ((‖P - T₂ - T₃‖ * ‖z‖) * ‖T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖(P - T₂ - T₃) * z‖ * ‖T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 4) * s * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂mT₃ hzn (norm_nonneg _) (by positivity)
  -- B14-2: (P-T₂) · z · (P-T₂) · z ≤ 5·s³ · s · 5·s³ · s = 25·s⁸
  have hB14_2 : ‖(P - T₂) * z * (P - T₂) * z‖ ≤ (5 * s ^ 3) * s * (5 * s ^ 3) * s :=
    calc _ ≤ ‖(P - T₂) * z * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ((‖P - T₂‖ * ‖z‖) * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖(P - T₂) * z‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hPmT₂ hzn (norm_nonneg _) (by positivity)
  -- B15: T₂ · z · (P-T₂-T₃) · z ≤ s² · s · 5·s⁴ · s = 5·s⁸
  have hB15 : ‖T₂ * z * (P - T₂ - T₃) * z‖ ≤ s ^ 2 * s * (5 * s ^ 4) * s :=
    calc _ ≤ ‖T₂ * z * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ((‖T₂‖ * ‖z‖) * ‖P - T₂ - T₃‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖T₂ * z‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((s ^ 2 * s) * (5 * s ^ 4)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hPmT₂mT₃ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hzn (norm_nonneg _) (by positivity)
  -- B16: (P²-T₂²-T₂T₃-T₃T₂) · z² ≤ 15·s⁶ · s² = 15·s⁸
  have hB16 : ‖(P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z ^ 2‖ ≤ (15 * s ^ 6) * s ^ 2 :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (15 * s ^ 6) * s ^ 2 := mul_le_mul hP2_etc
          (pow_le_pow_left₀ (norm_nonneg _) hzn 2) (by positivity) (by positivity)
  -- Triangle inequality (23 norm_add_le applications, 24 terms).
  set t1 : 𝔸 := z ^ 3 * (P - T₂ - T₃ - T₄)
  set t2 : 𝔸 := z ^ 2 * (P - T₂ - T₃ - T₄) * z
  set t3 : 𝔸 := z * (P - T₂ - T₃ - T₄) * z ^ 2
  set t4 : 𝔸 := (P - T₂ - T₃ - T₄) * z ^ 3
  set t5 : 𝔸 := z * (P ^ 3 - T₂ ^ 3)
  set t6 : 𝔸 := T₂ * z * (P ^ 2 - T₂ ^ 2)
  set t7 : 𝔸 := (P - T₂) * z * P ^ 2
  set t8 : 𝔸 := P ^ 4
  set t9 : 𝔸 := z ^ 2 * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂)
  set t10 : 𝔸 := T₂ ^ 2 * z * (P - T₂)
  set t11 : 𝔸 := (P ^ 2 - T₂ ^ 2) * z * T₂
  set t12 : 𝔸 := (P ^ 2 - T₂ ^ 2) * z * (P - T₂)
  set t13 : 𝔸 := z * (P - T₂ - T₃) * z * T₂
  set t14 : 𝔸 := z * (P - T₂) * z * (P - T₂)
  set t15 : 𝔸 := z * T₂ * z * (P - T₂ - T₃)
  set t16 : 𝔸 := (P - T₂ - T₃) * z ^ 2 * T₂
  set t17 : 𝔸 := (P - T₂) * z ^ 2 * (P - T₂)
  set t18 : 𝔸 := T₂ * z ^ 2 * (P - T₂ - T₃)
  set t19 : 𝔸 := (P ^ 3 - T₂ ^ 3) * z
  set t20 : 𝔸 := z * (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z
  set t21 : 𝔸 := (P - T₂ - T₃) * z * T₂ * z
  set t22 : 𝔸 := (P - T₂) * z * (P - T₂) * z
  set t23 : 𝔸 := T₂ * z * (P - T₂ - T₃) * z
  set t24 : 𝔸 := (P ^ 2 - T₂ ^ 2 - T₂ * T₃ - T₃ * T₂) * z ^ 2
  -- Cumulative sum bounds via repeated norm_add_le (23 of them).
  have ht_23 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22 + t23) t24
  have ht_22 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21 + t22) t23
  have ht_21 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20 + t21) t22
  have ht_20 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19 + t20) t21
  have ht_19 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18 + t19) t20
  have ht_18 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16 + t17 + t18) t19
  have ht_17 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16 + t17) t18
  have ht_16 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15 + t16) t17
  have ht_15 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14 + t15) t16
  have ht_14 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13 + t14) t15
  have ht_13 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12 + t13) t14
  have ht_12 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11 + t12) t13
  have ht_11 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10
    + t11) t12
  have ht_10 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11
  have ht_9 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10
  have ht_8 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9
  have ht_7 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have ht_6 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7
  have ht_5 := norm_add_le (t1 + t2 + t3 + t4 + t5) t6
  have ht_4 := norm_add_le (t1 + t2 + t3 + t4) t5
  have ht_3 := norm_add_le (t1 + t2 + t3) t4
  have ht_2 := norm_add_le (t1 + t2) t3
  have ht_1 := norm_add_le t1 t2
  -- Coalesce s⁹ → s⁸ via s ≤ 1.
  have hs8_nn : 0 ≤ s ^ 8 := pow_nonneg hs_nn 8
  nlinarith [pow_nonneg hs_nn 8, pow_nonneg hs_nn 7, pow_nonneg hs_nn 6,
    pow_nonneg hs_nn 5, pow_nonneg hs_nn 4, pow_nonneg hs_nn 3,
    pow_nonneg hs_nn 2, hs_le_one, sq_nonneg s]

/-- Norm bound `‖y² - z² - y2_3‖ ≤ 11·s⁴` where `z = y - P`,
`y2_3 = z·T₂ + T₂·z`. Used in the y5 octic norm bound for the
`(y²-z²-y2_3)·P·z²` compound term. -/
private theorem norm_y2_sub_z2_sub_y2_3_le (y P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖y ^ 2 - (y - P) ^ 2 - ((y - P) * T₂ + T₂ * (y - P))‖ ≤ 11 * s ^ 4 := by
  -- y² - z² - y2_3 = z·(P-T₂) + (P-T₂)·z + P²
  have heq : y ^ 2 - (y - P) ^ 2 - ((y - P) * T₂ + T₂ * (y - P)) =
      (y - P) * (P - T₂) + (P - T₂) * (y - P) + P ^ 2 := by noncomm_ring
  rw [heq]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have h1 : ‖z * (P - T₂)‖ ≤ s * (5 * s ^ 3) :=
    calc _ ≤ ‖z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ s * (5 * s ^ 3) := mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  have h2 : ‖(P - T₂) * z‖ ≤ (5 * s ^ 3) * s :=
    calc _ ≤ ‖P - T₂‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (5 * s ^ 3) * s := mul_le_mul hPmT₂ hzn (norm_nonneg _) (by positivity)
  have h3 : ‖P ^ 2‖ ≤ (s ^ 2) ^ 2 :=
    calc _ ≤ ‖P‖ ^ 2 := norm_pow_le P 2
      _ ≤ (s ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP 2
  have ht1 := norm_add_le (z * (P - T₂) + (P - T₂) * z) (P ^ 2)
  have ht2 := norm_add_le (z * (P - T₂)) ((P - T₂) * z)
  nlinarith [pow_nonneg hs_nn 4]

/-- Norm bound `‖y³ - z³ - y3_4‖ ≤ 19·s⁵` where `z = y - P`,
`y3_4 = z²·T₂ + z·T₂·z + T₂·z²`, for `s ≤ 1`. Used in the y5 octic
norm bound for the `(y³-z³-y3_4)·P·z` compound term. -/
private theorem norm_y3_sub_z3_sub_y3_4_le (y P T₂ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_le_one : s ≤ 1)
    (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) :
    ‖y ^ 3 - (y - P) ^ 3 -
      ((y - P) ^ 2 * T₂ + (y - P) * T₂ * (y - P) + T₂ * (y - P) ^ 2)‖ ≤ 19 * s ^ 5 := by
  -- y³ - z³ - y3_4 = (P-T₂)·z² + z²·(P-T₂) + z·(P-T₂)·z + P·z·P + P²·z + P³ + z·P²
  have heq : y ^ 3 - (y - P) ^ 3 -
      ((y - P) ^ 2 * T₂ + (y - P) * T₂ * (y - P) + T₂ * (y - P) ^ 2) =
      (P - T₂) * (y - P) ^ 2 + (y - P) ^ 2 * (P - T₂) +
        (y - P) * (P - T₂) * (y - P) +
        P * (y - P) * P + P ^ 2 * (y - P) + P ^ 3 + (y - P) * P ^ 2 := by noncomm_ring
  rw [heq]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have h1 : ‖(P - T₂) * z ^ 2‖ ≤ (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖P - T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (5 * s ^ 3) * s ^ 2 := mul_le_mul hPmT₂
          (pow_le_pow_left₀ (norm_nonneg _) hzn 2) (by positivity) (by positivity)
  have h2 : ‖z ^ 2 * (P - T₂)‖ ≤ s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P - T₂‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (5 * s ^ 3) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
          hPmT₂ (norm_nonneg _) (by positivity)
  have h3 : ‖z * (P - T₂) * z‖ ≤ s * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hPmT₂ (norm_nonneg _) (by positivity)
  have h4 : ‖P * z * P‖ ≤ s ^ 2 * s * s ^ 2 :=
    calc _ ≤ ‖P * z‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (‖P‖ * ‖z‖) * ‖P‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * s ^ 2 := by
          apply mul_le_mul _ hP (norm_nonneg _) (by positivity)
          exact mul_le_mul hP hzn (norm_nonneg _) (by positivity)
  have h5 : ‖P ^ 2 * z‖ ≤ (s ^ 2) ^ 2 * s :=
    calc _ ≤ ‖P ^ 2‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ‖P‖ ^ 2 * ‖z‖ := by gcongr; exact norm_pow_le P 2
      _ ≤ (s ^ 2) ^ 2 * s := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hP 2)
          hzn (norm_nonneg _) (by positivity)
  have h6 : ‖P ^ 3‖ ≤ (s ^ 2) ^ 3 :=
    calc _ ≤ ‖P‖ ^ 3 := norm_pow_le P 3
      _ ≤ (s ^ 2) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hP 3
  have h7 : ‖z * P ^ 2‖ ≤ s * (s ^ 2) ^ 2 :=
    calc _ ≤ ‖z‖ * ‖P ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖z‖ * ‖P‖ ^ 2 := by gcongr; exact norm_pow_le P 2
      _ ≤ s * (s ^ 2) ^ 2 := mul_le_mul hzn (pow_le_pow_left₀ (norm_nonneg _) hP 2)
          (by positivity) (by positivity)
  -- Triangle inequality (6 norm_add_le applications).
  have ht_6 := norm_add_le ((P - T₂) * z ^ 2 + z ^ 2 * (P - T₂) +
    z * (P - T₂) * z + P * z * P + P ^ 2 * z + P ^ 3) (z * P ^ 2)
  have ht_5 := norm_add_le ((P - T₂) * z ^ 2 + z ^ 2 * (P - T₂) +
    z * (P - T₂) * z + P * z * P + P ^ 2 * z) (P ^ 3)
  have ht_4 := norm_add_le ((P - T₂) * z ^ 2 + z ^ 2 * (P - T₂) +
    z * (P - T₂) * z + P * z * P) (P ^ 2 * z)
  have ht_3 := norm_add_le ((P - T₂) * z ^ 2 + z ^ 2 * (P - T₂) +
    z * (P - T₂) * z) (P * z * P)
  have ht_2 := norm_add_le ((P - T₂) * z ^ 2 + z ^ 2 * (P - T₂)) (z * (P - T₂) * z)
  have ht_1 := norm_add_le ((P - T₂) * z ^ 2) (z ^ 2 * (P - T₂))
  -- P³ has natural s⁶; use s ≤ 1 to bound by s⁵.
  nlinarith [pow_nonneg hs_nn 5, pow_nonneg hs_nn 4, pow_nonneg hs_nn 3,
    pow_nonneg hs_nn 6, hs_le_one]

set_option maxHeartbeats 16000000 in
/-- Algebraic decomposition of `y⁶ - z⁶ - y6_7 - y6_8` where `z = y - P`.

`y6_7` is the 6-term deg-7 leading contribution to `y⁶` (single T₂ in 6
positions among 5 z's), and `y6_8` is the 21-term deg-8 contribution:
6 (3,1,1,1,1,1) perms (single T₃) + 15 (2,2,1,1,1,1) perms (two T₂'s).

The RHS has 16 deg-9+ terms refined from the 11 octic-level terms:
* 4 (y^k − z^k)·P·z^(5−k) split (k=5,4,3,2) into compound + y_k_{k+1}·(P−T₂)
  pieces (8 terms total).
* k=1 split: P·P·z⁴ = T₂²·z⁴ + (P−T₂)·P·z⁴ + T₂·(P−T₂)·z⁴ — keep the latter 2.
* 6 z^j·(P−T₂)·z^(5−j) refined to z^j·(P−T₂−T₃)·z^(5−j) (single-T₃ extracted).

Deg-9 analog of `y6_sub_z6_sub_y6_7_decomp` at one degree higher. -/
private theorem y6_sub_z6_sub_y6_7_sub_y6_8_decomp (y P T₂ T₃ : 𝔸) :
    y ^ 6 - (y - P) ^ 6 -
      ((y - P) ^ 5 * T₂ + (y - P) ^ 4 * T₂ * (y - P) +
        (y - P) ^ 3 * T₂ * (y - P) ^ 2 + (y - P) ^ 2 * T₂ * (y - P) ^ 3 +
        (y - P) * T₂ * (y - P) ^ 4 + T₂ * (y - P) ^ 5) -
      ((y - P) ^ 5 * T₃ +
        (y - P) ^ 4 * T₂ * T₂ + (y - P) ^ 4 * T₃ * (y - P) +
        (y - P) ^ 3 * T₂ * (y - P) * T₂ + (y - P) ^ 3 * T₂ * T₂ * (y - P) +
        (y - P) ^ 3 * T₃ * (y - P) ^ 2 +
        (y - P) ^ 2 * T₂ * (y - P) ^ 2 * T₂ +
        (y - P) ^ 2 * T₂ * (y - P) * T₂ * (y - P) +
        (y - P) ^ 2 * T₂ * T₂ * (y - P) ^ 2 +
        (y - P) ^ 2 * T₃ * (y - P) ^ 3 +
        (y - P) * T₂ * (y - P) ^ 3 * T₂ +
        (y - P) * T₂ * (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) * T₂ * (y - P) ^ 2 +
        (y - P) * T₂ * T₂ * (y - P) ^ 3 +
        (y - P) * T₃ * (y - P) ^ 4 +
        T₂ * (y - P) ^ 4 * T₂ +
        T₂ * (y - P) ^ 3 * T₂ * (y - P) +
        T₂ * (y - P) ^ 2 * T₂ * (y - P) ^ 2 +
        T₂ * (y - P) * T₂ * (y - P) ^ 3 +
        T₂ * T₂ * (y - P) ^ 4 +
        T₃ * (y - P) ^ 5) =
      (y ^ 5 - (y - P) ^ 5 -
        ((y - P) ^ 4 * T₂ + (y - P) ^ 3 * T₂ * (y - P) +
          (y - P) ^ 2 * T₂ * (y - P) ^ 2 + (y - P) * T₂ * (y - P) ^ 3 +
          T₂ * (y - P) ^ 4)) * P +
      ((y - P) ^ 4 * T₂ + (y - P) ^ 3 * T₂ * (y - P) +
        (y - P) ^ 2 * T₂ * (y - P) ^ 2 + (y - P) * T₂ * (y - P) ^ 3 +
        T₂ * (y - P) ^ 4) * (P - T₂) +
      (y - P) ^ 5 * (P - T₂ - T₃) +
      (y ^ 4 - (y - P) ^ 4 -
        ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
          (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3)) * P * (y - P) +
      ((y - P) ^ 3 * T₂ + (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) ^ 2 + T₂ * (y - P) ^ 3) * (P - T₂) * (y - P) +
      (y - P) ^ 4 * (P - T₂ - T₃) * (y - P) +
      (y ^ 3 - (y - P) ^ 3 -
        ((y - P) ^ 2 * T₂ + (y - P) * T₂ * (y - P) + T₂ * (y - P) ^ 2)) *
          P * (y - P) ^ 2 +
      ((y - P) ^ 2 * T₂ + (y - P) * T₂ * (y - P) + T₂ * (y - P) ^ 2) *
          (P - T₂) * (y - P) ^ 2 +
      (y - P) ^ 3 * (P - T₂ - T₃) * (y - P) ^ 2 +
      (y ^ 2 - (y - P) ^ 2 - ((y - P) * T₂ + T₂ * (y - P))) * P * (y - P) ^ 3 +
      ((y - P) * T₂ + T₂ * (y - P)) * (P - T₂) * (y - P) ^ 3 +
      (y - P) ^ 2 * (P - T₂ - T₃) * (y - P) ^ 3 +
      (P - T₂) * P * (y - P) ^ 4 +
      T₂ * (P - T₂) * (y - P) ^ 4 +
      (y - P) * (P - T₂ - T₃) * (y - P) ^ 4 +
      (P - T₂ - T₃) * (y - P) ^ 5 := by
  noncomm_ring

set_option maxHeartbeats 16000000 in
/-- Norm bound for `y⁶ - z⁶ - y6_7 - y6_8`: 16 deg-9+ terms; total bound
`≤ 230·s⁹` (for `s ≤ 1`). Used as the `S₅''` inner piece bound in the
deg-9-parent T2-F7e-octic discharge (analog of `norm_y6_sub_z6_sub_y6_7_le`
at one degree higher).

Per-term bounds (units of s⁹):
* k=5 split: 51 + 25 = 76
* k=4 split: 31 + 20 = 51
* k=3 split: 19 + 15 = 34
* k=2 split: 11 + 10 = 21
* k=1 split: 5 + 5 = 10
* 6 single-T₃ refined `z^j·(P-T₂-T₃)·z^(5-j)`: 6·5 = 30
Total ≈ 222·s⁹ ≤ 230·s⁹. -/
private theorem norm_y6_sub_z6_sub_y6_7_sub_y6_8_le (y P T₂ T₃ : 𝔸)
    {s : ℝ} (hs_nn : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖y ^ 6 - (y - P) ^ 6 -
      ((y - P) ^ 5 * T₂ + (y - P) ^ 4 * T₂ * (y - P) +
        (y - P) ^ 3 * T₂ * (y - P) ^ 2 + (y - P) ^ 2 * T₂ * (y - P) ^ 3 +
        (y - P) * T₂ * (y - P) ^ 4 + T₂ * (y - P) ^ 5) -
      ((y - P) ^ 5 * T₃ +
        (y - P) ^ 4 * T₂ * T₂ + (y - P) ^ 4 * T₃ * (y - P) +
        (y - P) ^ 3 * T₂ * (y - P) * T₂ + (y - P) ^ 3 * T₂ * T₂ * (y - P) +
        (y - P) ^ 3 * T₃ * (y - P) ^ 2 +
        (y - P) ^ 2 * T₂ * (y - P) ^ 2 * T₂ +
        (y - P) ^ 2 * T₂ * (y - P) * T₂ * (y - P) +
        (y - P) ^ 2 * T₂ * T₂ * (y - P) ^ 2 +
        (y - P) ^ 2 * T₃ * (y - P) ^ 3 +
        (y - P) * T₂ * (y - P) ^ 3 * T₂ +
        (y - P) * T₂ * (y - P) ^ 2 * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) * T₂ * (y - P) ^ 2 +
        (y - P) * T₂ * T₂ * (y - P) ^ 3 +
        (y - P) * T₃ * (y - P) ^ 4 +
        T₂ * (y - P) ^ 4 * T₂ +
        T₂ * (y - P) ^ 3 * T₂ * (y - P) +
        T₂ * (y - P) ^ 2 * T₂ * (y - P) ^ 2 +
        T₂ * (y - P) * T₂ * (y - P) ^ 3 +
        T₂ * T₂ * (y - P) ^ 4 +
        T₃ * (y - P) ^ 5)‖ ≤ 230 * s ^ 9 := by
  rw [y6_sub_z6_sub_y6_7_sub_y6_8_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- Compound bounds from existing y_k-octic-level helpers.
  have hy5_656 := norm_y5_sub_z5_sub_y5_6_le y P T₂ hs_nn hy hz hP hPmT₂
  have hy4_545 := norm_y4_sub_z4_sub_y4_5_le y P T₂ hs_nn hy hz hP hPmT₂
  have hy3_343 := norm_y3_sub_z3_sub_y3_4_le y P T₂ hs_nn hs_le_one hz hP hPmT₂
  have hy2_323 := norm_y2_sub_z2_sub_y2_3_le y P T₂ hs_nn hz hP hPmT₂
  -- Bounds for the y_k_{k+1} polynomials (computed inline; ‖y_k_{k+1}‖ ≤ k·s^(k+1)).
  have h_y5_6 : ‖z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
      z * T₂ * z ^ 3 + T₂ * z ^ 4‖ ≤ 5 * s ^ 6 := by
    have e1 : ‖z ^ 4 * T₂‖ ≤ s ^ 4 * s ^ 2 :=
      calc _ ≤ ‖z ^ 4‖ * ‖T₂‖ := norm_mul_le _ _
        _ ≤ ‖z‖ ^ 4 * ‖T₂‖ := by gcongr; exact norm_pow_le z 4
        _ ≤ s ^ 4 * s ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 4) hT₂
              (norm_nonneg _) (by positivity)
    have e2 : ‖z ^ 3 * T₂ * z‖ ≤ s ^ 3 * s ^ 2 * s :=
      calc _ ≤ ‖z ^ 3 * T₂‖ * ‖z‖ := norm_mul_le _ _
        _ ≤ (‖z‖ ^ 3 * ‖T₂‖) * ‖z‖ := by
            gcongr
            calc _ ≤ ‖z ^ 3‖ * ‖T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 3
        _ ≤ (s ^ 3 * s ^ 2) * s :=
            mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
              hT₂ (norm_nonneg _) (by positivity)) hzn (norm_nonneg _) (by positivity)
    have e3 : ‖z ^ 2 * T₂ * z ^ 2‖ ≤ s ^ 2 * s ^ 2 * s ^ 2 :=
      calc _ ≤ ‖z ^ 2 * T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
        _ ≤ (‖z‖ ^ 2 * ‖T₂‖) * ‖z‖ ^ 2 := by
            gcongr
            · calc _ ≤ ‖z ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
                _ ≤ _ := by gcongr; exact norm_pow_le z 2
            · exact norm_pow_le z 2
        _ ≤ (s ^ 2 * s ^ 2) * s ^ 2 :=
            mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
              hT₂ (norm_nonneg _) (by positivity))
              (pow_le_pow_left₀ (norm_nonneg _) hzn 2) (by positivity) (by positivity)
    have e4 : ‖z * T₂ * z ^ 3‖ ≤ s * s ^ 2 * s ^ 3 :=
      calc _ ≤ ‖z * T₂‖ * ‖z ^ 3‖ := norm_mul_le _ _
        _ ≤ (‖z‖ * ‖T₂‖) * ‖z‖ ^ 3 := by
            gcongr
            · exact norm_mul_le _ _
            · exact norm_pow_le z 3
        _ ≤ (s * s ^ 2) * s ^ 3 :=
            mul_le_mul (mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity))
              (pow_le_pow_left₀ (norm_nonneg _) hzn 3) (by positivity) (by positivity)
    have e5 : ‖T₂ * z ^ 4‖ ≤ s ^ 2 * s ^ 4 :=
      calc _ ≤ ‖T₂‖ * ‖z ^ 4‖ := norm_mul_le _ _
        _ ≤ ‖T₂‖ * ‖z‖ ^ 4 := by gcongr; exact norm_pow_le z 4
        _ ≤ s ^ 2 * s ^ 4 :=
            mul_le_mul hT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
              (by positivity) (by positivity)
    have ha1 := norm_add_le (z ^ 4 * T₂ + z ^ 3 * T₂ * z +
      z ^ 2 * T₂ * z ^ 2 + z * T₂ * z ^ 3) (T₂ * z ^ 4)
    have ha2 := norm_add_le (z ^ 4 * T₂ + z ^ 3 * T₂ * z +
      z ^ 2 * T₂ * z ^ 2) (z * T₂ * z ^ 3)
    have ha3 := norm_add_le (z ^ 4 * T₂ + z ^ 3 * T₂ * z) (z ^ 2 * T₂ * z ^ 2)
    have ha4 := norm_add_le (z ^ 4 * T₂) (z ^ 3 * T₂ * z)
    nlinarith [pow_nonneg hs_nn 6]
  have h_y4_5 : ‖z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3‖ ≤
      4 * s ^ 5 := by
    have e1 : ‖z ^ 3 * T₂‖ ≤ s ^ 3 * s ^ 2 :=
      calc _ ≤ ‖z ^ 3‖ * ‖T₂‖ := norm_mul_le _ _
        _ ≤ ‖z‖ ^ 3 * ‖T₂‖ := by gcongr; exact norm_pow_le z 3
        _ ≤ s ^ 3 * s ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3) hT₂
              (norm_nonneg _) (by positivity)
    have e2 : ‖z ^ 2 * T₂ * z‖ ≤ s ^ 2 * s ^ 2 * s :=
      calc _ ≤ ‖z ^ 2 * T₂‖ * ‖z‖ := norm_mul_le _ _
        _ ≤ (‖z‖ ^ 2 * ‖T₂‖) * ‖z‖ := by
            gcongr
            calc _ ≤ ‖z ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 2
        _ ≤ (s ^ 2 * s ^ 2) * s :=
            mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
              hT₂ (norm_nonneg _) (by positivity)) hzn (norm_nonneg _) (by positivity)
    have e3 : ‖z * T₂ * z ^ 2‖ ≤ s * s ^ 2 * s ^ 2 :=
      calc _ ≤ ‖z * T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
        _ ≤ (‖z‖ * ‖T₂‖) * ‖z‖ ^ 2 := by
            gcongr
            · exact norm_mul_le _ _
            · exact norm_pow_le z 2
        _ ≤ (s * s ^ 2) * s ^ 2 :=
            mul_le_mul (mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity))
              (pow_le_pow_left₀ (norm_nonneg _) hzn 2) (by positivity) (by positivity)
    have e4 : ‖T₂ * z ^ 3‖ ≤ s ^ 2 * s ^ 3 :=
      calc _ ≤ ‖T₂‖ * ‖z ^ 3‖ := norm_mul_le _ _
        _ ≤ ‖T₂‖ * ‖z‖ ^ 3 := by gcongr; exact norm_pow_le z 3
        _ ≤ s ^ 2 * s ^ 3 :=
            mul_le_mul hT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
              (by positivity) (by positivity)
    have ha1 := norm_add_le (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2) (T₂ * z ^ 3)
    have ha2 := norm_add_le (z ^ 3 * T₂ + z ^ 2 * T₂ * z) (z * T₂ * z ^ 2)
    have ha3 := norm_add_le (z ^ 3 * T₂) (z ^ 2 * T₂ * z)
    nlinarith [pow_nonneg hs_nn 5]
  have h_y3_4 : ‖z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2‖ ≤ 3 * s ^ 4 := by
    have e1 : ‖z ^ 2 * T₂‖ ≤ s ^ 2 * s ^ 2 :=
      calc _ ≤ ‖z ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
        _ ≤ ‖z‖ ^ 2 * ‖T₂‖ := by gcongr; exact norm_pow_le z 2
        _ ≤ s ^ 2 * s ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hT₂
              (norm_nonneg _) (by positivity)
    have e2 : ‖z * T₂ * z‖ ≤ s * s ^ 2 * s :=
      calc _ ≤ ‖z * T₂‖ * ‖z‖ := norm_mul_le _ _
        _ ≤ (‖z‖ * ‖T₂‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ (s * s ^ 2) * s :=
            mul_le_mul (mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity))
              hzn (norm_nonneg _) (by positivity)
    have e3 : ‖T₂ * z ^ 2‖ ≤ s ^ 2 * s ^ 2 :=
      calc _ ≤ ‖T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
        _ ≤ ‖T₂‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
        _ ≤ s ^ 2 * s ^ 2 :=
            mul_le_mul hT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
              (by positivity) (by positivity)
    have ha1 := norm_add_le (z ^ 2 * T₂ + z * T₂ * z) (T₂ * z ^ 2)
    have ha2 := norm_add_le (z ^ 2 * T₂) (z * T₂ * z)
    nlinarith [pow_nonneg hs_nn 4]
  have h_y2_3 : ‖z * T₂ + T₂ * z‖ ≤ 2 * s ^ 3 := by
    have e1 : ‖z * T₂‖ ≤ s * s ^ 2 :=
      (norm_mul_le _ _).trans (mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity))
    have e2 : ‖T₂ * z‖ ≤ s ^ 2 * s :=
      (norm_mul_le _ _).trans (mul_le_mul hT₂ hzn (norm_nonneg _) (by positivity))
    have ha1 := norm_add_le (z * T₂) (T₂ * z)
    nlinarith [pow_nonneg hs_nn 3]
  -- Now bound each of the 16 RHS terms.
  -- Term 1: (y^5 - z^5 - y5_6) * P, ≤ 51·s⁷ · s² = 51·s⁹.
  have h_t1 : ‖(y ^ 5 - z ^ 5 -
      (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
       z * T₂ * z ^ 3 + T₂ * z ^ 4)) * P‖ ≤ 51 * s ^ 7 * s ^ 2 :=
    calc _ ≤ ‖y ^ 5 - z ^ 5 -
        (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
         z * T₂ * z ^ 3 + T₂ * z ^ 4)‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ 51 * s ^ 7 * s ^ 2 := mul_le_mul hy5_656 hP (norm_nonneg _) (by positivity)
  -- Term 2: y5_6 * (P - T₂), ≤ 5·s⁶ · 5·s³ = 25·s⁹.
  have h_t2 : ‖(z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
      z * T₂ * z ^ 3 + T₂ * z ^ 4) * (P - T₂)‖ ≤ (5 * s ^ 6) * (5 * s ^ 3) :=
    calc _ ≤ ‖z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
              z * T₂ * z ^ 3 + T₂ * z ^ 4‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (5 * s ^ 6) * (5 * s ^ 3) :=
          mul_le_mul h_y5_6 hPmT₂ (norm_nonneg _) (by positivity)
  -- Term 3: z^5 * (P - T₂ - T₃), ≤ s⁵ · 5·s⁴ = 5·s⁹.
  have h_t3 : ‖z ^ 5 * (P - T₂ - T₃)‖ ≤ s ^ 5 * (5 * s ^ 4) :=
    calc _ ≤ ‖z ^ 5‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 5 * ‖P - T₂ - T₃‖ := by gcongr; exact norm_pow_le z 5
      _ ≤ s ^ 5 * (5 * s ^ 4) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 5) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  -- Term 4: (y^4 - z^4 - y4_5) * P * z, ≤ 31·s⁶ · s² · s = 31·s⁹.
  have h_t4 : ‖(y ^ 4 - z ^ 4 -
      (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)) * P * z‖ ≤
      31 * s ^ 6 * s ^ 2 * s :=
    calc _ ≤ ‖(y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)) * P‖ * ‖z‖ :=
          norm_mul_le _ _
      _ ≤ (‖y ^ 4 - z ^ 4 -
          (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)‖ * ‖P‖) * ‖z‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ ((31 * s ^ 6) * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy4_545 hP (norm_nonneg _) (by positivity)
  -- Term 5: y4_5 * (P - T₂) * z, ≤ 4·s⁵ · 5·s³ · s = 20·s⁹.
  have h_t5 : ‖(z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) *
      (P - T₂) * z‖ ≤ (4 * s ^ 5) * (5 * s ^ 3) * s :=
    calc _ ≤ ‖(z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) *
        (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3‖ *
            ‖P - T₂‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((4 * s ^ 5) * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul h_y4_5 hPmT₂ (norm_nonneg _) (by positivity)
  -- Term 6: z^4 * (P - T₂ - T₃) * z, ≤ s⁴ · 5·s⁴ · s = 5·s⁹.
  have h_t6 : ‖z ^ 4 * (P - T₂ - T₃) * z‖ ≤ s ^ 4 * (5 * s ^ 4) * s :=
    calc _ ≤ ‖z ^ 4 * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 4 * ‖P - T₂ - T₃‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 4‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 4
      _ ≤ (s ^ 4 * (5 * s ^ 4)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 4) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  -- Term 7: (y^3 - z^3 - y3_4) * P * z^2, ≤ 19·s⁵ · s² · s² = 19·s⁹.
  have h_t7 : ‖(y ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)) * P * z ^ 2‖ ≤
      19 * s ^ 5 * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(y ^ 3 - z ^ 3 -
        (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)) * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 3 - z ^ 3 -
          (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ ((19 * s ^ 5) * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hy3_343 hP (norm_nonneg _) (by positivity)
  -- Term 8: y3_4 * (P - T₂) * z^2, ≤ 3·s⁴ · 5·s³ · s² = 15·s⁹.
  have h_t8 : ‖(z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) * (P - T₂) * z ^ 2‖ ≤
      (3 * s ^ 4) * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖(z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) * (P - T₂)‖ * ‖z ^ 2‖ :=
            norm_mul_le _ _
      _ ≤ (‖z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2‖ * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ ((3 * s ^ 4) * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul h_y3_4 hPmT₂ (norm_nonneg _) (by positivity)
  -- Term 9: z^3 * (P - T₂ - T₃) * z^2, ≤ s³ · 5·s⁴ · s² = 5·s⁹.
  have h_t9 : ‖z ^ 3 * (P - T₂ - T₃) * z ^ 2‖ ≤ s ^ 3 * (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖z ^ 3 * (P - T₂ - T₃)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 3 * ‖P - T₂ - T₃‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖z ^ 3‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 3
          · exact norm_pow_le z 2
      _ ≤ (s ^ 3 * (5 * s ^ 4)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  -- Term 10: (y^2 - z^2 - y2_3) * P * z^3, ≤ 11·s⁴ · s² · s³ = 11·s⁹.
  have h_t10 : ‖(y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)) * P * z ^ 3‖ ≤
      11 * s ^ 4 * s ^ 2 * s ^ 3 :=
    calc _ ≤ ‖(y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)) * P‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)‖ * ‖P‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ ((11 * s ^ 4) * s ^ 2) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hy2_323 hP (norm_nonneg _) (by positivity)
  -- Term 11: y2_3 * (P - T₂) * z^3, ≤ 2·s³ · 5·s³ · s³ = 10·s⁹.
  have h_t11 : ‖(z * T₂ + T₂ * z) * (P - T₂) * z ^ 3‖ ≤
      (2 * s ^ 3) * (5 * s ^ 3) * s ^ 3 :=
    calc _ ≤ ‖(z * T₂ + T₂ * z) * (P - T₂)‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖z * T₂ + T₂ * z‖ * ‖P - T₂‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ ((2 * s ^ 3) * (5 * s ^ 3)) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul h_y2_3 hPmT₂ (norm_nonneg _) (by positivity)
  -- Term 12: z^2 * (P - T₂ - T₃) * z^3, ≤ s² · 5·s⁴ · s³ = 5·s⁹.
  have h_t12 : ‖z ^ 2 * (P - T₂ - T₃) * z ^ 3‖ ≤ s ^ 2 * (5 * s ^ 4) * s ^ 3 :=
    calc _ ≤ ‖z ^ 2 * (P - T₂ - T₃)‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂ - T₃‖) * ‖z‖ ^ 3 := by
          gcongr
          · calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 2
          · exact norm_pow_le z 3
      _ ≤ (s ^ 2 * (5 * s ^ 4)) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  -- Term 13: (P - T₂) * P * z^4, ≤ 5·s³ · s² · s⁴ = 5·s⁹.
  have h_t13 : ‖(P - T₂) * P * z ^ 4‖ ≤ (5 * s ^ 3) * s ^ 2 * s ^ 4 :=
    calc _ ≤ ‖(P - T₂) * P‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖P‖) * ‖z‖ ^ 4 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 4
      _ ≤ ((5 * s ^ 3) * s ^ 2) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul hPmT₂ hP (norm_nonneg _) (by positivity)
  -- Term 14: T₂ * (P - T₂) * z^4, ≤ s² · 5·s³ · s⁴ = 5·s⁹.
  have h_t14 : ‖T₂ * (P - T₂) * z ^ 4‖ ≤ s ^ 2 * (5 * s ^ 3) * s ^ 4 :=
    calc _ ≤ ‖T₂ * (P - T₂)‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖P - T₂‖) * ‖z‖ ^ 4 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 4
      _ ≤ (s ^ 2 * (5 * s ^ 3)) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul hT₂ hPmT₂ (norm_nonneg _) (by positivity)
  -- Term 15: z * (P - T₂ - T₃) * z^4, ≤ s · 5·s⁴ · s⁴ = 5·s⁹.
  have h_t15 : ‖z * (P - T₂ - T₃) * z ^ 4‖ ≤ s * (5 * s ^ 4) * s ^ 4 :=
    calc _ ≤ ‖z * (P - T₂ - T₃)‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃‖) * ‖z‖ ^ 4 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 4
      _ ≤ (s * (5 * s ^ 4)) * s ^ 4 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂mT₃ (norm_nonneg _) (by positivity)
  -- Term 16: (P - T₂ - T₃) * z^5, ≤ 5·s⁴ · s⁵ = 5·s⁹.
  have h_t16 : ‖(P - T₂ - T₃) * z ^ 5‖ ≤ (5 * s ^ 4) * s ^ 5 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖z ^ 5‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ * ‖z‖ ^ 5 := by gcongr; exact norm_pow_le z 5
      _ ≤ (5 * s ^ 4) * s ^ 5 :=
          mul_le_mul hPmT₂mT₃ (pow_le_pow_left₀ (norm_nonneg _) hzn 5)
            (by positivity) (by positivity)
  -- 15 triangle inequalities for the 16-term sum.
  set t1 := (y ^ 5 - z ^ 5 -
    (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
     z * T₂ * z ^ 3 + T₂ * z ^ 4)) * P with ht1_def
  set t2 := (z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
    z * T₂ * z ^ 3 + T₂ * z ^ 4) * (P - T₂) with ht2_def
  set t3 := z ^ 5 * (P - T₂ - T₃) with ht3_def
  set t4 := (y ^ 4 - z ^ 4 -
    (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)) * P * z with ht4_def
  set t5 := (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3) *
    (P - T₂) * z with ht5_def
  set t6 := z ^ 4 * (P - T₂ - T₃) * z with ht6_def
  set t7 := (y ^ 3 - z ^ 3 -
    (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)) * P * z ^ 2 with ht7_def
  set t8 := (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) * (P - T₂) * z ^ 2 with ht8_def
  set t9 := z ^ 3 * (P - T₂ - T₃) * z ^ 2 with ht9_def
  set t10 := (y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)) * P * z ^ 3 with ht10_def
  set t11 := (z * T₂ + T₂ * z) * (P - T₂) * z ^ 3 with ht11_def
  set t12 := z ^ 2 * (P - T₂ - T₃) * z ^ 3 with ht12_def
  set t13 := (P - T₂) * P * z ^ 4 with ht13_def
  set t14 := T₂ * (P - T₂) * z ^ 4 with ht14_def
  set t15 := z * (P - T₂ - T₃) * z ^ 4 with ht15_def
  set t16 := (P - T₂ - T₃) * z ^ 5 with ht16_def
  have ha1 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 +
    t11 + t12 + t13 + t14 + t15) t16
  have ha2 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 +
    t11 + t12 + t13 + t14) t15
  have ha3 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 +
    t11 + t12 + t13) t14
  have ha4 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 +
    t11 + t12) t13
  have ha5 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11) t12
  have ha6 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11
  have ha7 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10
  have ha8 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9
  have ha9 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have ha10 := norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7
  have ha11 := norm_add_le (t1 + t2 + t3 + t4 + t5) t6
  have ha12 := norm_add_le (t1 + t2 + t3 + t4) t5
  have ha13 := norm_add_le (t1 + t2 + t3) t4
  have ha14 := norm_add_le (t1 + t2) t3
  have ha15 := norm_add_le t1 t2
  -- Sum: 51+25+5+31+20+5+19+15+5+11+10+5+5+5+5+5 = 222·s⁹ ≤ 230·s⁹.
  nlinarith [pow_nonneg hs_nn 9, hs_le_one]

/-- Norm bound `‖y² - z² - y2_3 - y2_4‖ ≤ 20·s⁵` where `z = y - P`,
`y2_3 = z·T₂ + T₂·z`, `y2_4 = z·T₃ + T₃·z + T₂²`.

Algebraic identity: `y² - z² - y2_3 - y2_4 = z·(P-T₂-T₃) + (P-T₂-T₃)·z + (P²-T₂²)`.

Forward-looking helper for the y5 nonic norm bound's `[F]` piece in the
deg-9-parent T2-F7e-octic discharge. Deg-5+ residual of `y²`. -/
private theorem norm_y2_sub_z2_sub_y2_3_sub_y2_4_le (y P T₂ T₃ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖y ^ 2 - (y - P) ^ 2 - ((y - P) * T₂ + T₂ * (y - P)) -
      ((y - P) * T₃ + T₃ * (y - P) + T₂ ^ 2)‖ ≤ 20 * s ^ 5 := by
  have heq : y ^ 2 - (y - P) ^ 2 - ((y - P) * T₂ + T₂ * (y - P)) -
      ((y - P) * T₃ + T₃ * (y - P) + T₂ ^ 2) =
      (y - P) * (P - T₂ - T₃) + (P - T₂ - T₃) * (y - P) + (P ^ 2 - T₂ ^ 2) := by
    noncomm_ring
  rw [heq]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have hP2T22 := norm_P2_sub_T22_le P T₂ hs_nn hP hT₂ hPmT₂
  have h1 : ‖z * (P - T₂ - T₃)‖ ≤ s * (5 * s ^ 4) :=
    (norm_mul_le _ _).trans (mul_le_mul hzn hPmT₂mT₃ (norm_nonneg _) (by positivity))
  have h2 : ‖(P - T₂ - T₃) * z‖ ≤ (5 * s ^ 4) * s :=
    (norm_mul_le _ _).trans (mul_le_mul hPmT₂mT₃ hzn (norm_nonneg _) (by positivity))
  have ht1 := norm_add_le (z * (P - T₂ - T₃) + (P - T₂ - T₃) * z) (P ^ 2 - T₂ ^ 2)
  have ht2 := norm_add_le (z * (P - T₂ - T₃)) ((P - T₂ - T₃) * z)
  -- Sum: 5·s⁵ + 5·s⁵ + 10·s⁵ = 20·s⁵.
  nlinarith [pow_nonneg hs_nn 5]

/-- Algebraic decomposition of `y³ - z³ - y3_4 - y3_5` where `z = y - P`.

`y3_4 = z²·T₂ + z·T₂·z + T₂·z²` (3 terms, deg-4 leading of y³).
`y3_5 = z²·T₃ + z·T₃·z + T₃·z² + z·T₂² + T₂·z·T₂ + T₂²·z` (6 terms, deg-5 leading).

Decomposes into 9 deg-6+ pieces:
* 3 weight-1 (P-T₂-T₃) middle terms.
* 3 from `P·z·P − T₂·z·T₂` refinement (each deg-6+).
* 2 `(P²-T₂²)·z` and `z·(P²-T₂²)` (deg-6+).
* 1 `P³` (deg-6 exactly). -/
private theorem y3_sub_z3_sub_y3_4_sub_y3_5_decomp (y P T₂ T₃ : 𝔸) :
    y ^ 3 - (y - P) ^ 3 -
      ((y - P) ^ 2 * T₂ + (y - P) * T₂ * (y - P) + T₂ * (y - P) ^ 2) -
      ((y - P) ^ 2 * T₃ + (y - P) * T₃ * (y - P) + T₃ * (y - P) ^ 2 +
        (y - P) * T₂ ^ 2 + T₂ * (y - P) * T₂ + T₂ ^ 2 * (y - P)) =
      (y - P) ^ 2 * (P - T₂ - T₃) + (y - P) * (P - T₂ - T₃) * (y - P) +
        (P - T₂ - T₃) * (y - P) ^ 2 +
      T₂ * (y - P) * (P - T₂) + (P - T₂) * (y - P) * T₂ +
        (P - T₂) * (y - P) * (P - T₂) +
      (P ^ 2 - T₂ ^ 2) * (y - P) + (y - P) * (P ^ 2 - T₂ ^ 2) +
      P ^ 3 := by
  noncomm_ring

/-- Norm bound `‖y³ - z³ - y3_4 - y3_5‖ ≤ 71·s⁶` for `s ≤ 1`. Forward-looking
helper for the y5 nonic norm bound's `[D]` piece.

Per-term breakdown (units of s⁶):
* 3 weight-1 (P-T₂-T₃) middle: 15·s⁶
* T₂·z·(P-T₂) + (P-T₂)·z·T₂ + (P-T₂)·z·(P-T₂): 5+5+25·s⁷ folded → 35·s⁶
* (P²-T₂²)·z + z·(P²-T₂²): 20·s⁶
* P³: 1·s⁶
Total: 71·s⁶. -/
private theorem norm_y3_sub_z3_sub_y3_4_sub_y3_5_le (y P T₂ T₃ : 𝔸) {s : ℝ}
    (hs_nn : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖y ^ 3 - (y - P) ^ 3 -
      ((y - P) ^ 2 * T₂ + (y - P) * T₂ * (y - P) + T₂ * (y - P) ^ 2) -
      ((y - P) ^ 2 * T₃ + (y - P) * T₃ * (y - P) + T₃ * (y - P) ^ 2 +
        (y - P) * T₂ ^ 2 + T₂ * (y - P) * T₂ + T₂ ^ 2 * (y - P))‖ ≤ 71 * s ^ 6 := by
  rw [y3_sub_z3_sub_y3_4_sub_y3_5_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  have hP2T22 := norm_P2_sub_T22_le P T₂ hs_nn hP hT₂ hPmT₂
  -- 3 weight-1 (P-T₂-T₃) middle terms, each ≤ 5·s⁶.
  have hA1 : ‖z ^ 2 * (P - T₂ - T₃)‖ ≤ s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P - T₂ - T₃‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (5 * s ^ 4) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  have hA2 : ‖z * (P - T₂ - T₃) * z‖ ≤ s * (5 * s ^ 4) * s :=
    calc _ ≤ ‖z * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (5 * s ^ 4)) * s :=
          mul_le_mul (mul_le_mul hzn hPmT₂mT₃ (norm_nonneg _) (by positivity))
            hzn (norm_nonneg _) (by positivity)
  have hA3 : ‖(P - T₂ - T₃) * z ^ 2‖ ≤ (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (5 * s ^ 4) * s ^ 2 :=
          mul_le_mul hPmT₂mT₃ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
  -- 3 P·z·P − T₂·z·T₂ refinement terms.
  have hB1 : ‖T₂ * z * (P - T₂)‖ ≤ s ^ 2 * s * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s ^ 2 * s) * (5 * s ^ 3) :=
          mul_le_mul (mul_le_mul hT₂ hzn (norm_nonneg _) (by positivity))
            hPmT₂ (norm_nonneg _) (by positivity)
  have hB2 : ‖(P - T₂) * z * T₂‖ ≤ (5 * s ^ 3) * s * s ^ 2 :=
    calc _ ≤ ‖(P - T₂) * z‖ * ‖T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖) * ‖T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s) * s ^ 2 :=
          mul_le_mul (mul_le_mul hPmT₂ hzn (norm_nonneg _) (by positivity))
            hT₂ (norm_nonneg _) (by positivity)
  have hB3 : ‖(P - T₂) * z * (P - T₂)‖ ≤ (5 * s ^ 3) * s * (5 * s ^ 3) :=
    calc _ ≤ ‖(P - T₂) * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖P - T₂‖ * ‖z‖) * ‖P - T₂‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((5 * s ^ 3) * s) * (5 * s ^ 3) :=
          mul_le_mul (mul_le_mul hPmT₂ hzn (norm_nonneg _) (by positivity))
            hPmT₂ (norm_nonneg _) (by positivity)
  -- 2 (P²-T₂²) terms.
  have hC1 : ‖(P ^ 2 - T₂ ^ 2) * z‖ ≤ (10 * s ^ 5) * s :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (10 * s ^ 5) * s := mul_le_mul hP2T22 hzn (norm_nonneg _) (by positivity)
  have hC2 : ‖z * (P ^ 2 - T₂ ^ 2)‖ ≤ s * (10 * s ^ 5) :=
    calc _ ≤ ‖z‖ * ‖P ^ 2 - T₂ ^ 2‖ := norm_mul_le _ _
      _ ≤ s * (10 * s ^ 5) := mul_le_mul hzn hP2T22 (norm_nonneg _) (by positivity)
  -- 1 P³ term.
  have hD1 : ‖P ^ 3‖ ≤ (s ^ 2) ^ 3 :=
    calc _ ≤ ‖P‖ ^ 3 := norm_pow_le P 3
      _ ≤ (s ^ 2) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hP 3
  -- 8 triangle inequalities for the 9-term sum.
  have ha1 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + T₂ * z * (P - T₂) + (P - T₂) * z * T₂ +
    (P - T₂) * z * (P - T₂) + (P ^ 2 - T₂ ^ 2) * z + z * (P ^ 2 - T₂ ^ 2)) (P ^ 3)
  have ha2 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + T₂ * z * (P - T₂) + (P - T₂) * z * T₂ +
    (P - T₂) * z * (P - T₂) + (P ^ 2 - T₂ ^ 2) * z) (z * (P ^ 2 - T₂ ^ 2))
  have ha3 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + T₂ * z * (P - T₂) + (P - T₂) * z * T₂ +
    (P - T₂) * z * (P - T₂)) ((P ^ 2 - T₂ ^ 2) * z)
  have ha4 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + T₂ * z * (P - T₂) + (P - T₂) * z * T₂)
    ((P - T₂) * z * (P - T₂))
  have ha5 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + T₂ * z * (P - T₂)) ((P - T₂) * z * T₂)
  have ha6 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2) (T₂ * z * (P - T₂))
  have ha7 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z)
    ((P - T₂ - T₃) * z ^ 2)
  have ha8 := norm_add_le (z ^ 2 * (P - T₂ - T₃)) (z * (P - T₂ - T₃) * z)
  -- Sum (s⁶ units): 15 + 5 + 5 + 25·s⁷→25·s⁶ + 20 + 1 = 71·s⁶.
  nlinarith [pow_nonneg hs_nn 6, pow_nonneg hs_nn 7, hs_le_one]

set_option maxHeartbeats 4000000 in
/-- Norm bound for `y⁵ - z⁵ - y5_6 - y5_7`: 18 deg-8+ terms; total bound
`≤ 141·s⁸` (for `s ≤ 1`). Used as the `S₄'` inner piece bound in the
octic small-s discharge (analog of `norm_y5_sub_z5_sub_y5_6_le` at one
degree higher).

The 18 terms split as:
- 5 weight-1 (P-T₂-T₃) middle terms: ≤ 25·s⁸
- 1 compound `(y⁴-z⁴-y4_5)·P` + 4 perms `z^i·T₂·z^j·(P-T₂)`: ≤ 31+20 = 51·s⁸
- 1 compound `(y³-z³-y3_4)·P·z` + 3 perms `z^i·T₂·z^j·(P-T₂)·z`: ≤ 19+15 = 34·s⁸
- 1 compound `(y²-z²-y2_3)·P·z²` + 2 perms `z^i·T₂·z^j·(P-T₂)·z²`: ≤ 11+10 = 21·s⁸
- 1 `(P²-T₂²)·z³`: ≤ 10·s⁸

Total = 25+51+34+21+10 = 141·s⁸. -/
theorem norm_y5_sub_z5_sub_y5_6_sub_y5_7_le (y P T₂ T₃ : 𝔸)
    {s : ℝ} (hs_nn : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hy : ‖y‖ ≤ 2 * s) (hz : ‖y - P‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2)
    (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3)
    (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4)
    (hP2T22 : ‖P ^ 2 - T₂ ^ 2‖ ≤ 10 * s ^ 5) :
    ‖y ^ 5 - (y - P) ^ 5 -
      ((y - P) ^ 4 * T₂ + (y - P) ^ 3 * T₂ * (y - P) +
        (y - P) ^ 2 * T₂ * (y - P) ^ 2 + (y - P) * T₂ * (y - P) ^ 3 +
        T₂ * (y - P) ^ 4) -
      ((y - P) * (y - P) * (y - P) * (y - P) * T₃ +
        (y - P) * (y - P) * (y - P) * T₃ * (y - P) +
        (y - P) * (y - P) * T₃ * (y - P) * (y - P) +
        (y - P) * T₃ * (y - P) * (y - P) * (y - P) +
        T₃ * (y - P) * (y - P) * (y - P) * (y - P) +
        (y - P) * (y - P) * (y - P) * T₂ * T₂ +
        (y - P) * (y - P) * T₂ * (y - P) * T₂ +
        (y - P) * (y - P) * T₂ * T₂ * (y - P) +
        (y - P) * T₂ * (y - P) * (y - P) * T₂ +
        (y - P) * T₂ * (y - P) * T₂ * (y - P) +
        (y - P) * T₂ * T₂ * (y - P) * (y - P) +
        T₂ * (y - P) * (y - P) * (y - P) * T₂ +
        T₂ * (y - P) * (y - P) * T₂ * (y - P) +
        T₂ * (y - P) * T₂ * (y - P) * (y - P) +
        T₂ * T₂ * (y - P) * (y - P) * (y - P))‖ ≤ 141 * s ^ 8 := by
  rw [y5_sub_z5_sub_y5_6_sub_y5_7_decomp]
  set z : 𝔸 := y - P with hz_def
  have hzn : ‖z‖ ≤ s := hz
  -- Helper bounds.
  have hy4_545 := norm_y4_sub_z4_sub_y4_5_le y P T₂ hs_nn hy hz hP hPmT₂
  have hy3_343 := norm_y3_sub_z3_sub_y3_4_le y P T₂ hs_nn hs_le_one hz hP hPmT₂
  have hy2_323 := norm_y2_sub_z2_sub_y2_3_le y P T₂ hs_nn hz hP hPmT₂
  -- Per-term bounds (18 terms).
  -- Group A: 5 (P-T₂-T₃) middle terms, each ≤ 5·s⁸.
  have hA1 : ‖z ^ 4 * (P - T₂ - T₃)‖ ≤ s ^ 4 * (5 * s ^ 4) :=
    calc _ ≤ ‖z ^ 4‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 4 * ‖P - T₂ - T₃‖ := by gcongr; exact norm_pow_le z 4
      _ ≤ s ^ 4 * (5 * s ^ 4) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 4)
          hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have hA2 : ‖z ^ 3 * (P - T₂ - T₃) * z‖ ≤ s ^ 3 * (5 * s ^ 4) * s :=
    calc _ ≤ ‖z ^ 3 * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 3 * ‖P - T₂ - T₃‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 3‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 3
      _ ≤ (s ^ 3 * (5 * s ^ 4)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  have hA3 : ‖z ^ 2 * (P - T₂ - T₃) * z ^ 2‖ ≤ s ^ 2 * (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖z ^ 2 * (P - T₂ - T₃)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 2 * ‖P - T₂ - T₃‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_pow_le z 2
          · exact norm_pow_le z 2
      _ ≤ (s ^ 2 * (5 * s ^ 4)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hPmT₂mT₃
            (norm_nonneg _) (by positivity)
  have hA4 : ‖z * (P - T₂ - T₃) * z ^ 3‖ ≤ s * (5 * s ^ 4) * s ^ 3 :=
    calc _ ≤ ‖z * (P - T₂ - T₃)‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃‖) * ‖z‖ ^ 3 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 3
      _ ≤ (s * (5 * s ^ 4)) * s ^ 3 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hPmT₂mT₃ (norm_nonneg _) (by positivity)
  have hA5 : ‖(P - T₂ - T₃) * z ^ 4‖ ≤ (5 * s ^ 4) * s ^ 4 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖z ^ 4‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ * ‖z‖ ^ 4 := by gcongr; exact norm_pow_le z 4
      _ ≤ (5 * s ^ 4) * s ^ 4 := mul_le_mul hPmT₂mT₃
          (pow_le_pow_left₀ (norm_nonneg _) hzn 4) (by positivity) (by positivity)
  -- Group B: (y⁴-z⁴-y4_5)·P + 4 perms y4_5·(P-T₂).
  have hB_compound : ‖(y ^ 4 - z ^ 4 -
      (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)) * P‖ ≤
      31 * s ^ 6 * s ^ 2 :=
    calc _ ≤ ‖y ^ 4 - z ^ 4 -
        (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)‖ * ‖P‖ :=
          norm_mul_le _ _
      _ ≤ 31 * s ^ 6 * s ^ 2 := mul_le_mul hy4_545 hP (norm_nonneg _) (by positivity)
  have hB1 : ‖z ^ 3 * T₂ * (P - T₂)‖ ≤ s ^ 3 * s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖z ^ 3 * T₂‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ 3 * ‖T₂‖) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖z ^ 3‖ * ‖T₂‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 3
      _ ≤ (s ^ 3 * s ^ 2) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 3) hT₂
            (norm_nonneg _) (by positivity)
  have hB2 : ‖z ^ 2 * T₂ * z * (P - T₂)‖ ≤ s ^ 2 * s ^ 2 * s * (5 * s ^ 3) :=
    calc _ ≤ ‖z ^ 2 * T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ ^ 2 * ‖T₂‖) * ‖z‖) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖z ^ 2 * T₂‖ * ‖z‖ := norm_mul_le _ _
            _ ≤ _ := by
                gcongr
                calc _ ≤ ‖z ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
                  _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ ((s ^ 2 * s ^ 2) * s) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hT₂
            (norm_nonneg _) (by positivity)
  have hB3 : ‖z * T₂ * z ^ 2 * (P - T₂)‖ ≤ s * s ^ 2 * s ^ 2 * (5 * s ^ 3) :=
    calc _ ≤ ‖z * T₂ * z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ * ‖T₂‖) * ‖z‖ ^ 2) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖z * T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
            _ ≤ _ := by
                gcongr
                · exact norm_mul_le _ _
                · exact norm_pow_le z 2
      _ ≤ ((s * s ^ 2) * s ^ 2) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity)
  have hB4 : ‖T₂ * z ^ 3 * (P - T₂)‖ ≤ s ^ 2 * s ^ 3 * (5 * s ^ 3) :=
    calc _ ≤ ‖T₂ * z ^ 3‖ * ‖P - T₂‖ := norm_mul_le _ _
      _ ≤ (‖T₂‖ * ‖z‖ ^ 3) * ‖P - T₂‖ := by
          gcongr
          calc _ ≤ ‖T₂‖ * ‖z ^ 3‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_pow_le z 3
      _ ≤ (s ^ 2 * s ^ 3) * (5 * s ^ 3) := by
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 3)
            (by positivity) (by positivity)
  -- Group C: (y³-z³-y3_4)·P·z + 3 perms y3_4·(P-T₂)·z.
  have hC_compound : ‖(y ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)) * P * z‖ ≤ 19 * s ^ 5 * s ^ 2 * s :=
    calc _ ≤ ‖(y ^ 3 - z ^ 3 -
        (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)) * P‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 3 - z ^ 3 -
          (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)‖ * ‖P‖) * ‖z‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ (19 * s ^ 5 * s ^ 2) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hy3_343 hP (norm_nonneg _) (by positivity)
  have hC1 : ‖z ^ 2 * T₂ * (P - T₂) * z‖ ≤ s ^ 2 * s ^ 2 * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z ^ 2 * T₂ * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ ^ 2 * ‖T₂‖) * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z ^ 2 * T₂‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by
                gcongr
                calc _ ≤ ‖z ^ 2‖ * ‖T₂‖ := norm_mul_le _ _
                  _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ ((s ^ 2 * s ^ 2) * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzn 2) hT₂
            (norm_nonneg _) (by positivity)
  have hC2 : ‖z * T₂ * z * (P - T₂) * z‖ ≤ s * s ^ 2 * s * (5 * s ^ 3) * s :=
    calc _ ≤ ‖z * T₂ * z * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (((‖z‖ * ‖T₂‖) * ‖z‖) * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖z * T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by
                gcongr
                calc _ ≤ ‖z * T₂‖ * ‖z‖ := norm_mul_le _ _
                  _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ (((s * s ^ 2) * s) * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity)
  have hC3 : ‖T₂ * z ^ 2 * (P - T₂) * z‖ ≤ s ^ 2 * s ^ 2 * (5 * s ^ 3) * s :=
    calc _ ≤ ‖T₂ * z ^ 2 * (P - T₂)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ ((‖T₂‖ * ‖z‖ ^ 2) * ‖P - T₂‖) * ‖z‖ := by
          gcongr
          calc _ ≤ ‖T₂ * z ^ 2‖ * ‖P - T₂‖ := norm_mul_le _ _
            _ ≤ _ := by
                gcongr
                calc _ ≤ ‖T₂‖ * ‖z ^ 2‖ := norm_mul_le _ _
                  _ ≤ _ := by gcongr; exact norm_pow_le z 2
      _ ≤ ((s ^ 2 * s ^ 2) * (5 * s ^ 3)) * s := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
  -- Group D: (y²-z²-y2_3)·P·z² + 2 perms y2_3·(P-T₂)·z².
  have hD_compound : ‖(y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)) * P * z ^ 2‖ ≤
      11 * s ^ 4 * s ^ 2 * s ^ 2 :=
    calc _ ≤ ‖(y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)) * P‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ (‖y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)‖ * ‖P‖) * ‖z‖ ^ 2 := by
          gcongr
          · exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ (11 * s ^ 4 * s ^ 2) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          exact mul_le_mul hy2_323 hP (norm_nonneg _) (by positivity)
  have hD1 : ‖z * T₂ * (P - T₂) * z ^ 2‖ ≤ s * s ^ 2 * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖z * T₂ * (P - T₂)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ((‖z‖ * ‖T₂‖) * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖z * T₂‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ ((s * s ^ 2) * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hzn hT₂ (norm_nonneg _) (by positivity)
  have hD2 : ‖T₂ * z * (P - T₂) * z ^ 2‖ ≤ s ^ 2 * s * (5 * s ^ 3) * s ^ 2 :=
    calc _ ≤ ‖T₂ * z * (P - T₂)‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ((‖T₂‖ * ‖z‖) * ‖P - T₂‖) * ‖z‖ ^ 2 := by
          gcongr
          · calc _ ≤ ‖T₂ * z‖ * ‖P - T₂‖ := norm_mul_le _ _
              _ ≤ _ := by gcongr; exact norm_mul_le _ _
          · exact norm_pow_le z 2
      _ ≤ ((s ^ 2 * s) * (5 * s ^ 3)) * s ^ 2 := by
          apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hzn 2)
            (by positivity) (by positivity)
          apply mul_le_mul _ hPmT₂ (norm_nonneg _) (by positivity)
          exact mul_le_mul hT₂ hzn (norm_nonneg _) (by positivity)
  -- Group E: (P²-T₂²)·z³
  have hE : ‖(P ^ 2 - T₂ ^ 2) * z ^ 3‖ ≤ (10 * s ^ 5) * s ^ 3 :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2‖ * ‖z ^ 3‖ := norm_mul_le _ _
      _ ≤ ‖P ^ 2 - T₂ ^ 2‖ * ‖z‖ ^ 3 := by gcongr; exact norm_pow_le z 3
      _ ≤ (10 * s ^ 5) * s ^ 3 := mul_le_mul hP2T22
          (pow_le_pow_left₀ (norm_nonneg _) hzn 3) (by positivity) (by positivity)
  -- Triangle inequality (17 norm_add_le applications, 18 terms).
  set u1 : 𝔸 := z ^ 4 * (P - T₂ - T₃)
  set u2 : 𝔸 := z ^ 3 * (P - T₂ - T₃) * z
  set u3 : 𝔸 := z ^ 2 * (P - T₂ - T₃) * z ^ 2
  set u4 : 𝔸 := z * (P - T₂ - T₃) * z ^ 3
  set u5 : 𝔸 := (P - T₂ - T₃) * z ^ 4
  set u6 : 𝔸 := (y ^ 4 - z ^ 4 -
      (z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3)) * P
  set u7 : 𝔸 := z ^ 3 * T₂ * (P - T₂)
  set u8 : 𝔸 := z ^ 2 * T₂ * z * (P - T₂)
  set u9 : 𝔸 := z * T₂ * z ^ 2 * (P - T₂)
  set u10 : 𝔸 := T₂ * z ^ 3 * (P - T₂)
  set u11 : 𝔸 := (y ^ 3 - z ^ 3 -
      (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)) * P * z
  set u12 : 𝔸 := z ^ 2 * T₂ * (P - T₂) * z
  set u13 : 𝔸 := z * T₂ * z * (P - T₂) * z
  set u14 : 𝔸 := T₂ * z ^ 2 * (P - T₂) * z
  set u15 : 𝔸 := (y ^ 2 - z ^ 2 - (z * T₂ + T₂ * z)) * P * z ^ 2
  set u16 : 𝔸 := z * T₂ * (P - T₂) * z ^ 2
  set u17 : 𝔸 := T₂ * z * (P - T₂) * z ^ 2
  set u18 : 𝔸 := (P ^ 2 - T₂ ^ 2) * z ^ 3
  have ht_17 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10
    + u11 + u12 + u13 + u14 + u15 + u16 + u17) u18
  have ht_16 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10
    + u11 + u12 + u13 + u14 + u15 + u16) u17
  have ht_15 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10
    + u11 + u12 + u13 + u14 + u15) u16
  have ht_14 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10
    + u11 + u12 + u13 + u14) u15
  have ht_13 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10
    + u11 + u12 + u13) u14
  have ht_12 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10
    + u11 + u12) u13
  have ht_11 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10
    + u11) u12
  have ht_10 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10) u11
  have ht_9 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9) u10
  have ht_8 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8) u9
  have ht_7 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7) u8
  have ht_6 := norm_add_le (u1 + u2 + u3 + u4 + u5 + u6) u7
  have ht_5 := norm_add_le (u1 + u2 + u3 + u4 + u5) u6
  have ht_4 := norm_add_le (u1 + u2 + u3 + u4) u5
  have ht_3 := norm_add_le (u1 + u2 + u3) u4
  have ht_2 := norm_add_le (u1 + u2) u3
  have ht_1 := norm_add_le u1 u2
  nlinarith [pow_nonneg hs_nn 8, pow_nonneg hs_nn 7, pow_nonneg hs_nn 6,
    pow_nonneg hs_nn 5, pow_nonneg hs_nn 4, pow_nonneg hs_nn 3,
    pow_nonneg hs_nn 2, hs_le_one, sq_nonneg s]

/-- Norm bound for `I₂ residual` (post `(3:𝕂)⁻¹` scalar factor):
inner sum ≤ 50·s⁶ for `s < 1/10`. -/
theorem norm_I2_residual_inner_le (z P T₂ T₃ : 𝔸) {s : ℝ} (hs_nn : 0 ≤ s)
    (hs_small : s ≤ 1 / 10)
    (hz : ‖z‖ ≤ s) (hP : ‖P‖ ≤ s ^ 2) (hT₂ : ‖T₂‖ ≤ s ^ 2)
    (hPmT₂ : ‖P - T₂‖ ≤ 5 * s ^ 3) (hPmT₂mT₃ : ‖P - T₂ - T₃‖ ≤ 5 * s ^ 4) :
    ‖z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z + (P - T₂ - T₃) * z ^ 2 +
     z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) +
     (P ^ 2 - T₂ ^ 2) * z + P ^ 3‖ ≤ 50 * s ^ 6 := by
  -- Helper bounds
  have hP2T22 := norm_P2_sub_T22_le P T₂ hs_nn hP hT₂ hPmT₂
  have hPzP := norm_PzP_sub_T2zT2_le z P T₂ hs_nn hs_small hz hT₂ hPmT₂
  -- Term 1: z² · (P-T₂-T₃) ≤ s²·5s⁴ = 5s⁶
  have h1 : ‖z ^ 2 * (P - T₂ - T₃)‖ ≤ s ^ 2 * (5 * s ^ 4) :=
    calc _ ≤ ‖z ^ 2‖ * ‖P - T₂ - T₃‖ := norm_mul_le _ _
      _ ≤ ‖z‖ ^ 2 * ‖P - T₂ - T₃‖ := by gcongr; exact norm_pow_le z 2
      _ ≤ s ^ 2 * (5 * s ^ 4) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz 2)
          hPmT₂mT₃ (norm_nonneg _) (by positivity)
  -- Term 2: z · (P-T₂-T₃) · z ≤ s·5s⁴·s = 5s⁶
  have h2 : ‖z * (P - T₂ - T₃) * z‖ ≤ s * (5 * s ^ 4) * s :=
    calc _ ≤ ‖z * (P - T₂ - T₃)‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (‖z‖ * ‖P - T₂ - T₃‖) * ‖z‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (s * (5 * s ^ 4)) * s := by
          apply mul_le_mul _ hz (norm_nonneg _) (by positivity)
          exact mul_le_mul hz hPmT₂mT₃ (norm_nonneg _) (by positivity)
  -- Term 3: (P-T₂-T₃) · z² ≤ 5s⁴·s² = 5s⁶
  have h3 : ‖(P - T₂ - T₃) * z ^ 2‖ ≤ (5 * s ^ 4) * s ^ 2 :=
    calc _ ≤ ‖P - T₂ - T₃‖ * ‖z ^ 2‖ := norm_mul_le _ _
      _ ≤ ‖P - T₂ - T₃‖ * ‖z‖ ^ 2 := by gcongr; exact norm_pow_le z 2
      _ ≤ (5 * s ^ 4) * s ^ 2 := mul_le_mul hPmT₂mT₃
          (pow_le_pow_left₀ (norm_nonneg _) hz 2) (by positivity) (by positivity)
  -- Term 4: z · (P²-T₂²) ≤ s·10s⁵ = 10s⁶
  have h4 : ‖z * (P ^ 2 - T₂ ^ 2)‖ ≤ s * (10 * s ^ 5) :=
    calc _ ≤ ‖z‖ * ‖P ^ 2 - T₂ ^ 2‖ := norm_mul_le _ _
      _ ≤ s * (10 * s ^ 5) := mul_le_mul hz hP2T22 (norm_nonneg _) hs_nn
  -- Term 5: PzP - T₂zT₂ ≤ 13s⁶
  -- (already have hPzP)
  -- Term 6: (P²-T₂²) · z ≤ 10s⁵·s = 10s⁶
  have h6 : ‖(P ^ 2 - T₂ ^ 2) * z‖ ≤ (10 * s ^ 5) * s :=
    calc _ ≤ ‖P ^ 2 - T₂ ^ 2‖ * ‖z‖ := norm_mul_le _ _
      _ ≤ (10 * s ^ 5) * s := mul_le_mul hP2T22 hz (norm_nonneg _) (by positivity)
  -- Term 7: P³ ≤ s⁶
  have h7 : ‖P ^ 3‖ ≤ (s ^ 2) ^ 3 :=
    calc _ ≤ ‖P‖ ^ 3 := norm_pow_le P 3
      _ ≤ (s ^ 2) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hP 3
  -- Sum 7 terms via norm_add_le chain
  have ha1 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂) +
    (P ^ 2 - T₂ ^ 2) * z) (P ^ 3)
  have ha2 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + z * (P ^ 2 - T₂ ^ 2) + (P * z * P - T₂ * z * T₂))
    ((P ^ 2 - T₂ ^ 2) * z)
  have ha3 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2 + z * (P ^ 2 - T₂ ^ 2)) (P * z * P - T₂ * z * T₂)
  have ha4 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z +
    (P - T₂ - T₃) * z ^ 2) (z * (P ^ 2 - T₂ ^ 2))
  have ha5 := norm_add_le (z ^ 2 * (P - T₂ - T₃) + z * (P - T₂ - T₃) * z)
    ((P - T₂ - T₃) * z ^ 2)
  have ha6 := norm_add_le (z ^ 2 * (P - T₂ - T₃)) (z * (P - T₂ - T₃) * z)
  -- Sum: 5+5+5+10+13+10+1 = 49 ≤ 50
  nlinarith [pow_nonneg hs_nn 6]

set_option maxHeartbeats 1024000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Algebraic decomposition of `pieceB''` for the sextic remainder small-s case.**

States that pieceB'' (the algebraic part of the sextic remainder, with H1
NOT applied — keeping the `y - z - ½[a,b] - ½y²` form) decomposes as:

```
pieceB'' = (I₁ - corr₁ - corr₁_5) + (I₂ - corr₂ - corr₂_5)
           - ¼(y⁴ - z⁴ - y4_5) + ⅕(y⁵ - z⁵)
```

where:
- `I₁ = y - z - ½[a,b] - ½y² + ⅓z³ - C₃` (== ½W + ⅓z³ - C₃ via H1)
- `I₂ = ⅓(y³ - z³)`
- `corr₁`, `corr₂` from `quintic_pure_identity` (deg-4 corrections)
- `corr₁_5 = ½·W5`, `corr₂_5 = ⅓·y3_5` from `sextic_pure_identity` (deg-5)

Proof: `pieceB'' - RHS = (LHS_QPI) + (LHS_SPI) = 0 + 0 = 0` via QPI + SPI. -/
theorem pieceB_sextic_decomp (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃_QPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)
    let T₃_SPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃_SPI + T₃_SPI * T₂)
    let y3_5 : 𝔸 := z ^ 2 * T₃_SPI + z * T₃_SPI * z + T₃_SPI * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z
    let y4_5 : 𝔸 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3
    let y : 𝔸 := exp a * exp b - 1
    let corr₁ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃_QPI + T₃_QPI * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2
    let corr₂ : 𝔸 := (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)
    let corr₁_5 : 𝔸 := (2 : 𝕂)⁻¹ • W5
    let corr₂_5 : 𝔸 := (3 : 𝕂)⁻¹ • y3_5
    -- pieceB''
    y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
      (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b =
    -- RHS
    ((y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
        (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b) - corr₁ - corr₁_5) +
    ((3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) - corr₂ - corr₂_5) -
    (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4 - y4_5) +
    (5 : 𝕂)⁻¹ • (y ^ 5 - z ^ 5) := by
  intro z T₂ T₃_QPI T₃_SPI T₄ W5 y3_5 y4_5 y corr₁ corr₂ corr₁_5 corr₂_5
  -- Use QPI + SPI
  have hQPI := quintic_pure_identity 𝕂 a b
  have hSPI := sextic_pure_identity 𝕂 a b
  -- Try linear_combination with module as norm
  linear_combination (norm := module) hQPI + hSPI

set_option maxHeartbeats 2048000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Algebraic decomposition of `pieceB'''` for the septic remainder small-s case.**

Extends `pieceB_sextic_decomp` to one degree higher. States that pieceB'''
(= pieceB'' - ⅙y⁶ - C₆) decomposes as:

```
pieceB''' = (I₁ - corr₁ - corr₁_5 - corr₁_6) + (I₂ - corr₂ - corr₂_5 - corr₂_6)
           - ¼(y⁴ - z⁴ - y4_5 - y4_6) + ⅕(y⁵ - z⁵ - y5_6) - ⅙(y⁶ - z⁶)
```

where (in addition to the sextic case):
- `corr₁_6 = ½·W6` (the deg-6 contribution to I₁ from septic_pure_identity)
- `corr₂_6 = ⅓·y3_6` (the deg-6 contribution to ⅓(y³-z³) from septic_pure_identity)
- `y4_6 = z²T₃ + zT₃z + T₃z² + T₃z³ + z²T₂² + zT₂zT₂ + zT₂²z + T₂z²T₂ + T₂zT₂z + T₂²z²`
   (10 terms — the deg-6 contribution to y⁴ via (1,1,1,3) + (1,1,2,2) perms)
- `y5_6 = z⁴T₂ + z³T₂z + z²T₂z² + zT₂z³ + T₂z⁴` (5 terms — (1,1,1,1,2) perms)
- `W6 = 2·y_d6 - (y²)_d6` per septic_pure_identity definition

Each piece on the RHS is deg-7+. Proof: `pieceB''' - RHS =
(LHS_QPI deg-4) + (LHS_SPI deg-5) + (LHS_Septic deg-6) = 0+0+0 = 0`. -/
theorem pieceB_septic_decomp (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃_QPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)
    let T₃_SPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃_SPI + T₃_SPI * T₂)
    let W6 : 𝔸 := (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
        (360 : 𝕂)⁻¹ • b ^ 6 -
        (z * T₅ + T₂ * T₄ + T₃_SPI * T₃_SPI + T₄ * T₂ + T₅ * z)
    let y3_5 : 𝔸 := z ^ 2 * T₃_SPI + z * T₃_SPI * z + T₃_SPI * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z
    let y3_6 : 𝔸 := z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
        z * T₂ * T₃_SPI + z * T₃_SPI * T₂ + T₂ * z * T₃_SPI +
        T₂ * T₃_SPI * z + T₃_SPI * z * T₂ + T₃_SPI * T₂ * z + T₂ ^ 3
    let y4_5 : 𝔸 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3
    let y4_6 : 𝔸 := z ^ 3 * T₃_SPI + z ^ 2 * T₃_SPI * z + z * T₃_SPI * z ^ 2 + T₃_SPI * z ^ 3 +
        z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
        T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2
    let y5_6 : 𝔸 := z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
        z * T₂ * z ^ 3 + T₂ * z ^ 4
    let y : 𝔸 := exp a * exp b - 1
    let corr₁ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃_QPI + T₃_QPI * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2
    let corr₂ : 𝔸 := (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)
    let corr₁_5 : 𝔸 := (2 : 𝕂)⁻¹ • W5
    let corr₂_5 : 𝔸 := (3 : 𝕂)⁻¹ • y3_5
    let corr₁_6 : 𝔸 := (2 : 𝕂)⁻¹ • W6
    let corr₂_6 : 𝔸 := (3 : 𝕂)⁻¹ • y3_6
    -- pieceB''' (extends pieceB'' by -⅙y⁶ - C₆)
    y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
      (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
      (6 : 𝕂)⁻¹ • y ^ 6 -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b =
    -- RHS: 5 pieces
    ((y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
        (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b) - corr₁ - corr₁_5 - corr₁_6) +
    ((3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) - corr₂ - corr₂_5 - corr₂_6) -
    (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4 - y4_5 - y4_6) +
    (5 : 𝕂)⁻¹ • (y ^ 5 - z ^ 5 - y5_6) -
    (6 : 𝕂)⁻¹ • (y ^ 6 - z ^ 6) := by
  intro z T₂ T₃_QPI T₃_SPI T₄ T₅ W5 W6 y3_5 y3_6 y4_5 y4_6 y5_6 y
    corr₁ corr₂ corr₁_5 corr₂_5 corr₁_6 corr₂_6
  -- Use QPI + SPI + Septic
  have hQPI := quintic_pure_identity 𝕂 a b
  have hSPI := sextic_pure_identity 𝕂 a b
  have hSeptic := septic_pure_identity 𝕂 a b
  linear_combination (norm := module) hQPI + hSPI + hSeptic

set_option maxHeartbeats 4096000000 in
omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **Algebraic decomposition of `pieceB''''` for the octic remainder small-s case.**

Extends `pieceB_septic_decomp` to one degree higher. States that pieceB''''
(= pieceB''' + ⅐y⁷ - C₇) decomposes as:

```
pieceB'''' = (I₁ - corr₁ - corr₁_5 - corr₁_6 - corr₁_7) +
              (I₂ - corr₂ - corr₂_5 - corr₂_6 - corr₂_7) -
              ¼(y⁴ - z⁴ - y4_5 - y4_6 - y4_7) +
              ⅕(y⁵ - z⁵ - y5_6 - y5_7) -
              ⅙(y⁶ - z⁶ - y6_7) +
              ⅐(y⁷ - z⁷)
```

where (in addition to the septic case):
- `corr₁_7 = ½·W7` (the deg-7 contribution to I₁ from octic_pure_identity)
- `corr₂_7 = ⅓·y3_7` (the deg-7 contribution to ⅓(y³-z³))
- `y4_7`, `y5_7`, `y6_7` are the deg-7 contributions to y⁴, y⁵, y⁶
- `W7 = 2·y_d7 - (y²)_d7` per octic_pure_identity definition

Each piece on the RHS is deg-8+. Proof: `pieceB'''' - RHS =
(LHS_QPI deg-4) + (LHS_SPI deg-5) + (LHS_Septic deg-6) + (LHS_Octic deg-7)
= 0+0+0+0 = 0`. Foundation for stepping stone 1 (`symmetric_bch_septic_sub_poly_axiom`)
discharge — the deg-9 analog of T2-F7e. -/
theorem pieceB_octic_decomp (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃_QPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (6 : 𝕂)⁻¹ • b ^ 3 +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (2 : 𝕂)⁻¹ • (a ^ 2 * b)
    let T₃_SPI : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + (2 : 𝕂)⁻¹ • (a ^ 2 * b) +
        (2 : 𝕂)⁻¹ • (a * b ^ 2) + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) + (6 : 𝕂)⁻¹ • (a * b ^ 3) +
        (24 : 𝕂)⁻¹ • b ^ 4
    let T₅ : 𝔸 := (120 : 𝕂)⁻¹ • a ^ 5 + (24 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (12 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) + (12 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a * b ^ 4) + (120 : 𝕂)⁻¹ • b ^ 5
    let T₆ : 𝔸 := (720 : 𝕂)⁻¹ • a ^ 6 + (120 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (48 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (36 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (48 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (120 : 𝕂)⁻¹ • (a * b ^ 5) +
        (720 : 𝕂)⁻¹ • b ^ 6
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + (60 : 𝕂)⁻¹ • b ^ 5 +
        (12 : 𝕂)⁻¹ • (a * b ^ 4) + (12 : 𝕂)⁻¹ • (a ^ 4 * b) +
        (6 : 𝕂)⁻¹ • (a ^ 2 * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃_SPI + T₃_SPI * T₂)
    let W6 : 𝔸 := (360 : 𝕂)⁻¹ • a ^ 6 + (60 : 𝕂)⁻¹ • (a ^ 5 * b) +
        (24 : 𝕂)⁻¹ • (a ^ 4 * b ^ 2) + (18 : 𝕂)⁻¹ • (a ^ 3 * b ^ 3) +
        (24 : 𝕂)⁻¹ • (a ^ 2 * b ^ 4) + (60 : 𝕂)⁻¹ • (a * b ^ 5) +
        (360 : 𝕂)⁻¹ • b ^ 6 -
        (z * T₅ + T₂ * T₄ + T₃_SPI * T₃_SPI + T₄ * T₂ + T₅ * z)
    let W7 : 𝔸 := (2520 : 𝕂)⁻¹ • a ^ 7 + (360 : 𝕂)⁻¹ • (a ^ 6 * b) +
        (120 : 𝕂)⁻¹ • (a ^ 5 * b ^ 2) + (72 : 𝕂)⁻¹ • (a ^ 4 * b ^ 3) +
        (72 : 𝕂)⁻¹ • (a ^ 3 * b ^ 4) + (120 : 𝕂)⁻¹ • (a ^ 2 * b ^ 5) +
        (360 : 𝕂)⁻¹ • (a * b ^ 6) + (2520 : 𝕂)⁻¹ • b ^ 7 -
        (z * T₆ + T₂ * T₅ + T₃_SPI * T₄ + T₄ * T₃_SPI + T₅ * T₂ + T₆ * z)
    let y3_5 : 𝔸 := z ^ 2 * T₃_SPI + z * T₃_SPI * z + T₃_SPI * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z
    let y3_6 : 𝔸 := z ^ 2 * T₄ + z * T₄ * z + T₄ * z ^ 2 +
        z * T₂ * T₃_SPI + z * T₃_SPI * T₂ + T₂ * z * T₃_SPI +
        T₂ * T₃_SPI * z + T₃_SPI * z * T₂ + T₃_SPI * T₂ * z + T₂ ^ 3
    let y3_7 : 𝔸 :=
        z * z * T₅
        + z * T₂ * T₄
        + z * T₃_SPI * T₃_SPI
        + z * T₄ * T₂
        + z * T₅ * z
        + T₂ * z * T₄
        + T₂ * T₂ * T₃_SPI
        + T₂ * T₃_SPI * T₂
        + T₂ * T₄ * z
        + T₃_SPI * z * T₃_SPI
        + T₃_SPI * T₂ * T₂
        + T₃_SPI * T₃_SPI * z
        + T₄ * z * T₂
        + T₄ * T₂ * z
        + T₅ * z * z
    let y4_5 : 𝔸 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3
    let y4_6 : 𝔸 := z ^ 3 * T₃_SPI + z ^ 2 * T₃_SPI * z + z * T₃_SPI * z ^ 2 + T₃_SPI * z ^ 3 +
        z ^ 2 * T₂ ^ 2 + z * T₂ * z * T₂ + z * T₂ ^ 2 * z +
        T₂ * z ^ 2 * T₂ + T₂ * z * T₂ * z + T₂ ^ 2 * z ^ 2
    let y4_7 : 𝔸 :=
        z * z * z * T₄
        + z * z * T₂ * T₃_SPI
        + z * z * T₃_SPI * T₂
        + z * z * T₄ * z
        + z * T₂ * z * T₃_SPI
        + z * T₂ * T₂ * T₂
        + z * T₂ * T₃_SPI * z
        + z * T₃_SPI * z * T₂
        + z * T₃_SPI * T₂ * z
        + z * T₄ * z * z
        + T₂ * z * z * T₃_SPI
        + T₂ * z * T₂ * T₂
        + T₂ * z * T₃_SPI * z
        + T₂ * T₂ * z * T₂
        + T₂ * T₂ * T₂ * z
        + T₂ * T₃_SPI * z * z
        + T₃_SPI * z * z * T₂
        + T₃_SPI * z * T₂ * z
        + T₃_SPI * T₂ * z * z
        + T₄ * z * z * z
    let y5_6 : 𝔸 := z ^ 4 * T₂ + z ^ 3 * T₂ * z + z ^ 2 * T₂ * z ^ 2 +
        z * T₂ * z ^ 3 + T₂ * z ^ 4
    let y5_7 : 𝔸 :=
        z * z * z * z * T₃_SPI
        + z * z * z * T₂ * T₂
        + z * z * z * T₃_SPI * z
        + z * z * T₂ * z * T₂
        + z * z * T₂ * T₂ * z
        + z * z * T₃_SPI * z * z
        + z * T₂ * z * z * T₂
        + z * T₂ * z * T₂ * z
        + z * T₂ * T₂ * z * z
        + z * T₃_SPI * z * z * z
        + T₂ * z * z * z * T₂
        + T₂ * z * z * T₂ * z
        + T₂ * z * T₂ * z * z
        + T₂ * T₂ * z * z * z
        + T₃_SPI * z * z * z * z
    let y6_7 : 𝔸 :=
        z * z * z * z * z * T₂
        + z * z * z * z * T₂ * z
        + z * z * z * T₂ * z * z
        + z * z * T₂ * z * z * z
        + z * T₂ * z * z * z * z
        + T₂ * z * z * z * z * z
    let y : 𝔸 := exp a * exp b - 1
    let corr₁ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + (24 : 𝕂)⁻¹ • b ^ 4 +
        (6 : 𝕂)⁻¹ • (a * b ^ 3) + (6 : 𝕂)⁻¹ • (a ^ 3 * b) +
        (4 : 𝕂)⁻¹ • (a ^ 2 * b ^ 2) -
        (2 : 𝕂)⁻¹ • (z * T₃_QPI + T₃_QPI * z) - (2 : 𝕂)⁻¹ • T₂ ^ 2
    let corr₂ : 𝔸 := (3 : 𝕂)⁻¹ • (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2)
    let corr₁_5 : 𝔸 := (2 : 𝕂)⁻¹ • W5
    let corr₂_5 : 𝔸 := (3 : 𝕂)⁻¹ • y3_5
    let corr₁_6 : 𝔸 := (2 : 𝕂)⁻¹ • W6
    let corr₂_6 : 𝔸 := (3 : 𝕂)⁻¹ • y3_6
    let corr₁_7 : 𝔸 := (2 : 𝕂)⁻¹ • W7
    let corr₂_7 : 𝔸 := (3 : 𝕂)⁻¹ • y3_7
    -- pieceB'''' (extends pieceB''' by +⅐y⁷ - C₇)
    y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
      (3 : 𝕂)⁻¹ • y ^ 3 - (4 : 𝕂)⁻¹ • y ^ 4 + (5 : 𝕂)⁻¹ • y ^ 5 -
      (6 : 𝕂)⁻¹ • y ^ 6 + (7 : 𝕂)⁻¹ • y ^ 7 -
      bch_cubic_term 𝕂 a b - bch_quartic_term 𝕂 a b -
      bch_quintic_term 𝕂 a b - bch_sextic_term 𝕂 a b -
      bch_septic_term 𝕂 a b =
    -- RHS: 6 pieces
    ((y - z - (2 : 𝕂)⁻¹ • (a * b - b * a) - (2 : 𝕂)⁻¹ • y ^ 2 +
        (3 : 𝕂)⁻¹ • z ^ 3 - bch_cubic_term 𝕂 a b) -
        corr₁ - corr₁_5 - corr₁_6 - corr₁_7) +
    ((3 : 𝕂)⁻¹ • (y ^ 3 - z ^ 3) - corr₂ - corr₂_5 - corr₂_6 - corr₂_7) -
    (4 : 𝕂)⁻¹ • (y ^ 4 - z ^ 4 - y4_5 - y4_6 - y4_7) +
    (5 : 𝕂)⁻¹ • (y ^ 5 - z ^ 5 - y5_6 - y5_7) -
    (6 : 𝕂)⁻¹ • (y ^ 6 - z ^ 6 - y6_7) +
    (7 : 𝕂)⁻¹ • (y ^ 7 - z ^ 7) := by
  intro z T₂ T₃_QPI T₃_SPI T₄ T₅ T₆ W5 W6 W7 y3_5 y3_6 y3_7 y4_5 y4_6 y4_7
    y5_6 y5_7 y6_7 y
    corr₁ corr₂ corr₁_5 corr₂_5 corr₁_6 corr₂_6 corr₁_7 corr₂_7
  -- Use QPI + SPI + Septic + Octic
  have hQPI := quintic_pure_identity 𝕂 a b
  have hSPI := sextic_pure_identity 𝕂 a b
  have hSeptic := septic_pure_identity 𝕂 a b
  have hOctic := octic_pure_identity 𝕂 a b
  linear_combination (norm := module) hQPI + hSPI + hSeptic + hOctic

end

end BCH
