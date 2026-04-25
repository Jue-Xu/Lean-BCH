/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH/Suzuki5Quintic — Explicit 5-factor palindromic quintic remainder

Provides the Childs-basis expansion of `R₅(A,B,p)`, the τ⁵ coefficient
of `log(suzuki5Product A B p τ) − τ•(A+B)` under `IsSuzukiCubic p`.

## Background

Under `IsSuzukiCubic p`, the degree-2, 3, 4, and 6 (by palindromic
symmetry) coefficients of `log(suzuki5Product A B p τ) − τ•(A+B)`
vanish identically, leaving a leading τ⁵ term. The symbolic non-
commutative BCH computation (CAS pipeline
`Lean-Trotter/scripts/compute_bch_prefactors.py`) projects this τ⁵
element onto the 8 Childs commutators with polynomial coefficients
`βᵢ(p) ∈ ℚ[p]`:

    β₁(p) =  127·p²/144000  + 13·p/36000  −  1/24000
    β₂(p) =       p²/12000  + 13·p/6000   −  1/4000
    β₃(p) =  0
    β₄(p) =  −61·p²/9000    + 13·p/3000   −  1/2000
    β₅(p) =   31·p²/9000    − 13·p/18000  +  1/12000
    β₆(p) =   31·p²/3000    − 13·p/6000   +  1/4000
    β₇(p) =  0
    β₈(p) =       p²/18000  + 13·p/9000   −  1/6000

(These match the symbolic output at lines 567–581 of
`LieTrotter/Suzuki4ViaBCH.lean` in the Lean-Trotter project.)

For `p` the unique real root of `IsSuzukiCubic p` (i.e.
`p = 1/(4−4^(1/3)) ≈ 0.4145`), numerically `|βᵢ(p)| ≤ 0.002 ≪ 1`.

## Main results (this file)

* `IsSuzukiCubic_real_strict_bound`: under `IsSuzukiCubic p` for `p : ℝ`,
  `0 < p ∧ p < 1`.
* `suzuki5_β₁ … suzuki5_β₈`: the eight signed polynomials in ℝ[p].
* `abs_suzuki5_βᵢ_le_one`: under `IsSuzukiCubic p` for `p : ℝ`,
  each `|suzuki5_βᵢ p| ≤ 1`.
* `suzuki5_R5 A B p`: the explicit τ⁵ element in the Childs basis,
  wrapped as an opaque `noncomputable def` to avoid downstream kernel
  whnf blow-up.
* `norm_suzuki5_R5_le_bchFourFoldSum`: `‖suzuki5_R5 A B p‖ ≤
  bchFourFoldSum A B` under `IsSuzukiCubic p` (for `p : ℝ`).

## Deferred

The headline theorem

    ‖suzuki5_bch ℝ A B p τ − τ•(A+B) − τ⁵ • suzuki5_R5 A B p‖ ≤ K·‖τ‖⁶

is the BIG open piece of Phase 1: extracting the τ⁵ leading coefficient
from the existing M4b quintic-error bound, in terms of the 8 Childs
commutators. Its proof requires symbolic 5-factor BCH composition in
Lean, which is multi-week work.

Once that lands, `Palindromic.lean`'s bridging corollary
`suzuki5_log_product_quintic_of_IsSuzukiCubic` becomes a direct
consequence and the Lean-Trotter-side axiom
`bch_w4Deriv_quintic_level2` becomes closeable in a short derivation
through `hasDerivAt_w4_explicit` + `norm_suzuki4_order5_via_module3`.
-/

import BCH.Palindromic
import BCH.ChildsBasis
import Mathlib.Analysis.Complex.ExponentialBounds

namespace BCH

/-!
## IsSuzukiCubic real-root bound

The unique real root of `4p³ + (1−4p)³ = 0` lies in `(0, 1)`.
-/

/-- For `p : ℝ` satisfying `IsSuzukiCubic p`, we have `0 < p ∧ p < 1`. -/
lemma IsSuzukiCubic_real_strict_bound (p : ℝ) (hcubic : IsSuzukiCubic p) :
    0 < p ∧ p < 1 := by
  rw [IsSuzukiCubic_iff] at hcubic
  -- Convert to expanded cubic form.
  have h_exp : 4 * p ^ 3 + (1 - 4 * p) ^ 3 = -60 * p ^ 3 + 48 * p ^ 2 - 12 * p + 1 := by
    ring
  rw [h_exp] at hcubic
  -- hcubic: -60 * p^3 + 48 * p^2 - 12 * p + 1 = 0
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    -- p ≤ 0: -60·p³ ≥ 0, 48·p² ≥ 0, -12·p ≥ 0, +1 ⟹ LHS ≥ 1 ≠ 0.
    have hp3 : p ^ 3 ≤ 0 := by
      have heq : p ^ 3 = p * p ^ 2 := by ring
      rw [heq]
      exact mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg p)
    have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
    linarith
  · by_contra h
    push_neg at h  -- h : 1 ≤ p
    -- For p ≥ 1: -60·p³ + 48·p² ≤ -12·p² ≤ -12,  -12·p ≤ -12, so LHS ≤ -23 ≠ 0.
    have hp2_ge : 1 ≤ p ^ 2 := by nlinarith [h]
    -- p^2 ≤ p^3 when p ≥ 1
    have hp23 : p ^ 2 ≤ p ^ 3 := by
      have heq : p ^ 3 - p ^ 2 = p ^ 2 * (p - 1) := by ring
      nlinarith [sq_nonneg p, h]
    -- Combine: -60p³ + 48p² ≤ -12p² (since 60p³ ≥ 60p² + 12p², i.e., 60p³ - 60p² ≥ 12p² from p²(p-1) ≥ p²·(p-1)/5 or just p^2*(p-1) ≥ 0 times 60)
    -- Simpler: 60p³ - 48p² = 60p² · (p - 48/60) = 60p² · (p - 0.8) ≥ 60p² · 0.2 = 12p² ≥ 12
    have h_step1 : 60 * p ^ 3 - 48 * p ^ 2 ≥ 12 * p ^ 2 := by
      have heq : 60 * p ^ 3 - 48 * p ^ 2 - 12 * p ^ 2 = 60 * p ^ 2 * (p - 1) := by
        ring
      nlinarith [sq_nonneg p, h, heq]
    linarith

/-!
## The 8 signed prefactor polynomials

Source: `compute_bch_prefactors.py` (Lean-Trotter repo), symbolic CAS
output for the τ⁵ coefficient of `log(suzuki5Product)` projected onto
the Childs 8-commutator basis.
-/

/-- `β₁(p) = 127p²/144000 + 13p/36000 − 1/24000`. -/
noncomputable def suzuki5_β₁ (p : ℝ) : ℝ := 127 * p ^ 2 / 144000 + 13 * p / 36000 - 1 / 24000

/-- `β₂(p) = p²/12000 + 13p/6000 − 1/4000`. -/
noncomputable def suzuki5_β₂ (p : ℝ) : ℝ := p ^ 2 / 12000 + 13 * p / 6000 - 1 / 4000

/-- `β₃(p) = 0` (free-parameter projection choice). -/
noncomputable def suzuki5_β₃ (_p : ℝ) : ℝ := 0

/-- `β₄(p) = −61p²/9000 + 13p/3000 − 1/2000`. -/
noncomputable def suzuki5_β₄ (p : ℝ) : ℝ := -61 * p ^ 2 / 9000 + 13 * p / 3000 - 1 / 2000

/-- `β₅(p) = 31p²/9000 − 13p/18000 + 1/12000`. -/
noncomputable def suzuki5_β₅ (p : ℝ) : ℝ := 31 * p ^ 2 / 9000 - 13 * p / 18000 + 1 / 12000

/-- `β₆(p) = 31p²/3000 − 13p/6000 + 1/4000`. -/
noncomputable def suzuki5_β₆ (p : ℝ) : ℝ := 31 * p ^ 2 / 3000 - 13 * p / 6000 + 1 / 4000

/-- `β₇(p) = 0` (free-parameter projection choice). -/
noncomputable def suzuki5_β₇ (_p : ℝ) : ℝ := 0

/-- `β₈(p) = p²/18000 + 13p/9000 − 1/6000`. -/
noncomputable def suzuki5_β₈ (p : ℝ) : ℝ := p ^ 2 / 18000 + 13 * p / 9000 - 1 / 6000

/-!
## Absolute-value bounds: `|βᵢ(p)| ≤ 1` under IsSuzukiCubic

For `p : ℝ` with `IsSuzukiCubic p`, we have `0 < p < 1`. Each βᵢ is a
quadratic; on `(0, 1)` the absolute value is bounded by a small constant
(≤ 0.003) and in particular ≤ 1.
-/

lemma abs_suzuki5_β₁_le_one (p : ℝ) (hcubic : IsSuzukiCubic p) :
    |suzuki5_β₁ p| ≤ 1 := by
  obtain ⟨hp_pos, hp_lt⟩ := IsSuzukiCubic_real_strict_bound p hcubic
  unfold suzuki5_β₁
  have hp_sq : p ^ 2 ≤ 1 := by nlinarith [hp_pos.le, hp_lt]
  have hp_sq_nn : 0 ≤ p ^ 2 := sq_nonneg p
  rw [abs_le]
  constructor <;> nlinarith [hp_sq, hp_sq_nn, hp_pos.le, hp_lt]

lemma abs_suzuki5_β₂_le_one (p : ℝ) (hcubic : IsSuzukiCubic p) :
    |suzuki5_β₂ p| ≤ 1 := by
  obtain ⟨hp_pos, hp_lt⟩ := IsSuzukiCubic_real_strict_bound p hcubic
  unfold suzuki5_β₂
  have hp_sq : p ^ 2 ≤ 1 := by nlinarith [hp_pos.le, hp_lt]
  have hp_sq_nn : 0 ≤ p ^ 2 := sq_nonneg p
  rw [abs_le]
  constructor <;> nlinarith [hp_sq, hp_sq_nn, hp_pos.le, hp_lt]

lemma abs_suzuki5_β₃_le_one (p : ℝ) (_hcubic : IsSuzukiCubic p) :
    |suzuki5_β₃ p| ≤ 1 := by
  unfold suzuki5_β₃; simp

lemma abs_suzuki5_β₄_le_one (p : ℝ) (hcubic : IsSuzukiCubic p) :
    |suzuki5_β₄ p| ≤ 1 := by
  obtain ⟨hp_pos, hp_lt⟩ := IsSuzukiCubic_real_strict_bound p hcubic
  unfold suzuki5_β₄
  have hp_sq : p ^ 2 ≤ 1 := by nlinarith [hp_pos.le, hp_lt]
  have hp_sq_nn : 0 ≤ p ^ 2 := sq_nonneg p
  rw [abs_le]
  constructor <;> nlinarith [hp_sq, hp_sq_nn, hp_pos.le, hp_lt]

lemma abs_suzuki5_β₅_le_one (p : ℝ) (hcubic : IsSuzukiCubic p) :
    |suzuki5_β₅ p| ≤ 1 := by
  obtain ⟨hp_pos, hp_lt⟩ := IsSuzukiCubic_real_strict_bound p hcubic
  unfold suzuki5_β₅
  have hp_sq : p ^ 2 ≤ 1 := by nlinarith [hp_pos.le, hp_lt]
  have hp_sq_nn : 0 ≤ p ^ 2 := sq_nonneg p
  rw [abs_le]
  constructor <;> nlinarith [hp_sq, hp_sq_nn, hp_pos.le, hp_lt]

lemma abs_suzuki5_β₆_le_one (p : ℝ) (hcubic : IsSuzukiCubic p) :
    |suzuki5_β₆ p| ≤ 1 := by
  obtain ⟨hp_pos, hp_lt⟩ := IsSuzukiCubic_real_strict_bound p hcubic
  unfold suzuki5_β₆
  have hp_sq : p ^ 2 ≤ 1 := by nlinarith [hp_pos.le, hp_lt]
  have hp_sq_nn : 0 ≤ p ^ 2 := sq_nonneg p
  rw [abs_le]
  constructor <;> nlinarith [hp_sq, hp_sq_nn, hp_pos.le, hp_lt]

lemma abs_suzuki5_β₇_le_one (p : ℝ) (_hcubic : IsSuzukiCubic p) :
    |suzuki5_β₇ p| ≤ 1 := by
  unfold suzuki5_β₇; simp

lemma abs_suzuki5_β₈_le_one (p : ℝ) (hcubic : IsSuzukiCubic p) :
    |suzuki5_β₈ p| ≤ 1 := by
  obtain ⟨hp_pos, hp_lt⟩ := IsSuzukiCubic_real_strict_bound p hcubic
  unfold suzuki5_β₈
  have hp_sq : p ^ 2 ≤ 1 := by nlinarith [hp_pos.le, hp_lt]
  have hp_sq_nn : 0 ≤ p ^ 2 := sq_nonneg p
  rw [abs_le]
  constructor <;> nlinarith [hp_sq, hp_sq_nn, hp_pos.le, hp_lt]

/-!
## The τ⁵ element R₅ in the Childs basis

`suzuki5_R5 A B p` is the explicit τ⁵ coefficient of
`log(suzuki5Product A B p τ) − τ•(A+B)` under `IsSuzukiCubic p`,
as produced by the CAS projection onto the 8 Childs commutators.

Wrapped `noncomputable def` to avoid kernel whnf blow-up when
downstream proofs unfold it in a triangle inequality.
-/

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The τ⁵ Childs-basis combination for the 5-factor palindromic
quintic remainder under IsSuzukiCubic. -/
noncomputable def suzuki5_R5 (A B : 𝔸) (p : ℝ) : 𝔸 :=
  suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B +
  suzuki5_β₃ p • childsComm₃ A B + suzuki5_β₄ p • childsComm₄ A B +
  suzuki5_β₅ p • childsComm₅ A B + suzuki5_β₆ p • childsComm₆ A B +
  suzuki5_β₇ p • childsComm₇ A B + suzuki5_β₈ p • childsComm₈ A B

/-- Under `IsSuzukiCubic p`, the τ⁵ Childs-basis element has norm
bounded by `bchFourFoldSum A B` (unit-coefficient Level-2 bound). -/
theorem norm_suzuki5_R5_le_bchFourFoldSum
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ‖suzuki5_R5 A B p‖ ≤ bchFourFoldSum A B := by
  unfold suzuki5_R5 bchFourFoldSum
  have h₁ := abs_suzuki5_β₁_le_one p hcubic
  have h₂ := abs_suzuki5_β₂_le_one p hcubic
  have h₃ := abs_suzuki5_β₃_le_one p hcubic
  have h₄ := abs_suzuki5_β₄_le_one p hcubic
  have h₅ := abs_suzuki5_β₅_le_one p hcubic
  have h₆ := abs_suzuki5_β₆_le_one p hcubic
  have h₇ := abs_suzuki5_β₇_le_one p hcubic
  have h₈ := abs_suzuki5_β₈_le_one p hcubic
  have hC₁ : ‖suzuki5_β₁ p • childsComm₁ A B‖ ≤ ‖childsComm₁ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₁ p| * ‖childsComm₁ A B‖
        ≤ 1 * ‖childsComm₁ A B‖ :=
          mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
      _ = ‖childsComm₁ A B‖ := one_mul _
  have hC₂ : ‖suzuki5_β₂ p • childsComm₂ A B‖ ≤ ‖childsComm₂ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₂ p| * ‖childsComm₂ A B‖
        ≤ 1 * ‖childsComm₂ A B‖ :=
          mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
      _ = ‖childsComm₂ A B‖ := one_mul _
  have hC₃ : ‖suzuki5_β₃ p • childsComm₃ A B‖ ≤ ‖childsComm₃ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₃ p| * ‖childsComm₃ A B‖
        ≤ 1 * ‖childsComm₃ A B‖ :=
          mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)
      _ = ‖childsComm₃ A B‖ := one_mul _
  have hC₄ : ‖suzuki5_β₄ p • childsComm₄ A B‖ ≤ ‖childsComm₄ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₄ p| * ‖childsComm₄ A B‖
        ≤ 1 * ‖childsComm₄ A B‖ :=
          mul_le_mul_of_nonneg_right h₄ (norm_nonneg _)
      _ = ‖childsComm₄ A B‖ := one_mul _
  have hC₅ : ‖suzuki5_β₅ p • childsComm₅ A B‖ ≤ ‖childsComm₅ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₅ p| * ‖childsComm₅ A B‖
        ≤ 1 * ‖childsComm₅ A B‖ :=
          mul_le_mul_of_nonneg_right h₅ (norm_nonneg _)
      _ = ‖childsComm₅ A B‖ := one_mul _
  have hC₆ : ‖suzuki5_β₆ p • childsComm₆ A B‖ ≤ ‖childsComm₆ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₆ p| * ‖childsComm₆ A B‖
        ≤ 1 * ‖childsComm₆ A B‖ :=
          mul_le_mul_of_nonneg_right h₆ (norm_nonneg _)
      _ = ‖childsComm₆ A B‖ := one_mul _
  have hC₇ : ‖suzuki5_β₇ p • childsComm₇ A B‖ ≤ ‖childsComm₇ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₇ p| * ‖childsComm₇ A B‖
        ≤ 1 * ‖childsComm₇ A B‖ :=
          mul_le_mul_of_nonneg_right h₇ (norm_nonneg _)
      _ = ‖childsComm₇ A B‖ := one_mul _
  have hC₈ : ‖suzuki5_β₈ p • childsComm₈ A B‖ ≤ ‖childsComm₈ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |suzuki5_β₈ p| * ‖childsComm₈ A B‖
        ≤ 1 * ‖childsComm₈ A B‖ :=
          mul_le_mul_of_nonneg_right h₈ (norm_nonneg _)
      _ = ‖childsComm₈ A B‖ := one_mul _
  calc ‖suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B +
        suzuki5_β₃ p • childsComm₃ A B + suzuki5_β₄ p • childsComm₄ A B +
        suzuki5_β₅ p • childsComm₅ A B + suzuki5_β₆ p • childsComm₆ A B +
        suzuki5_β₇ p • childsComm₇ A B + suzuki5_β₈ p • childsComm₈ A B‖
      ≤ ‖suzuki5_β₁ p • childsComm₁ A B‖ + ‖suzuki5_β₂ p • childsComm₂ A B‖ +
        ‖suzuki5_β₃ p • childsComm₃ A B‖ + ‖suzuki5_β₄ p • childsComm₄ A B‖ +
        ‖suzuki5_β₅ p • childsComm₅ A B‖ + ‖suzuki5_β₆ p • childsComm₆ A B‖ +
        ‖suzuki5_β₇ p • childsComm₇ A B‖ + ‖suzuki5_β₈ p • childsComm₈ A B‖ := by
        -- Chain of seven norm_add_le applications.
        have h_s1 : ‖suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B‖ ≤
                    ‖suzuki5_β₁ p • childsComm₁ A B‖ + ‖suzuki5_β₂ p • childsComm₂ A B‖ :=
                    norm_add_le _ _
        -- instead of chaining manually, use Finset-style or direct norm_add_le iterated.
        -- Simpler: apply norm_add_le repeatedly via linarith+norm_add_le.
        have := norm_add_le
              (suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B +
               suzuki5_β₃ p • childsComm₃ A B + suzuki5_β₄ p • childsComm₄ A B +
               suzuki5_β₅ p • childsComm₅ A B + suzuki5_β₆ p • childsComm₆ A B +
               suzuki5_β₇ p • childsComm₇ A B)
              (suzuki5_β₈ p • childsComm₈ A B)
        have := norm_add_le
              (suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B +
               suzuki5_β₃ p • childsComm₃ A B + suzuki5_β₄ p • childsComm₄ A B +
               suzuki5_β₅ p • childsComm₅ A B + suzuki5_β₆ p • childsComm₆ A B)
              (suzuki5_β₇ p • childsComm₇ A B)
        have := norm_add_le
              (suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B +
               suzuki5_β₃ p • childsComm₃ A B + suzuki5_β₄ p • childsComm₄ A B +
               suzuki5_β₅ p • childsComm₅ A B)
              (suzuki5_β₆ p • childsComm₆ A B)
        have := norm_add_le
              (suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B +
               suzuki5_β₃ p • childsComm₃ A B + suzuki5_β₄ p • childsComm₄ A B)
              (suzuki5_β₅ p • childsComm₅ A B)
        have := norm_add_le
              (suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B +
               suzuki5_β₃ p • childsComm₃ A B)
              (suzuki5_β₄ p • childsComm₄ A B)
        have := norm_add_le
              (suzuki5_β₁ p • childsComm₁ A B + suzuki5_β₂ p • childsComm₂ A B)
              (suzuki5_β₃ p • childsComm₃ A B)
        have := norm_add_le
              (suzuki5_β₁ p • childsComm₁ A B) (suzuki5_β₂ p • childsComm₂ A B)
        linarith
    _ ≤ ‖childsComm₁ A B‖ + ‖childsComm₂ A B‖ + ‖childsComm₃ A B‖ + ‖childsComm₄ A B‖ +
        ‖childsComm₅ A B‖ + ‖childsComm₆ A B‖ + ‖childsComm₇ A B‖ + ‖childsComm₈ A B‖ := by
        linarith [hC₁, hC₂, hC₃, hC₄, hC₅, hC₆, hC₇, hC₈]

/-! ### B2.2.e τ⁵ matching identity: L_leading + γ5·E_5 = R₅(A,B,p)

The cornerstone polynomial-in-p identity that combines:
- the L_leading projection (`comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis`),
- the E_5 projection (`smul_5760_symmetric_bch_quintic_poly_eq_childs_basis`),
- the Jacobi relations C₂=C₃, C₆=C₇,
to identify the τ⁵ content of `suzuki5_bch` as `R₅(A, B, p)` modulo IsSuzukiCubic.

Proof structure:
1. Apply Childs projections to rewrite `[V,[V,E_3]]` and `E_5` on the basis.
2. Apply Jacobi to swap C₃↔C₂ and C₇↔C₆.
3. Unfold R₅(A,B,p) and βᵢ(p).
4. Express each βᵢ(p) as `(LHS polynomial in p) - 0` modulo `4p³+(1-4p)³`
   via 6 `linear_combination` calls (one per non-trivial Cᵢ).
5. Substitute and close via `module` (pure ring identity in p, no hcubic). -/

/-- **B2.2.e τ⁵ matching identity (sans τ⁵ scaling)**: under `IsSuzukiCubic p`,
the L_leading and γ5·E_5 contributions on the Childs basis sum to `R₅(A, B, p)`. -/
theorem L_leading_plus_E5_eq_R5 (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ((1 / 3 : ℝ) * (p * (1 - 4 * p) * (1 - 2 * p) * (p ^ 2 - (1 - 4 * p) ^ 2))) •
        commBr (A + B) (commBr (A + B) (symmetric_bch_cubic_poly ℝ A B)) +
      (4 * p ^ 5 + (1 - 4 * p) ^ 5) • symmetric_bch_quintic_poly ℝ A B =
    suzuki5_R5 A B p := by
  -- Unfold IsSuzukiCubic to get the cubic identity 4p³+(1-4p)³ = 0.
  have hcubic' : 4 * p ^ 3 + (1 - 4 * p) ^ 3 = 0 := hcubic
  -- Substitute Childs projections.
  have h24 := comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis (𝕂 := ℝ) A B
  have h5760 := smul_5760_symmetric_bch_quintic_poly_eq_childs_basis (𝕂 := ℝ) A B
  have h24_inv : commBr (A + B) (commBr (A + B) (symmetric_bch_cubic_poly ℝ A B)) =
      (1 / 24 : ℝ) • ((24 : ℝ) • commBr (A + B) (commBr (A + B) (symmetric_bch_cubic_poly ℝ A B))) := by
    rw [smul_smul]; norm_num
  have h5760_inv : symmetric_bch_quintic_poly ℝ A B =
      (1 / 5760 : ℝ) • ((5760 : ℝ) • symmetric_bch_quintic_poly ℝ A B) := by
    rw [smul_smul]; norm_num
  rw [h24_inv, h5760_inv, h24, h5760]
  -- Apply Jacobi C₂ = C₃ and C₆ = C₇.
  rw [← childsComm₂_eq_childsComm₃ A B, ← childsComm₆_eq_childsComm₇ A B]
  unfold suzuki5_R5 suzuki5_β₁ suzuki5_β₂ suzuki5_β₃ suzuki5_β₄
    suzuki5_β₅ suzuki5_β₆ suzuki5_β₇ suzuki5_β₈
  -- Set up `p_p` and `g5` shorthands; prove the 6 βᵢ ↔ poly identities under hcubic.
  set p_p : ℝ := p * (1 - 4 * p) * (1 - 2 * p) * (p ^ 2 - (1 - 4 * p) ^ 2) with hp_p
  set g5 : ℝ := 4 * p ^ 5 + (1 - 4 * p) ^ 5 with hg5
  have eq1 : 127 * p ^ 2 / 144000 + 13 * p / 36000 - 1 / 24000 =
             p_p / 72 - 7 * g5 / 5760 := by
    rw [hp_p, hg5]
    linear_combination (-(41 * p ^ 2 / 5760 - 29 * p / 7200 - 169 / 144000)) * hcubic'
  have eq2 : p ^ 2 / 12000 + 13 * p / 6000 - 1 / 4000 =
             p_p / 24 - 12 * g5 / 5760 := by
    rw [hp_p, hg5]
    linear_combination (-(23 * p ^ 2 / 480 - 29 * p / 1200 - 11 / 6000)) * hcubic'
  have eq4 : -61 * p ^ 2 / 9000 + 13 * p / 3000 - 1 / 2000 =
             p_p / 36 + 16 * g5 / 5760 := by
    rw [hp_p, hg5]
    linear_combination (-(37 * p ^ 2 / 360 - 29 * p / 600 + 59 / 18000)) * hcubic'
  have eq5 : 31 * p ^ 2 / 9000 - 13 * p / 18000 + 1 / 12000 =
             p_p / 72 - 16 * g5 / 5760 := by
    rw [hp_p, hg5]
    linear_combination (-(-7 * p ^ 2 / 360 + 29 * p / 3600 - 103 / 36000)) * hcubic'
  have eq6 : 31 * p ^ 2 / 3000 - 13 * p / 6000 + 1 / 4000 =
             p_p / 24 - 48 * g5 / 5760 := by
    rw [hp_p, hg5]
    linear_combination (-(-7 * p ^ 2 / 120 + 29 * p / 1200 - 103 / 12000)) * hcubic'
  have eq8 : p ^ 2 / 18000 + 13 * p / 9000 - 1 / 6000 =
             p_p / 36 - 8 * g5 / 5760 := by
    rw [hp_p, hg5]
    linear_combination (-(23 * p ^ 2 / 720 - 29 * p / 1800 - 11 / 9000)) * hcubic'
  -- Substitute β_i with the L_leading + γ5·E_5 form.
  rw [eq1, eq2, eq4, eq5, eq6, eq8]
  module

/-- **B2.2.e τ⁵-scaled matching identity**: τ⁵·L_leading_coeff + τ⁵·γ5·E_5 = τ⁵·R₅,
applying the L_leading-on-Childs-basis closed form (post substitution of
δa = 4(pτ)³•E_3, δb = ((1-4p)τ)³•E_3 in `sym_cubic_poly_linear_part_smul_V`).

Direct corollary of `L_leading_plus_E5_eq_R5` by τ⁵ smul, plus the closed
form `sym_cubic_poly_linear_part_at_strangBlock_E3`. -/
theorem sym_cubic_linear_part_τ5_plus_E5_τ5_eq_R5_τ5
    (A B : 𝔸) (p τ : ℝ) (hcubic : IsSuzukiCubic p) :
    sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
        ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly ℝ A B)
        (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly ℝ A B) +
      (τ ^ 5 * (4 * p ^ 5 + (1 - 4 * p) ^ 5)) • symmetric_bch_quintic_poly ℝ A B =
    τ ^ 5 • suzuki5_R5 A B p := by
  -- Substitute the closed-form of the linear part.
  rw [sym_cubic_poly_linear_part_at_strangBlock_E3 (𝕂 := ℝ) A B p τ]
  -- The matching identity scaled by τ⁵.
  have h_match := L_leading_plus_E5_eq_R5 A B p hcubic
  have h_match_τ5 : (τ ^ 5 : ℝ) • (((1 / 3 : ℝ) *
        (p * (1 - 4 * p) * (1 - 2 * p) * (p ^ 2 - (1 - 4 * p) ^ 2))) •
          commBr (A + B) (commBr (A + B) (symmetric_bch_cubic_poly ℝ A B)) +
        (4 * p ^ 5 + (1 - 4 * p) ^ 5) • symmetric_bch_quintic_poly ℝ A B) =
      (τ ^ 5 : ℝ) • suzuki5_R5 A B p := by
    rw [h_match]
  -- Distribute τ⁵ and combine scalars; the resulting form matches the goal.
  rw [smul_add, smul_smul, smul_smul] at h_match_τ5
  -- Rewrite the goal scalars to match h_match_τ5.
  convert h_match_τ5 using 2
  ring

/-!
## Headline theorem: τ⁵ identification of `log(suzuki5Product)`

Under `IsSuzukiCubic p`, the τ⁵ Taylor coefficient of `suzuki5_bch ℝ A B p τ
− τ•(A+B)` is precisely `suzuki5_R5 A B p` (the Childs-basis projection),
with τ⁶ residual:

    ‖suzuki5_bch ℝ A B p τ − τ•(A+B) − τ⁵•suzuki5_R5 A B p‖ ≤ K·|τ|⁶

for `|τ| < δ`.

### Proof status

This theorem is now a **fully proved theorem** (no Tier-2 axiom).
Discharged session 12 via the chain:

* `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic` (B2.5 algebraic backbone):
  decomposes `suzuki5_bch - τ•V - τ⁵•R₅` into three explicit summands.
* `norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime`: triangle-inequality
  assembly bounding the three summands under 6 regime hypotheses.
* Six regime helpers `p_regime_of_tau_small`, `q_regime_of_tau_small`,
  `reg_lt_quarter_of_tau_small`, `R_lt_log_two_of_tau_small`,
  `Z1_lt_log_two_of_tau_small`, `Z2_lt_log_two_of_tau_small`: derive the
  6 hypotheses from `‖τ‖ < 1/(10¹¹·pn·qn·s)`.
* Per-term bounds `RHS_T1_le_aux`, `RHS_T2a/b/c_le_aux`, `RHS_T3_le_aux`,
  `D_bound_aux`: bound each of 7 summands of `suzuki5_bch_sub_R5_RHS` by a
  polynomial in `pn`, `qn`, `s` times `‖τ‖⁶`.

Combined: `‖...‖ ≤ K·‖τ‖⁶` with explicit
`K = 4·10⁹·pn⁷·s⁷ + 10⁹·qn⁷·s⁷ + 10⁹·40002⁷·(4pn+qn)⁷·s⁷ +
       2·10¹⁸·pn¹¹·qn¹¹·s¹¹ + 10²⁶·pn¹⁵·qn¹⁵·s¹⁵ +
       10⁸·pn⁶·qn⁶·s⁷ + 2·10³⁰·pn⁹·qn⁹·s⁹`.

After this discharge, only the **B1.c axiom** `symmetric_bch_quintic_sub_poly_axiom`
remains (in `BCH/SymmetricQuintic.lean`).
-/

section HeadlineTheorem

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
  [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **B2.5 algebraic decomposition**: under IsSuzukiCubic p, the τ⁵-shifted
suzuki5_bch difference decomposes as a sum of three explicit terms, each of
which is bounded by `O(τ⁷)` from upstream theorems:

  `suzuki5_bch - τ•V - τ⁵•R₅ = R_b1c + (sym_cubic_poly(4X,Y) - L_leading_τ⁵)
                                + sym_quintic_poly(4X,Y)`

where:
- `R_b1c` is the residual from `norm_suzuki5_bch_sub_smul_sub_quintic_le` (B1.c
  + B2.1, after IsSuzukiCubic τ³ vanishing).
- `L_leading_τ⁵ = sym_cubic_poly_linear_part_smul_V V (4pτ) ((1-4p)τ)
  (4(pτ)³•E_3) (((1-4p)τ)³•E_3)` is the τ⁵ leading content of
  `sym_cubic_poly(4X,Y)` from B2.2.e.

This is the algebraic backbone of the τ⁶ assembly for P1 axiom discharge.
Combines the matching identity (which handles `τ⁵·γ5·E_5 + L_leading_τ⁵ = τ⁵·R₅`
under IsSuzukiCubic) with the M4a + B1.c structure. -/
theorem suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic (A B : 𝔸) (p τ : ℝ)
    (hcubic : IsSuzukiCubic p) :
    suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p =
      (suzuki5_bch ℝ A B p τ - τ • (A + B) -
          (τ ^ 3 * suzuki5_bch_cubic_coeff ℝ p) • symmetric_bch_cubic_poly ℝ A B -
          (τ ^ 5 * suzuki5_bch_quintic_coeff ℝ p) • symmetric_bch_quintic_poly ℝ A B -
          symmetric_bch_cubic_poly ℝ
            ((4 : ℝ) • strangBlock_log ℝ A B p τ)
            (strangBlock_log ℝ A B (1 - 4 * p) τ) -
          symmetric_bch_quintic_poly ℝ
            ((4 : ℝ) • strangBlock_log ℝ A B p τ)
            (strangBlock_log ℝ A B (1 - 4 * p) τ)) +
        (symmetric_bch_cubic_poly ℝ
            ((4 : ℝ) • strangBlock_log ℝ A B p τ)
            (strangBlock_log ℝ A B (1 - 4 * p) τ) -
          sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
            ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly ℝ A B)
            (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly ℝ A B)) +
        symmetric_bch_quintic_poly ℝ
          ((4 : ℝ) • strangBlock_log ℝ A B p τ)
          (strangBlock_log ℝ A B (1 - 4 * p) τ) := by
  have hcubic_zero : suzuki5_bch_cubic_coeff ℝ p = 0 := hcubic
  have hmatch := sym_cubic_linear_part_τ5_plus_E5_τ5_eq_R5_τ5 A B p τ hcubic
  -- The matching identity τ⁵·R₅ = L_leading_τ⁵ + (τ⁵·γ5)·E_5.
  -- Substitute (τ⁵·R₅).symm and the τ³·cubic_coeff zero, then `abel`.
  rw [show (τ ^ 3 * suzuki5_bch_cubic_coeff ℝ p) • symmetric_bch_cubic_poly ℝ A B = 0 from by
    rw [hcubic_zero, mul_zero, zero_smul]]
  rw [← hmatch]
  abel

/-- **Headline theorem (τ⁵ identification)**: Under `IsSuzukiCubic p`,
`suzuki5_bch` has leading-order quintic expansion

    suzuki5_bch ℝ A B p τ = τ•(A+B) + τ⁵ • suzuki5_R5 A B p + O(τ⁶)

where `suzuki5_R5 A B p` is the explicit Childs 4-fold commutator
projection with polynomial prefactors `βᵢ(p)` (see
`Suzuki5Quintic.lean` header).

Quantitatively: `∃ δ > 0, ∃ K ≥ 0, ∀ τ, |τ| < δ →
  ‖suzuki5_bch ℝ A B p τ − τ•(A+B) − τ⁵•suzuki5_R5 A B p‖ ≤ K·|τ|⁶`.

**Status**: Fully proved (no axiom). Discharged session 12 via the chain:
6 regime helpers → `norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime`
(triangle inequality assembly) → 7 per-term polynomial bounds
(`RHS_T1_le_aux`, `RHS_T2a/b/c_le_aux`, `RHS_T3_le_aux`, `D_bound_aux`).

The algebraic decomposition `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic`
above provides the structural backbone: combined with explicit O(τ⁷)
bounds on each summand (from `norm_suzuki5_bch_sub_smul_sub_quintic_le`,
B2.2.e residual + L_extra, and B2.2.c), the discharge becomes a direct
triangle inequality assembly.

`#print axioms norm_suzuki5_bch_sub_smul_sub_R5_le` returns only
`{propext, Classical.choice, Quot.sound, BCH.symmetric_bch_quintic_sub_poly_axiom}`
(B1.c remains as the sole project-side axiom).

**Session 11 progress**: T₂ bound `norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le`
in `BCH/Palindromic.lean` is now fully proved. Below
`norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime` closes the assembly
under regime hypotheses (zero new axioms). The remaining work to discharge
the P1 axiom is the regime-hypothesis derivation for small δ. -/
private theorem norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime
    (A B : 𝔸) (p τ : ℝ) (hcubic : IsSuzukiCubic p)
    (hR : suzuki5ArgNormBound A B p τ < Real.log 2)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4)
    (hreg : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
            ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ < 1 / 4)
    (hZ1 : ‖suzuki5_bch ℝ A B p τ‖ < Real.log 2)
    (hZ2 : ‖bch (𝕂 := ℝ)
      (bch (𝕂 := ℝ)
        ((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))
        (strangBlock_log ℝ A B (1 - 4 * p) τ))
      ((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))‖ < Real.log 2) :
    ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖ ≤
      (4 * (1000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
        1000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 +
        1000000000 * (‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                      ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖) ^ 7) +
      ((3 / 2 : ℝ) *
          ((‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖) *
           (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
            ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
              (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2) +
        (1 / 2 : ℝ) *
          (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
           ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
             (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 3 +
        (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ * ‖A + B‖ ^ 2 *
          (‖(((1 - 4 * p) * τ) : ℝ)‖ *
              (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
           ‖((4 * p * τ) : ℝ)‖ *
              (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5))) +
      2 * (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
            ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
            ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖) ^ 4 *
        (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
         ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
           (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) := by
  -- Apply the algebraic decomposition.
  rw [suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic A B p τ hcubic]
  -- Triangle inequality on the three-summand sum.
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  -- Bound T₁ via norm_suzuki5_bch_sub_smul_sub_quintic_le.
  have hT1 := norm_suzuki5_bch_sub_smul_sub_quintic_le (𝕂 := ℝ) A B p τ
                hR hp h1m4p hreg hZ1 hZ2
  -- Bound T₂ via the new norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le.
  have hT2 := norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le
                (𝕂 := ℝ) A B p τ hp h1m4p
  -- Bound T₃ via B2.2.c.
  -- Need to express sym_quintic_poly(4X, Y) = sym_quintic_poly(α•V + δa, β•V + δb)
  -- where α = 4*p*τ, β = (1-4*p)*τ, V = A+B, δa = 4•X - α•V, δb = Y - β•V.
  set N : ℝ := ‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
            ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
            ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ with hN_def
  have hN_α : ‖((4 * p * τ : ℝ)) • (A + B)‖ ≤ N := by
    rw [hN_def]
    linarith [norm_nonneg ((((1 - 4 * p) * τ : ℝ)) • (A + B)),
              norm_nonneg ((4 : ℝ) • strangBlock_log ℝ A B p τ),
              norm_nonneg (strangBlock_log ℝ A B (1 - 4 * p) τ)]
  have hN_β : ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ ≤ N := by
    rw [hN_def]
    linarith [norm_nonneg ((((4 * p * τ : ℝ)) • (A + B))),
              norm_nonneg ((4 : ℝ) • strangBlock_log ℝ A B p τ),
              norm_nonneg (strangBlock_log ℝ A B (1 - 4 * p) τ)]
  have hN_4X : ‖((4 * p * τ : ℝ)) • (A + B) +
      ((4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B))‖ ≤ N := by
    rw [show ((4 * p * τ : ℝ)) • (A + B) +
        ((4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)) =
        (4 : ℝ) • strangBlock_log ℝ A B p τ from by abel]
    rw [hN_def]
    linarith [norm_nonneg (((4 * p * τ : ℝ)) • (A + B)),
              norm_nonneg ((((1 - 4 * p) * τ : ℝ)) • (A + B)),
              norm_nonneg (strangBlock_log ℝ A B (1 - 4 * p) τ)]
  have hN_Y : ‖(((1 - 4 * p) * τ : ℝ)) • (A + B) +
      (strangBlock_log ℝ A B (1 - 4 * p) τ - (((1 - 4 * p) * τ : ℝ)) • (A + B))‖ ≤ N := by
    rw [show (((1 - 4 * p) * τ : ℝ)) • (A + B) +
        (strangBlock_log ℝ A B (1 - 4 * p) τ - (((1 - 4 * p) * τ : ℝ)) • (A + B)) =
        strangBlock_log ℝ A B (1 - 4 * p) τ from by abel]
    rw [hN_def]
    linarith [norm_nonneg (((4 * p * τ : ℝ)) • (A + B)),
              norm_nonneg ((((1 - 4 * p) * τ : ℝ)) • (A + B)),
              norm_nonneg ((4 : ℝ) • strangBlock_log ℝ A B p τ)]
  have hN_nn : (0 : ℝ) ≤ N := by rw [hN_def]; positivity
  -- Express 4•X = α•V + δa, Y = β•V + δb.
  have h_4X_eq : (4 : ℝ) • strangBlock_log ℝ A B p τ =
      ((4 * p * τ : ℝ)) • (A + B) +
        ((4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)) := by abel
  have h_Y_eq : strangBlock_log ℝ A B (1 - 4 * p) τ =
      (((1 - 4 * p) * τ : ℝ)) • (A + B) +
        (strangBlock_log ℝ A B (1 - 4 * p) τ - (((1 - 4 * p) * τ : ℝ)) • (A + B)) := by abel
  have hT3_eq : symmetric_bch_quintic_poly ℝ
        ((4 : ℝ) • strangBlock_log ℝ A B p τ)
        (strangBlock_log ℝ A B (1 - 4 * p) τ) =
      symmetric_bch_quintic_poly ℝ
        (((4 * p * τ : ℝ)) • (A + B) +
          ((4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)))
        ((((1 - 4 * p) * τ : ℝ)) • (A + B) +
          (strangBlock_log ℝ A B (1 - 4 * p) τ - (((1 - 4 * p) * τ : ℝ)) • (A + B))) := by
    congr 1 <;> abel
  have hT3 := norm_symmetric_bch_quintic_poly_apply_smul_add_smul_add_le
                (𝕂 := ℝ) (A + B) ((4 * p * τ : ℝ)) (((1 - 4 * p) * τ : ℝ))
                ((4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B))
                (strangBlock_log ℝ A B (1 - 4 * p) τ - (((1 - 4 * p) * τ : ℝ)) • (A + B))
                N hN_α hN_β hN_4X hN_Y hN_nn
  -- Convert hT3's LHS from α•V form to 4X form (matching the goal).
  rw [← hT3_eq] at hT3
  -- Goal: (‖T₁‖ + ‖T₂‖) + ‖T₃ in 4X form‖ ≤ poly_T1 + poly_T2 + 2·N⁴·D
  exact add_le_add (add_le_add hT1 hT2) hT3

/-- The bound RHS expression from `norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime`.
Abbreviated for use in the bookkeeping step of the public theorem. -/
private noncomputable def suzuki5_bch_sub_R5_RHS (A B : 𝔸) (p τ : ℝ) : ℝ :=
  (4 * (1000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
    1000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 +
    1000000000 * (‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                  ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖) ^ 7) +
  ((3 / 2 : ℝ) *
      ((‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖) *
       (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
        ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
          (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2) +
    (1 / 2 : ℝ) *
      (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
       ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
         (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 3 +
    (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ * ‖A + B‖ ^ 2 *
      (‖(((1 - 4 * p) * τ) : ℝ)‖ *
          (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
       ‖((4 * p * τ) : ℝ)‖ *
          (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5))) +
  2 * (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
        ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
        ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖) ^ 4 *
    (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
     ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
       (((1 - 4 * p) * τ : ℝ)) • (A + B)‖)

/-! ### Regime-hypothesis derivation auxiliary lemmas

Six small `private` helpers that derive the under-regime hypotheses
from a single small-`τ` regime `‖τ‖ < 1/(10^11·pn·qn·s)`. They feed
into `norm_suzuki5_bch_sub_smul_sub_R5_le_aux` below, which discharges
the P1 axiom. -/

/-- For `‖τ‖ < 1/(10^11·pn·qn·s)`, the per-block argument norm
`‖(p*τ)•A‖+‖(p*τ)•B‖` is below `1/4` (in fact below `10⁻¹¹/qn`). -/
private lemma p_regime_of_tau_small
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  -- Bound η_p = ‖p·τ‖·(‖A‖+‖B‖) ≤ pn·s·‖τ‖
  have hpτ_norm : ‖(p * τ : ℝ)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hsmul_pτA : ‖(p * τ) • A‖ = ‖(p * τ : ℝ)‖ * ‖A‖ := norm_smul _ _
  have hsmul_pτB : ‖(p * τ) • B‖ = ‖(p * τ : ℝ)‖ * ‖B‖ := norm_smul _ _
  have hsum_eq : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ =
                 ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_pτA, hsmul_pτB, hpτ_norm]; ring
  rw [hsum_eq]
  -- Show ‖p‖·‖τ‖·(‖A‖+‖B‖) ≤ pn·s·‖τ‖
  have h_eta_le : ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_pn_τ_nn : 0 ≤ pn * ‖τ‖ := by positivity
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hp_le h_τAB_nn
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_pn_τ_nn
      _ = pn * s * ‖τ‖ := by ring
  -- Show pn·s·‖τ‖ < 1/4 via: pn·s·‖τ‖ < pn·s·(1/(10^11·pn·qn·s)) = 1/(10^11·qn) ≤ 10⁻¹¹ < 1/4
  have hpns_pos : (0 : ℝ) < pn * s := by positivity
  have h_τ_step : pn * s * ‖τ‖ < pn * s * (1 / (10^11 * pn * qn * s)) :=
    mul_lt_mul_of_pos_left hτ_lt hpns_pos
  have h_simplify : pn * s * (1 / (10^11 * pn * qn * s)) = 1 / (10^11 * qn) := by
    field_simp
  have h_inv_le : (1 : ℝ) / (10^11 * qn) ≤ 1 / (10^11 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 10^11)
    nlinarith [hqn_ge]
  have h_eleven_lt : (1 : ℝ) / 10^11 < 1 / 4 := by norm_num
  linarith

/-- For `‖τ‖ < 1/(10^11·pn·qn·s)`, the per-block argument norm for
the inner block `‖((1-4p)*τ)•A‖+‖((1-4p)*τ)•B‖` is below `1/4`. -/
private lemma q_regime_of_tau_small
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn) (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ := norm_nonneg _
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  have hsmul_qτA : ‖((1 - 4 * p) * τ) • A‖ = ‖((1 - 4 * p) * τ : ℝ)‖ * ‖A‖ := norm_smul _ _
  have hsmul_qτB : ‖((1 - 4 * p) * τ) • B‖ = ‖((1 - 4 * p) * τ : ℝ)‖ * ‖B‖ := norm_smul _ _
  have hsum_eq : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ =
                 ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_qτA, hsmul_qτB, hqτ_norm]; ring
  rw [hsum_eq]
  have h_eta_le : ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_qn_τ_nn : 0 ≤ qn * ‖τ‖ := by positivity
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hq_le h_τAB_nn
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_qn_τ_nn
      _ = qn * s * ‖τ‖ := by ring
  have hqns_pos : (0 : ℝ) < qn * s := by positivity
  have h_τ_step : qn * s * ‖τ‖ < qn * s * (1 / (10^11 * pn * qn * s)) :=
    mul_lt_mul_of_pos_left hτ_lt hqns_pos
  have h_simplify : qn * s * (1 / (10^11 * pn * qn * s)) = 1 / (10^11 * pn) := by
    field_simp
  have h_inv_le : (1 : ℝ) / (10^11 * pn) ≤ 1 / (10^11 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 10^11)
    nlinarith [hpn_ge]
  have h_eleven_lt : (1 : ℝ) / 10^11 < 1 / 4 := by norm_num
  linarith

/-- Bound `‖4·X‖ + ‖Y‖ < 1/4` from `norm_strangBlock_log_linear` and the small-`τ`
regime. Gives the `hreg` hypothesis for `under_regime`. -/
private lemma reg_lt_quarter_of_tau_small
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
      ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ < 1 / 4 := by
  -- Apply `p_regime_of_tau_small` and `q_regime_of_tau_small` to get the per-block 1/4 bounds.
  have hp_reg := p_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hAB_le hτ_lt
  have hq_reg := q_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hq_le hAB_le hτ_lt
  -- Bound ‖X‖ ≤ 40002·‖p·τ‖·(‖A‖+‖B‖) and similarly for Y.
  have hX_bound := norm_strangBlock_log_linear (𝕂 := ℝ) A B p τ hp_reg
  have hY_bound := norm_strangBlock_log_linear (𝕂 := ℝ) A B (1 - 4 * p) τ hq_reg
  -- ‖4 • X‖ = 4 · ‖X‖
  have h4_norm : ‖(4 : ℝ)‖ = 4 := by simp
  have h4X_eq : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ =
                4 * ‖strangBlock_log ℝ A B p τ‖ := by
    rw [norm_smul, h4_norm]
  -- Bound ‖p·τ‖·(‖A‖+‖B‖) ≤ pn·s·‖τ‖
  have hpτ_norm : ‖(p * τ : ℝ)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ := norm_nonneg _
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  -- η_p = ‖p·τ‖·(‖A‖+‖B‖) ≤ pn·s·‖τ‖
  have hηp_le : ‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    rw [hpτ_norm]
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_pn_τ_nn : 0 ≤ pn * ‖τ‖ := by positivity
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hp_le h_τAB_nn
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_pn_τ_nn
      _ = pn * s * ‖τ‖ := by ring
  have hηq_le : ‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    rw [hqτ_norm]
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_qn_τ_nn : 0 ≤ qn * ‖τ‖ := by positivity
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hq_le h_τAB_nn
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_qn_τ_nn
      _ = qn * s * ‖τ‖ := by ring
  -- Combine: ‖4X‖+‖Y‖ ≤ 4·40002·pn·s·‖τ‖ + 40002·qn·s·‖τ‖ = 40002·(4·pn+qn)·s·‖τ‖
  have h4X_le : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ ≤ 4 * (40002 * (pn * s * ‖τ‖)) := by
    rw [h4X_eq]
    nlinarith [hX_bound, hηp_le, norm_nonneg (strangBlock_log ℝ A B p τ)]
  have hY_le : ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ ≤ 40002 * (qn * s * ‖τ‖) := by
    nlinarith [hY_bound, hηq_le]
  -- Show 4·40002·pn·s·‖τ‖ + 40002·qn·s·‖τ‖ < 1/4 from ‖τ‖ < δ.
  have h_combined_le :
      4 * (40002 * (pn * s * ‖τ‖)) + 40002 * (qn * s * ‖τ‖) ≤
      40002 * (4 * pn + qn) * s * ‖τ‖ := le_of_eq (by ring)
  have h_4pq_le : 40002 * (4 * pn + qn) ≤ 200010 * pn * qn := by
    have h1 : 4 * pn ≤ 4 * pn * qn := by nlinarith [hqn_ge, hpn_pos]
    have h2 : qn ≤ pn * qn := by nlinarith [hpn_ge, hqn_pos]
    nlinarith
  have h_pq_pos : (0 : ℝ) < pn * qn * s := by positivity
  have h_pq_pos2 : (0 : ℝ) < 200010 * pn * qn := by positivity
  -- 200010·pn·qn·s·‖τ‖ < 200010·pn·qn·s·1/(10^11·pn·qn·s) = 200010/10^11 < 1/4
  have h_τ_step : 200010 * pn * qn * s * ‖τ‖ < 200010 * pn * qn * s * (1/(10^11 * pn * qn * s)) := by
    have h_lhs_pos : (0 : ℝ) < 200010 * pn * qn * s := by positivity
    exact mul_lt_mul_of_pos_left hτ_lt h_lhs_pos
  have h_simp : 200010 * pn * qn * s * (1/(10^11 * pn * qn * s)) = 200010 / 10^11 := by
    field_simp
  have h_num_lt : (200010 : ℝ) / 10^11 < 1/4 := by norm_num
  -- Chain everything together.
  have hs_τ_nn : 0 ≤ s * ‖τ‖ := by positivity
  have h40002_nn : (0 : ℝ) ≤ 40002 := by norm_num
  have h_half : 40002 * (4 * pn + qn) * s * ‖τ‖ ≤ 200010 * pn * qn * s * ‖τ‖ := by
    have : 40002 * (4 * pn + qn) * s * ‖τ‖ ≤ 200010 * pn * qn * s * ‖τ‖ := by
      have h1 : 40002 * (4 * pn + qn) * (s * ‖τ‖) ≤ 200010 * pn * qn * (s * ‖τ‖) :=
        mul_le_mul_of_nonneg_right h_4pq_le hs_τ_nn
      linarith [h1]
    exact this
  linarith [h4X_le, hY_le, h_combined_le, h_half, h_τ_step, h_simp, h_num_lt]

/-- Bound `R = suzuki5ArgNormBound A B p τ ≤ 7·pn·qn·s·‖τ‖` (no `τ` regime needed).
Used in both `R_lt_log_two_of_tau_small` and `Z1_lt_log_two_of_tau_small`. -/
private lemma suzuki5ArgNormBound_le_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s) :
    suzuki5ArgNormBound A B p τ ≤ 7 * pn * qn * s * ‖τ‖ := by
  unfold suzuki5ArgNormBound
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ := norm_nonneg _
  have hA_nn : 0 ≤ ‖A‖ := norm_nonneg _
  have hB_nn : 0 ≤ ‖B‖ := norm_nonneg _
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  -- Bound ‖1-3p‖ ≤ 1 + 3‖p‖.
  have h13p_bnd : ‖((1 : ℝ) - 3 * p)‖ ≤ 1 + 3 * ‖p‖ := by
    have h_norm_step : ‖((1 : ℝ) - 3 * p)‖ ≤ ‖(1 : ℝ)‖ + ‖(3 * p : ℝ)‖ := norm_sub_le _ _
    have h1 : ‖(1 : ℝ)‖ = 1 := norm_one
    have h2 : ‖(3 * p : ℝ)‖ = 3 * ‖p‖ := by rw [norm_mul, RCLike.norm_ofNat]
    linarith
  have h_coef_A_le' : 3 * ‖p‖ + ‖((1 : ℝ) - 3 * p)‖ ≤ 7 * pn * qn := by
    have h7pn : (3 * ‖p‖ + ‖((1 : ℝ) - 3 * p)‖) ≤ 7 * pn := by linarith
    have : 7 * pn ≤ 7 * pn * qn := by nlinarith
    linarith
  have h_coef_B_le' : 4 * ‖p‖ + ‖((1 : ℝ) - 4 * p)‖ ≤ 5 * pn * qn := by
    have h1 : 4 * pn ≤ 4 * pn * qn := by nlinarith
    have h2 : qn ≤ pn * qn := by nlinarith
    linarith
  have h_inner_le : (3 * ‖p‖ + ‖((1 : ℝ) - 3 * p)‖) * ‖A‖ +
                    (4 * ‖p‖ + ‖((1 : ℝ) - 4 * p)‖) * ‖B‖ ≤
                    7 * pn * qn * (‖A‖ + ‖B‖) := by
    have h1 : (3 * ‖p‖ + ‖((1 : ℝ) - 3 * p)‖) * ‖A‖ ≤ 7 * pn * qn * ‖A‖ :=
      mul_le_mul_of_nonneg_right h_coef_A_le' hA_nn
    have h2 : (4 * ‖p‖ + ‖((1 : ℝ) - 4 * p)‖) * ‖B‖ ≤ 7 * pn * qn * ‖B‖ := by
      have h2a : 5 * pn * qn ≤ 7 * pn * qn := by nlinarith
      have h2b : (4 * ‖p‖ + ‖((1 : ℝ) - 4 * p)‖) * ‖B‖ ≤ 5 * pn * qn * ‖B‖ :=
        mul_le_mul_of_nonneg_right h_coef_B_le' hB_nn
      have h2c : 5 * pn * qn * ‖B‖ ≤ 7 * pn * qn * ‖B‖ :=
        mul_le_mul_of_nonneg_right h2a hB_nn
      linarith
    linarith [mul_add (7 * pn * qn) ‖A‖ ‖B‖]
  have h_inner_nn : 0 ≤ (3 * ‖p‖ + ‖((1 : ℝ) - 3 * p)‖) * ‖A‖ +
                    (4 * ‖p‖ + ‖((1 : ℝ) - 4 * p)‖) * ‖B‖ := by positivity
  have h_AB_le_s : ‖A‖ + ‖B‖ ≤ s := hAB_le
  have h_inner_step : (3 * ‖p‖ + ‖((1 : ℝ) - 3 * p)‖) * ‖A‖ +
                     (4 * ‖p‖ + ‖((1 : ℝ) - 4 * p)‖) * ‖B‖ ≤ 7 * pn * qn * s := by
    have h_pq_nn : 0 ≤ 7 * pn * qn := by positivity
    have h2 : 7 * pn * qn * (‖A‖ + ‖B‖) ≤ 7 * pn * qn * s :=
      mul_le_mul_of_nonneg_left h_AB_le_s h_pq_nn
    linarith
  nlinarith [h_inner_step, hτ_nn, h_inner_nn]

/-- Bound `R = suzuki5ArgNormBound A B p τ < log 2` from the small-`τ` regime.
Gives the `hR` hypothesis for `under_regime`. -/
private lemma R_lt_log_two_of_tau_small
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    suzuki5ArgNormBound A B p τ < Real.log 2 := by
  -- R ≤ 7·pn·qn·s·‖τ‖ (helper)
  have hR_bound :=
    suzuki5ArgNormBound_le_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  -- 7·pn·qn·s·‖τ‖ < 7/10^11 < log 2.
  have h_pqs_pos : (0 : ℝ) < 7 * pn * qn * s := by positivity
  have h_τ_step : 7 * pn * qn * s * ‖τ‖ < 7 * pn * qn * s * (1 / (10^11 * pn * qn * s)) :=
    mul_lt_mul_of_pos_left hτ_lt h_pqs_pos
  have h_simp : 7 * pn * qn * s * (1 / (10^11 * pn * qn * s)) = 7 / 10^11 := by field_simp
  have h_num_lt : (7 : ℝ) / 10^11 < Real.log 2 := by
    have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  linarith

/-- Bound `‖suzuki5_bch ℝ A B p τ‖ < log 2` from the small-`τ` regime.
Gives the `hZ1` hypothesis for `under_regime`. Uses
`Real.abs_exp_sub_one_sub_id_le` for `e^R ≤ 1 + R + R²` and
`norm_logOnePlus_le` for the `log(1+x)` bound. -/
private lemma Z1_lt_log_two_of_tau_small
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    ‖suzuki5_bch ℝ A B p τ‖ < Real.log 2 := by
  set R := suzuki5ArgNormBound A B p τ with hR_def
  have hR_nn : 0 ≤ R := by rw [hR_def]; unfold suzuki5ArgNormBound; positivity
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  -- Step 1: R ≤ 7·pn·qn·s·‖τ‖ ≤ 7/10^11 (using helper).
  have hR_bound :=
    suzuki5ArgNormBound_le_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le
  have hR_bound' : R ≤ 7 * pn * qn * s * ‖τ‖ := hR_bound
  have h_pqs_pos : (0 : ℝ) < 7 * pn * qn * s := by positivity
  have h_τ_step : 7 * pn * qn * s * ‖τ‖ ≤ 7 * pn * qn * s * (1 / (10^11 * pn * qn * s)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hτ_lt) (le_of_lt h_pqs_pos)
  have h_simp : 7 * pn * qn * s * (1 / (10^11 * pn * qn * s)) = 7 / 10^11 := by field_simp
  have hR_le_tiny : R ≤ 7 / 10^11 := by linarith
  have hR_le_one : R ≤ 1 := by
    have : (7 : ℝ) / 10^11 ≤ 1 := by norm_num
    linarith
  have h_abs_R : |R| ≤ 1 := by rw [abs_of_nonneg hR_nn]; exact hR_le_one
  -- Step 2: e^R - 1 ≤ R + R² (from |e^R - 1 - R| ≤ R²).
  have h_exp_sub_one_sub : |Real.exp R - 1 - R| ≤ R^2 :=
    Real.abs_exp_sub_one_sub_id_le h_abs_R
  have h_exp_sub_one : Real.exp R - 1 ≤ R + R^2 := by
    have := abs_le.mp h_exp_sub_one_sub
    linarith [this.2]
  have h_R_sq_le_R : R^2 ≤ R := by nlinarith [hR_nn, hR_le_one, sq_nonneg R]
  have h_exp_sub_one_le_2R : Real.exp R - 1 ≤ 2 * R := by linarith
  -- Step 3: ‖suzuki5Product - 1‖ ≤ exp R - 1 (combine M2a + sum_arg bound).
  have h_sum_bnd := sum_arg_norms_le_bound (𝕂 := ℝ) A B p τ
  have h_sub_one_le : ‖suzuki5Product A B p τ - 1‖ ≤ Real.exp R - 1 := by
    have h1 := norm_suzuki5Product_sub_one_le (𝕂 := ℝ) A B p τ
    have h2 : Real.exp _ ≤ Real.exp R := Real.exp_le_exp.mpr h_sum_bnd
    linarith
  -- Step 4: ‖suzuki5Product - 1‖ ≤ 2·R ≤ 14/10^11 ≤ 1/2.
  have h_sub_one_le_2R : ‖suzuki5Product A B p τ - 1‖ ≤ 2 * R := by linarith
  have h_2R_le_tiny : 2 * R ≤ 14 / 10^11 := by linarith
  have h_sub_one_le_half : ‖suzuki5Product A B p τ - 1‖ ≤ 1 / 2 := by
    have : (14 : ℝ) / 10^11 ≤ 1 / 2 := by norm_num
    linarith
  have h_sub_one_lt_one : ‖suzuki5Product A B p τ - 1‖ < 1 := by linarith
  -- Step 5: ‖suzuki5_bch‖ = ‖logOnePlus(suzuki5Product - 1)‖ ≤ 2·‖suzuki5Product - 1‖.
  unfold suzuki5_bch
  have h_logOnePlus_le := norm_logOnePlus_le (𝕂 := ℝ) (suzuki5Product A B p τ - 1) h_sub_one_lt_one
  have h_x_nn : 0 ≤ ‖suzuki5Product A B p τ - 1‖ := norm_nonneg _
  have h_denom_pos : 0 < 1 - ‖suzuki5Product A B p τ - 1‖ := by linarith
  have h_denom_ge : 1 - ‖suzuki5Product A B p τ - 1‖ ≥ 1 / 2 := by linarith
  have h_div_bound :
      ‖suzuki5Product A B p τ - 1‖ / (1 - ‖suzuki5Product A B p τ - 1‖) ≤
      2 * ‖suzuki5Product A B p τ - 1‖ := by
    rw [div_le_iff₀ h_denom_pos]
    nlinarith
  -- Combine: ‖logOnePlus(...)‖ ≤ ‖suzuki5Product-1‖/(1-‖...‖) ≤ 2·‖...‖ ≤ 28/10^11 < log 2.
  have h_logOnePlus_le_2x :
      ‖logOnePlus (𝕂 := ℝ) (suzuki5Product A B p τ - 1)‖ ≤
      2 * ‖suzuki5Product A B p τ - 1‖ := by
    linarith [h_logOnePlus_le]
  have h_2x_le_tiny : 2 * ‖suzuki5Product A B p τ - 1‖ ≤ 28 / 10^11 := by
    linarith
  have h_28_lt_log : (28 : ℝ) / 10^11 < Real.log 2 := by
    have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hbnd : (28 : ℝ) / 10^11 < 0.6931471803 := by norm_num
    linarith
  linarith

set_option maxHeartbeats 8000000 in
/-- Bound `‖outer_bch‖ < log 2` (the `hZ2` hypothesis for `under_regime`).
Outer = bch(inner, (1/2)·(4X)) where inner = bch((1/2)·(4X), Y).
For our small `τ` regime, ‖4X‖+‖Y‖ ≤ 200010·pn·qn·s·‖τ‖ ≤ 2·10⁻⁶, so ‖outer‖ ≤
3·10⁻⁶ << log 2 via two applications of `norm_bch_sub_add_le`. -/
private lemma Z2_lt_log_two_of_tau_small
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    ‖bch (𝕂 := ℝ)
      (bch (𝕂 := ℝ)
        ((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))
        (strangBlock_log ℝ A B (1 - 4 * p) τ))
      ((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))‖ < Real.log 2 := by
  -- Setup: regime hypotheses for X, Y bounds via norm_strangBlock_log_linear.
  have hp_reg := p_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hAB_le hτ_lt
  have hq_reg := q_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hq_le hAB_le hτ_lt
  have hX_bound := norm_strangBlock_log_linear (𝕂 := ℝ) A B p τ hp_reg
  have hY_bound := norm_strangBlock_log_linear (𝕂 := ℝ) A B (1 - 4 * p) τ hq_reg
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ := norm_nonneg _
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  -- Norm equalities for ‖p·τ‖, etc.
  have hpτ_norm : ‖(p * τ : ℝ)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  -- Bound η_p, η_q ≤ pn·s·‖τ‖, qn·s·‖τ‖.
  have hηp_le : ‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    rw [hpτ_norm]
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_pn_τ_nn : 0 ≤ pn * ‖τ‖ := by positivity
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hp_le h_τAB_nn
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_pn_τ_nn
      _ = pn * s * ‖τ‖ := by ring
  have hηq_le : ‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    rw [hqτ_norm]
    have h_τAB_nn : 0 ≤ ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
    have h_qn_τ_nn : 0 ≤ qn * ‖τ‖ := by positivity
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_right hq_le h_τAB_nn
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := mul_le_mul_of_nonneg_left hAB_le h_qn_τ_nn
      _ = qn * s * ‖τ‖ := by ring
  -- ‖X‖ ≤ 40002·pn·s·‖τ‖, ‖Y‖ ≤ 40002·qn·s·‖τ‖.
  have h_X_le : ‖strangBlock_log ℝ A B p τ‖ ≤ 40002 * (pn * s * ‖τ‖) := by
    nlinarith [hX_bound, hηp_le]
  have h_Y_le : ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ ≤ 40002 * (qn * s * ‖τ‖) := by
    nlinarith [hY_bound, hηq_le]
  -- ‖4·X‖ = 4·‖X‖
  have h4_norm : ‖(4 : ℝ)‖ = 4 := by simp
  have h_4X_eq : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ =
                 4 * ‖strangBlock_log ℝ A B p τ‖ := by
    rw [norm_smul, h4_norm]
  -- ‖a‖ = ‖(1/2)·(4X)‖ = (1/2)·4·‖X‖ = 2·‖X‖
  have h_inv_2_norm : ‖((2 : ℝ)⁻¹ : ℝ)‖ = 1 / 2 := by
    rw [norm_inv, RCLike.norm_ofNat]; norm_num
  have h_a_eq : ‖((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))‖ =
                2 * ‖strangBlock_log ℝ A B p τ‖ := by
    rw [norm_smul, h_inv_2_norm, h_4X_eq]; ring
  -- ‖a‖ ≤ 2·40002·pn·s·‖τ‖
  have h_a_le : ‖((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))‖ ≤
                2 * (40002 * (pn * s * ‖τ‖)) := by
    rw [h_a_eq]
    nlinarith [h_X_le, norm_nonneg (strangBlock_log ℝ A B p τ)]
  -- s_inner = ‖a‖+‖b‖ ≤ 2·40002·pn·s·‖τ‖ + 40002·qn·s·‖τ‖ = 40002·(2·pn+qn)·s·‖τ‖
  set sa : ℝ := ‖((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))‖ with hsa_def
  set sb : ℝ := ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ with hsb_def
  have hsa_nn : 0 ≤ sa := by rw [hsa_def]; exact norm_nonneg _
  have hsb_nn : 0 ≤ sb := by rw [hsb_def]; exact norm_nonneg _
  have h_inner_arg_le : sa + sb ≤ 40002 * (2 * pn + qn) * s * ‖τ‖ := by
    have h1 : sa ≤ 2 * (40002 * (pn * s * ‖τ‖)) := h_a_le
    have h2 : sb ≤ 40002 * (qn * s * ‖τ‖) := h_Y_le
    have heq : 2 * (40002 * (pn * s * ‖τ‖)) + 40002 * (qn * s * ‖τ‖) =
               40002 * (2 * pn + qn) * s * ‖τ‖ := by ring
    linarith
  -- 40002·(2pn+qn)·s·‖τ‖ ≤ 40002·3·pn·qn·s·‖τ‖ ≤ 120006·pn·qn·s·‖τ‖.
  have h_2pq_le : 40002 * (2 * pn + qn) ≤ 120006 * pn * qn := by
    have h1 : 2 * pn ≤ 2 * pn * qn := by nlinarith
    have h2 : qn ≤ pn * qn := by nlinarith
    linarith [mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 40002 by norm_num),
              mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 40002 by norm_num)]
  have hs_τ_nn : 0 ≤ s * ‖τ‖ := by positivity
  have h_inner_arg_le' : sa + sb ≤ 120006 * pn * qn * s * ‖τ‖ := by
    have h1 : 40002 * (2 * pn + qn) * (s * ‖τ‖) ≤ 120006 * pn * qn * (s * ‖τ‖) :=
      mul_le_mul_of_nonneg_right h_2pq_le hs_τ_nn
    linarith
  -- 120006·pn·qn·s·‖τ‖ ≤ 120006/10^11 (very small).
  have h_120006_pqs_pos : (0 : ℝ) < 120006 * pn * qn * s := by positivity
  have h_τ_step1 : 120006 * pn * qn * s * ‖τ‖ ≤
                   120006 * pn * qn * s * (1 / (10^11 * pn * qn * s)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hτ_lt) (le_of_lt h_120006_pqs_pos)
  have h_simp1 : 120006 * pn * qn * s * (1 / (10^11 * pn * qn * s)) =
                 120006 / 10^11 := by field_simp
  have h_inner_arg_tiny : sa + sb ≤ 120006 / 10^11 := by linarith
  have h_inner_arg_lt_quarter : sa + sb < 1 / 4 := by
    have : (120006 : ℝ) / 10^11 < 1 / 4 := by norm_num
    linarith
  have h_inner_arg_lt_log2 : sa + sb < Real.log 2 := by
    have : (120006 : ℝ) / 10^11 < Real.log 2 := by
      have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have : (120006 : ℝ) / 10^11 < 0.6931471803 := by norm_num
      linarith
    linarith
  -- Apply norm_bch_sub_add_le to inner.
  set a := (2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ) with ha_def
  set b := strangBlock_log ℝ A B (1 - 4 * p) τ with hb_def
  have ha_norm : ‖a‖ = sa := by rw [ha_def, hsa_def]
  have hb_norm : ‖b‖ = sb := by rw [hb_def, hsb_def]
  have h_ab_lt_log2 : ‖a‖ + ‖b‖ < Real.log 2 := by rw [ha_norm, hb_norm]; exact h_inner_arg_lt_log2
  have h_inner_resid := norm_bch_sub_add_le (𝕂 := ℝ) a b h_ab_lt_log2
  -- Bound ‖inner‖ ≤ ‖a‖+‖b‖ + 3·(‖a‖+‖b‖)²/(2-eˢ).
  -- For ‖a‖+‖b‖ ≤ 1/4, 2-eˢ ≥ 1/2.
  set s_inner : ℝ := ‖a‖ + ‖b‖ with hs_inner_def
  have hs_inner_nn : 0 ≤ s_inner := by rw [hs_inner_def]; positivity
  have hs_inner_eq : s_inner = sa + sb := by rw [hs_inner_def, ha_norm, hb_norm]
  have hs_inner_lt_quarter : s_inner < 1 / 4 := by rw [hs_inner_eq]; exact h_inner_arg_lt_quarter
  have hs_inner_le_one : s_inner ≤ 1 := by linarith
  have h_abs_s_inner : |s_inner| ≤ 1 := by rw [abs_of_nonneg hs_inner_nn]; exact hs_inner_le_one
  -- e^s_inner ≤ 1 + s_inner + s_inner² (from abs bound)
  have h_exp_si_bnd : Real.exp s_inner ≤ 1 + s_inner + s_inner ^ 2 := by
    have habs := Real.abs_exp_sub_one_sub_id_le h_abs_s_inner
    have := (abs_le.mp habs).2
    linarith
  have hs_inner_sq_le : s_inner ^ 2 ≤ s_inner := by
    nlinarith [hs_inner_nn, hs_inner_le_one, sq_nonneg s_inner]
  have h_exp_si_le : Real.exp s_inner ≤ 1 + 2 * s_inner := by linarith
  have h_2_sub_exp_si : 2 - Real.exp s_inner ≥ 1 - 2 * s_inner := by linarith
  have h_one_minus_2si_pos : 1 - 2 * s_inner ≥ 1 / 2 := by linarith
  have h_2_sub_exp_si_pos : 2 - Real.exp s_inner ≥ 1 / 2 := by linarith
  -- 3·s_inner²/(2-e^s_inner) ≤ 6·s_inner²
  have h_resid_bnd_inner : 3 * s_inner^2 / (2 - Real.exp s_inner) ≤ 6 * s_inner^2 := by
    rw [div_le_iff₀ (by linarith : 0 < 2 - Real.exp s_inner)]
    nlinarith [sq_nonneg s_inner, h_2_sub_exp_si, hs_inner_nn]
  have h_inner_resid_le : ‖bch (𝕂 := ℝ) a b - (a + b)‖ ≤ 6 * s_inner^2 := by
    have h_eq_ab : 3 * (‖a‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a‖ + ‖b‖)) =
                   3 * s_inner ^ 2 / (2 - Real.exp s_inner) := by
      rw [hs_inner_def]
    rw [h_eq_ab] at h_inner_resid
    linarith
  -- ‖inner‖ ≤ s_inner + 6·s_inner²
  have h_inner_le : ‖bch (𝕂 := ℝ) a b‖ ≤ s_inner + 6 * s_inner^2 := by
    have h_triangle : ‖bch (𝕂 := ℝ) a b‖ ≤ ‖bch (𝕂 := ℝ) a b - (a + b)‖ + ‖a + b‖ := by
      have h_eq : bch (𝕂 := ℝ) a b = (bch (𝕂 := ℝ) a b - (a + b)) + (a + b) := by abel
      calc ‖bch (𝕂 := ℝ) a b‖ = ‖(bch (𝕂 := ℝ) a b - (a + b)) + (a + b)‖ := by rw [← h_eq]
        _ ≤ ‖bch (𝕂 := ℝ) a b - (a + b)‖ + ‖a + b‖ := norm_add_le _ _
    have h_ab_le : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    rw [hs_inner_def]
    linarith
  -- s_outer = ‖inner‖ + ‖a‖
  set s_outer : ℝ := ‖bch (𝕂 := ℝ) a b‖ + ‖a‖ with hs_outer_def
  have hs_outer_nn : 0 ≤ s_outer := by rw [hs_outer_def]; positivity
  -- s_outer ≤ s_inner + 6·s_inner² + ‖a‖ ≤ s_inner + 6·s_inner² + s_inner = 2·s_inner + 6·s_inner²
  have ha_le_si : ‖a‖ ≤ s_inner := by
    rw [hs_inner_def]; linarith [norm_nonneg b]
  have hs_outer_le : s_outer ≤ 2 * s_inner + 6 * s_inner^2 := by
    rw [hs_outer_def]
    linarith
  -- 2·s_inner + 6·s_inner² ≤ 2·s_inner + (3/2)·s_inner = (7/2)·s_inner (since s_inner ≤ 1/4)
  have hs_inner_le_quarter : s_inner ≤ 1 / 4 := le_of_lt hs_inner_lt_quarter
  have h_6si_sq_le : 6 * s_inner^2 ≤ (3/2) * s_inner := by
    nlinarith [sq_nonneg s_inner, hs_inner_nn, hs_inner_le_quarter]
  have hs_outer_le' : s_outer ≤ (7/2) * s_inner := by linarith
  -- For s_inner ≤ 120006/10^11: s_outer ≤ (7/2)·120006/10^11 < log 2
  have hsi_le_tiny : s_inner ≤ 120006 / 10^11 := by
    rw [hs_inner_eq]; exact h_inner_arg_tiny
  have hs_outer_le_tiny : s_outer ≤ (7/2) * (120006 / 10^11) := by
    have h_mul := mul_le_mul_of_nonneg_left hsi_le_tiny
                    (show (0:ℝ) ≤ 7/2 by norm_num)
    linarith [h_mul]
  have hs_outer_lt_log2 : s_outer < Real.log 2 := by
    have h1 : (7/2 : ℝ) * (120006 / 10^11) < Real.log 2 := by
      have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h2 : (7/2 : ℝ) * (120006 / 10^11) < 0.6931471803 := by norm_num
      linarith
    linarith
  -- s_outer < 1 (sub-condition for outer norm_bch_sub_add_le)
  have hs_outer_le_one : s_outer ≤ 1 := by
    have hlog2_lt : Real.log 2 ≤ 1 := by
      have : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith
    linarith
  have h_abs_so : |s_outer| ≤ 1 := by rw [abs_of_nonneg hs_outer_nn]; exact hs_outer_le_one
  -- Apply norm_bch_sub_add_le to outer.
  have h_outer_sum_lt : ‖bch (𝕂 := ℝ) a b‖ + ‖a‖ < Real.log 2 := by
    rw [← hs_outer_def]; exact hs_outer_lt_log2
  have h_outer_resid := norm_bch_sub_add_le (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a h_outer_sum_lt
  -- Bound 2 - e^s_outer ≥ 1/2 (similar argument).
  have h_exp_so_bnd : Real.exp s_outer ≤ 1 + s_outer + s_outer ^ 2 := by
    have habs := Real.abs_exp_sub_one_sub_id_le h_abs_so
    have := (abs_le.mp habs).2
    linarith
  have hs_outer_sq_le : s_outer ^ 2 ≤ s_outer := by
    nlinarith [hs_outer_nn, hs_outer_le_one, sq_nonneg s_outer]
  have h_exp_so_le : Real.exp s_outer ≤ 1 + 2 * s_outer := by linarith
  -- For s_outer ≤ 1/4: 2-e^s_outer ≥ 1/2.
  have hs_outer_le_quarter : s_outer ≤ 1 / 4 := by
    have : (7/2 : ℝ) * (120006 / 10^11) ≤ 1 / 4 := by norm_num
    linarith
  have h_2_sub_exp_so_pos : 2 - Real.exp s_outer ≥ 1 / 2 := by linarith
  -- 3·s_outer²/(2-e^s_outer) ≤ 6·s_outer²
  have h_resid_bnd_outer : 3 * s_outer^2 / (2 - Real.exp s_outer) ≤ 6 * s_outer^2 := by
    rw [div_le_iff₀ (by linarith : 0 < 2 - Real.exp s_outer)]
    nlinarith [sq_nonneg s_outer, h_2_sub_exp_so_pos, hs_outer_nn]
  have h_outer_resid_le : ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a -
                             (bch (𝕂 := ℝ) a b + a)‖ ≤ 6 * s_outer^2 := by
    have h_eq_ab : 3 * (‖bch (𝕂 := ℝ) a b‖ + ‖a‖) ^ 2 /
                   (2 - Real.exp (‖bch (𝕂 := ℝ) a b‖ + ‖a‖)) =
                   3 * s_outer ^ 2 / (2 - Real.exp s_outer) := by rw [hs_outer_def]
    rw [h_eq_ab] at h_outer_resid
    linarith
  -- ‖outer‖ ≤ s_outer + 6·s_outer²
  have h_outer_le : ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a‖ ≤ s_outer + 6 * s_outer^2 := by
    have h_triangle : ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a‖ ≤
        ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a - (bch (𝕂 := ℝ) a b + a)‖ +
        ‖bch (𝕂 := ℝ) a b + a‖ := by
      have h_eq : bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a =
          (bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a - (bch (𝕂 := ℝ) a b + a)) +
          (bch (𝕂 := ℝ) a b + a) := by abel
      calc ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a‖
          = ‖(bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a - (bch (𝕂 := ℝ) a b + a)) +
              (bch (𝕂 := ℝ) a b + a)‖ := by rw [← h_eq]
        _ ≤ ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a - (bch (𝕂 := ℝ) a b + a)‖ +
            ‖bch (𝕂 := ℝ) a b + a‖ := norm_add_le _ _
    have h_sum_le : ‖bch (𝕂 := ℝ) a b + a‖ ≤ s_outer := by
      rw [hs_outer_def]; exact norm_add_le _ _
    linarith
  -- s_outer + 6·s_outer² ≤ s_outer + (3/2)·s_outer = (5/2)·s_outer
  have h_6so_sq_le : 6 * s_outer^2 ≤ (3/2) * s_outer := by
    nlinarith [sq_nonneg s_outer, hs_outer_nn, hs_outer_le_quarter]
  have h_outer_le' : ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a‖ ≤ (5/2) * s_outer := by linarith
  -- (5/2)·s_outer ≤ (5/2)·(7/2)·(120006/10^11) = 35/4 · 120006/10^11 < log 2
  have h_final : (5/2) * s_outer < Real.log 2 := by
    have h1 : (5/2 : ℝ) * s_outer ≤ (5/2 : ℝ) * ((7/2) * (120006 / 10^11)) := by
      nlinarith [hs_outer_le_tiny]
    have h2 : (5/2 : ℝ) * ((7/2) * (120006 / 10^11)) < Real.log 2 := by
      have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hb : (5/2 : ℝ) * ((7/2) * (120006 / 10^11)) < 0.6931471803 := by norm_num
      linarith
    linarith
  -- The goal expression matches `‖bch ℝ (bch ℝ a b) a‖`.
  have h_goal_eq : ‖bch (𝕂 := ℝ)
      (bch (𝕂 := ℝ)
        ((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))
        (strangBlock_log ℝ A B (1 - 4 * p) τ))
      ((2 : ℝ)⁻¹ • ((4 : ℝ) • strangBlock_log ℝ A B p τ))‖ =
      ‖bch (𝕂 := ℝ) (bch (𝕂 := ℝ) a b) a‖ := by rw [ha_def, hb_def]
  rw [h_goal_eq]
  linarith

/-! ### Foundational bounds for τ⁶ assembly

A handful of `private` helpers that establish polynomial bounds on the
norm-quantities appearing in `suzuki5_bch_sub_R5_RHS` (the under-regime
bound), in terms of `pn = ‖p‖+1`, `qn = ‖1-4p‖+1`, `s = ‖A‖+‖B‖+1`.

For `‖τ‖ < 1/(10¹¹·pn·qn·s)`:
* `‖(p·τ)·A‖ + ‖(p·τ)·B‖ ≤ pn·s·‖τ‖`
* `‖((1-4p)·τ)·A‖ + ‖((1-4p)·τ)·B‖ ≤ qn·s·‖τ‖`
* `‖(4·p·τ)·(A+B)‖ ≤ 4·pn·s·‖τ‖`
* `‖((1-4p)·τ)·(A+B)‖ ≤ qn·s·‖τ‖`
* per-block residual `D` ≤ `5·10⁸·pn⁵·qn⁵·s⁵·‖τ‖³`

These feed into the per-term bounds for the τ⁶ assembly. -/

set_option maxHeartbeats 2000000 in
/-- Per-block residual norm bound: combining both blocks gives
`D ≤ 5·10⁸·pn⁵·qn⁵·s⁵·‖τ‖³`. -/
private lemma D_bound_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    ‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
      ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
        (((1 - 4 * p) * τ : ℝ)) • (A + B)‖ ≤
      5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  -- Regime hypotheses for slice 4 bound.
  have hp_reg := p_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hAB_le hτ_lt
  have hq_reg := q_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hq_le hAB_le hτ_lt
  -- Apply the slice 4 bound: ‖sb_log - (cτ)·(A+B)‖ ≤ η^3 + 10^7·η^5.
  have hp_resid := norm_strangBlock_log_sub_linear_le (𝕂 := ℝ) A B p τ hp_reg
  have hq_resid := norm_strangBlock_log_sub_linear_le (𝕂 := ℝ) A B (1 - 4 * p) τ hq_reg
  -- η_p = ‖p·τ‖·(‖A‖+‖B‖) ≤ pn·s·‖τ‖
  have hpτ_norm : ‖(p * τ : ℝ)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ := norm_nonneg _
  have hηp_le : ‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    rw [hpτ_norm]
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hp_le; positivity
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = pn * s * ‖τ‖ := by ring
  have hηq_le : ‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    rw [hqτ_norm]
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hq_le; positivity
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = qn * s * ‖τ‖ := by ring
  -- Bound η_p^3, η_p^5 by polynomials in pn, s, |τ|.
  have hηp_nn : 0 ≤ ‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖) := by positivity
  have hηq_nn : 0 ≤ ‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖) := by positivity
  have hpnst_nn : 0 ≤ pn * s * ‖τ‖ := by positivity
  have hqnst_nn : 0 ≤ qn * s * ‖τ‖ := by positivity
  -- Derive ‖τ‖ ≤ 1.
  have h_pqs_ge : (1 : ℝ) ≤ pn * qn * s := by
    have : (1 : ℝ) ≤ pn * qn := by nlinarith
    nlinarith
  have h11pqs_ge : (10^11 : ℝ) ≤ 10^11 * pn * qn * s := by nlinarith
  have hδ_le_one : 1 / (10^11 * pn * qn * s) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 10^11 * pn * qn * s := by linarith
    have h2 : (0 : ℝ) < 10^11 * pn * qn * s := by linarith
    calc 1 / (10^11 * pn * qn * s) ≤ 1 / 1 :=
          one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) h1
      _ = 1 := by norm_num
  have hτ_le_one : ‖τ‖ ≤ 1 := by linarith
  -- Bounds on η^3, η^5 via pow_le_pow_left₀ + |τ|^5 ≤ |τ|^3.
  have hτ5_le_3 : ‖τ‖ ^ 5 ≤ ‖τ‖ ^ 3 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 3 ≤ 5)
  have hτ3_nn : (0 : ℝ) ≤ ‖τ‖ ^ 3 := by positivity
  -- p-block residual bound: η_p^3 + 10^7·η_p^5 ≤ (1+10^7)·pn^5·s^5·|τ|^3
  have hp_resid_pol :
      (‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 3 +
        10000000 * (‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 5 ≤
      (1 + 10000000) * pn^5 * s^5 * ‖τ‖^3 := by
    have h_pow3 : (‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 3 ≤ (pn * s * ‖τ‖) ^ 3 :=
      pow_le_pow_left₀ hηp_nn hηp_le 3
    have h_pow5 : (‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 5 ≤ (pn * s * ‖τ‖) ^ 5 :=
      pow_le_pow_left₀ hηp_nn hηp_le 5
    have hexp3 : (pn * s * ‖τ‖)^3 = pn^3 * s^3 * ‖τ‖^3 := by ring
    have hexp5 : (pn * s * ‖τ‖)^5 = pn^5 * s^5 * ‖τ‖^5 := by ring
    have hpn3_le_5 : pn^3 ≤ pn^5 := pow_le_pow_right₀ hpn_ge (by norm_num : 3 ≤ 5)
    have hs3_le_5 : s^3 ≤ s^5 := pow_le_pow_right₀ hs_ge (by norm_num : 3 ≤ 5)
    have h_pn5s5_nn : 0 ≤ pn^5 * s^5 := by positivity
    calc (‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 3 +
          10000000 * (‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 5
        ≤ (pn * s * ‖τ‖) ^ 3 + 10000000 * (pn * s * ‖τ‖) ^ 5 := by
          have h10nn : (0:ℝ) ≤ 10000000 := by norm_num
          linarith [mul_le_mul_of_nonneg_left h_pow5 h10nn]
      _ = pn^3 * s^3 * ‖τ‖^3 + 10000000 * (pn^5 * s^5 * ‖τ‖^5) := by rw [hexp3, hexp5]
      _ ≤ pn^5 * s^5 * ‖τ‖^3 + 10000000 * (pn^5 * s^5 * ‖τ‖^3) := by
          have h1 : pn^3 * s^3 * ‖τ‖^3 ≤ pn^5 * s^5 * ‖τ‖^3 := by
            have ha : pn^3 * s^3 ≤ pn^5 * s^5 := by
              have hh1 : pn^3 * s^3 ≤ pn^5 * s^3 :=
                mul_le_mul_of_nonneg_right hpn3_le_5 (by positivity)
              have hh2 : pn^5 * s^3 ≤ pn^5 * s^5 :=
                mul_le_mul_of_nonneg_left hs3_le_5 (by positivity)
              linarith
            exact mul_le_mul_of_nonneg_right ha hτ3_nn
          have h2 : 10000000 * (pn^5 * s^5 * ‖τ‖^5) ≤ 10000000 * (pn^5 * s^5 * ‖τ‖^3) := by
            have hh : pn^5 * s^5 * ‖τ‖^5 ≤ pn^5 * s^5 * ‖τ‖^3 :=
              mul_le_mul_of_nonneg_left hτ5_le_3 h_pn5s5_nn
            linarith
          linarith
      _ = (1 + 10000000) * (pn^5 * s^5 * ‖τ‖^3) := by ring
      _ = (1 + 10000000) * pn^5 * s^5 * ‖τ‖^3 := by ring
  -- q-block residual bound (analogous)
  have hq_resid_pol :
      (‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 3 +
        10000000 * (‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 5 ≤
      (1 + 10000000) * qn^5 * s^5 * ‖τ‖^3 := by
    have h_pow3 : (‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 3 ≤ (qn * s * ‖τ‖) ^ 3 :=
      pow_le_pow_left₀ hηq_nn hηq_le 3
    have h_pow5 : (‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 5 ≤ (qn * s * ‖τ‖) ^ 5 :=
      pow_le_pow_left₀ hηq_nn hηq_le 5
    have hexp3 : (qn * s * ‖τ‖)^3 = qn^3 * s^3 * ‖τ‖^3 := by ring
    have hexp5 : (qn * s * ‖τ‖)^5 = qn^5 * s^5 * ‖τ‖^5 := by ring
    have hqn3_le_5 : qn^3 ≤ qn^5 := pow_le_pow_right₀ hqn_ge (by norm_num : 3 ≤ 5)
    have hs3_le_5 : s^3 ≤ s^5 := pow_le_pow_right₀ hs_ge (by norm_num : 3 ≤ 5)
    have h_qn5s5_nn : 0 ≤ qn^5 * s^5 := by positivity
    calc (‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 3 +
          10000000 * (‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ^ 5
        ≤ (qn * s * ‖τ‖) ^ 3 + 10000000 * (qn * s * ‖τ‖) ^ 5 := by
          have h10nn : (0:ℝ) ≤ 10000000 := by norm_num
          linarith [mul_le_mul_of_nonneg_left h_pow5 h10nn]
      _ = qn^3 * s^3 * ‖τ‖^3 + 10000000 * (qn^5 * s^5 * ‖τ‖^5) := by rw [hexp3, hexp5]
      _ ≤ qn^5 * s^5 * ‖τ‖^3 + 10000000 * (qn^5 * s^5 * ‖τ‖^3) := by
          have h1 : qn^3 * s^3 * ‖τ‖^3 ≤ qn^5 * s^5 * ‖τ‖^3 := by
            have ha : qn^3 * s^3 ≤ qn^5 * s^5 := by
              have hh1 : qn^3 * s^3 ≤ qn^5 * s^3 :=
                mul_le_mul_of_nonneg_right hqn3_le_5 (by positivity)
              have hh2 : qn^5 * s^3 ≤ qn^5 * s^5 :=
                mul_le_mul_of_nonneg_left hs3_le_5 (by positivity)
              linarith
            exact mul_le_mul_of_nonneg_right ha hτ3_nn
          have h2 : 10000000 * (qn^5 * s^5 * ‖τ‖^5) ≤ 10000000 * (qn^5 * s^5 * ‖τ‖^3) := by
            have hh : qn^5 * s^5 * ‖τ‖^5 ≤ qn^5 * s^5 * ‖τ‖^3 :=
              mul_le_mul_of_nonneg_left hτ5_le_3 h_qn5s5_nn
            linarith
          linarith
      _ = (1 + 10000000) * (qn^5 * s^5 * ‖τ‖^3) := by ring
      _ = (1 + 10000000) * qn^5 * s^5 * ‖τ‖^3 := by ring
  -- Now bound ‖4·X - (4pτ)·(A+B)‖ = 4·‖X - (pτ)·(A+B)‖.
  have h4_eq : (4 * p * τ : ℝ) = 4 * (p * τ) := by ring
  have hsmul_decomp :
      (4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B) =
        (4 : ℝ) • (strangBlock_log ℝ A B p τ - (p * τ : ℝ) • (A + B)) := by
    rw [h4_eq]
    rw [show (4 * (p * τ) : ℝ) • (A + B) = (4 : ℝ) • ((p * τ : ℝ) • (A + B)) from by
      rw [smul_smul]]
    rw [smul_sub]
  have h4_norm : ‖(4 : ℝ)‖ = 4 := by simp
  have h4smul_eq :
      ‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ =
      4 * ‖strangBlock_log ℝ A B p τ - (p * τ : ℝ) • (A + B)‖ := by
    rw [hsmul_decomp, norm_smul, h4_norm]
  -- Apply 4·(η_p^3 + 10^7·η_p^5) ≤ 4·(1+10^7)·pn^5·s^5·|τ|^3
  have h_step_p : ‖strangBlock_log ℝ A B p τ - (p * τ : ℝ) • (A + B)‖ ≤
                  (1 + 10000000) * pn^5 * s^5 * ‖τ‖^3 := by
    linarith [hp_resid, hp_resid_pol]
  have hp_resid_4 :
      ‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ ≤
        4 * ((1 + 10000000) * pn^5 * s^5 * ‖τ‖^3) := by
    rw [h4smul_eq]
    exact mul_le_mul_of_nonneg_left h_step_p (by norm_num : (0:ℝ) ≤ 4)
  -- q-block residual bound (analogous, no factor of 4)
  have hq_resid_bnd :
      ‖strangBlock_log ℝ A B (1 - 4 * p) τ - (((1 - 4 * p) * τ : ℝ)) • (A + B)‖ ≤
        (1 + 10000000) * qn^5 * s^5 * ‖τ‖^3 := by linarith [hq_resid, hq_resid_pol]
  -- Combine: 4·(1+10⁷)·pn⁵·s⁵·|τ|³ + (1+10⁷)·qn⁵·s⁵·|τ|³ ≤ 5·10⁸·pn⁵·qn⁵·s⁵·|τ|³
  have h_qn5_ge : (1 : ℝ) ≤ qn^5 := one_le_pow₀ hqn_ge
  have h_pn5_ge : (1 : ℝ) ≤ pn^5 := one_le_pow₀ hpn_ge
  have h_pn5_nn : (0 : ℝ) ≤ pn^5 := by positivity
  have h_qn5_nn : (0 : ℝ) ≤ qn^5 := by positivity
  have hp5_le : pn^5 ≤ pn^5 * qn^5 := by
    have := mul_le_mul_of_nonneg_left h_qn5_ge h_pn5_nn
    linarith
  have hq5_le : qn^5 ≤ pn^5 * qn^5 := by
    have := mul_le_mul_of_nonneg_right h_pn5_ge h_qn5_nn
    linarith
  have hs5_τ3_nn : 0 ≤ s^5 * ‖τ‖^3 := by positivity
  have h_combine : 4 * ((1 + 10000000) * pn^5 * s^5 * ‖τ‖^3) +
                   (1 + 10000000) * qn^5 * s^5 * ‖τ‖^3 ≤
                   5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3 := by
    -- Use pn^5 ≤ pn^5·qn^5 and qn^5 ≤ pn^5·qn^5 to bound everything by pn^5·qn^5.
    have h_a : pn^5 * s^5 * ‖τ‖^3 ≤ pn^5 * qn^5 * s^5 * ‖τ‖^3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp5_le (by positivity : (0:ℝ) ≤ s^5))
        (by positivity : (0:ℝ) ≤ ‖τ‖^3)
    have h_b : qn^5 * s^5 * ‖τ‖^3 ≤ pn^5 * qn^5 * s^5 * ‖τ‖^3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq5_le (by positivity : (0:ℝ) ≤ s^5))
        (by positivity : (0:ℝ) ≤ ‖τ‖^3)
    have hpq5s5τ3_nn : 0 ≤ pn^5 * qn^5 * s^5 * ‖τ‖^3 := by positivity
    nlinarith [h_a, h_b, hpq5s5τ3_nn]
  linarith [hp_resid_4, hq_resid_bnd, h_combine]

/-! ### Per-term polynomial bounds for `suzuki5_bch_sub_R5_RHS`

The under-regime bound is a sum of 7 summands (T1a, T1b, T1c, T2a, T2b, T2c, T3)
in `suzuki5_bch_sub_R5_RHS`. Each is bounded by an explicit polynomial in
`pn`, `qn`, `s` times `‖τ‖^6`. The polynomial helpers below isolate these
bounds so the kernel can typecheck them independently. -/

set_option maxHeartbeats 2000000 in
/-- T1 bound: bounds T1a + T1b + T1c in `suzuki5_bch_sub_R5_RHS`. -/
private lemma RHS_T1_le_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    4 * (1000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) +
        1000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 +
        1000000000 * (‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                      ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖) ^ 7 ≤
      (4 * 10^9 * pn^7 * s^7 + 10^9 * qn^7 * s^7 +
       10^9 * 40002^7 * (4 * pn + qn)^7 * s^7) * ‖τ‖^6 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  -- Derive ‖τ‖ ≤ 1 from the regime hypothesis.
  have h_pqs_ge : (1 : ℝ) ≤ pn * qn * s := by
    have : (1 : ℝ) ≤ pn * qn := by nlinarith
    nlinarith
  have h11pqs_ge : (1 : ℝ) ≤ 10^11 * pn * qn * s := by nlinarith
  have hδ_le_one : 1 / (10^11 * pn * qn * s) ≤ 1 := by
    have h2 : (0 : ℝ) < 10^11 * pn * qn * s := by linarith
    calc 1 / (10^11 * pn * qn * s) ≤ 1 / 1 :=
          one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) h11pqs_ge
      _ = 1 := by norm_num
  have hτ_le_one : ‖τ‖ ≤ 1 := by linarith
  have hτ7_le_6 : ‖τ‖ ^ 7 ≤ ‖τ‖ ^ 6 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 6 ≤ 7)
  -- Norm equalities.
  have hpτ_norm : ‖(p * τ : ℝ)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  have hsmul_pτA : ‖(p * τ) • A‖ = ‖(p * τ : ℝ)‖ * ‖A‖ := norm_smul _ _
  have hsmul_pτB : ‖(p * τ) • B‖ = ‖(p * τ : ℝ)‖ * ‖B‖ := norm_smul _ _
  have hsmul_qτA : ‖((1 - 4 * p) * τ) • A‖ = ‖((1 - 4 * p) * τ : ℝ)‖ * ‖A‖ := norm_smul _ _
  have hsmul_qτB : ‖((1 - 4 * p) * τ) • B‖ = ‖((1 - 4 * p) * τ : ℝ)‖ * ‖B‖ := norm_smul _ _
  have hηp_eq : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ = ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_pτA, hsmul_pτB, hpτ_norm]; ring
  have hηq_eq : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ =
                ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_qτA, hsmul_qτB, hqτ_norm]; ring
  -- η_p, η_q bounds.
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ := norm_nonneg _
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have hηp_le : ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hp_le; positivity
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = pn * s * ‖τ‖ := by ring
  have hηq_le : ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hq_le; positivity
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = qn * s * ‖τ‖ := by ring
  have hηp_nn : 0 ≤ ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
  have hηq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
  have hpnst_nn : 0 ≤ pn * s * ‖τ‖ := by positivity
  have hqnst_nn : 0 ≤ qn * s * ‖τ‖ := by positivity
  -- Strang block linear bounds (need η_p, η_q < 1/4 hypothesis).
  have hp_reg := p_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hAB_le hτ_lt
  have hq_reg := q_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hq_le hAB_le hτ_lt
  have hsbp := norm_strangBlock_log_linear (𝕂 := ℝ) A B p τ hp_reg
  have hsbq := norm_strangBlock_log_linear (𝕂 := ℝ) A B (1 - 4 * p) τ hq_reg
  have hsbp_bnd : ‖strangBlock_log ℝ A B p τ‖ ≤ 40002 * (pn * s * ‖τ‖) := by
    have h1 : 40002 * (‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ≤ 40002 * (pn * s * ‖τ‖) := by
      have : ‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by rw [hpτ_norm]; exact hηp_le
      linarith
    linarith
  have hsbq_bnd : ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ ≤ 40002 * (qn * s * ‖τ‖) := by
    have h1 : 40002 * (‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖)) ≤ 40002 * (qn * s * ‖τ‖) := by
      have : ‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by rw [hqτ_norm]; exact hηq_le
      linarith
    linarith
  have h4_norm : ‖(4 : ℝ)‖ = 4 := by simp
  have h4smul : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ = 4 * ‖strangBlock_log ℝ A B p τ‖ := by
    rw [norm_smul, h4_norm]
  have h4sbp_bnd : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ ≤ 4 * (40002 * (pn * s * ‖τ‖)) := by
    rw [h4smul]
    exact mul_le_mul_of_nonneg_left hsbp_bnd (by norm_num : (0:ℝ) ≤ 4)
  have hL_bnd : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ ≤
                40002 * (4 * pn + qn) * s * ‖τ‖ := by
    have heq : 4 * (40002 * (pn * s * ‖τ‖)) + 40002 * (qn * s * ‖τ‖) =
               40002 * (4 * pn + qn) * s * ‖τ‖ := by ring
    linarith [h4sbp_bnd, hsbq_bnd]
  have hL_nn : 0 ≤ ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                   ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ := by positivity
  -- Term 1a bound.
  have hT1a : 4 * (1000000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 7) ≤
              (4 * 10^9 * pn^7 * s^7) * ‖τ‖^6 := by
    rw [hηp_eq]
    have h_pow7 : (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^7 ≤ (pn * s * ‖τ‖)^7 :=
      pow_le_pow_left₀ hηp_nn hηp_le 7
    have h_pow7_eq : (pn * s * ‖τ‖)^7 = pn^7 * s^7 * ‖τ‖^7 := by ring
    have h_τ_step : pn^7 * s^7 * ‖τ‖^7 ≤ pn^7 * s^7 * ‖τ‖^6 :=
      mul_le_mul_of_nonneg_left hτ7_le_6 (by positivity)
    have h_pre : 4 * (1000000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^7) ≤
                 4 * (1000000000 * (pn * s * ‖τ‖)^7) := by
      have h_step : (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^7 ≤ (pn * s * ‖τ‖)^7 := h_pow7
      have h_step2 : 1000000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^7 ≤
                     1000000000 * (pn * s * ‖τ‖)^7 :=
        mul_le_mul_of_nonneg_left h_step (by norm_num)
      linarith
    have h_chain : 4 * (1000000000 * (pn * s * ‖τ‖)^7) =
                   (4 * 10^9 * pn^7 * s^7) * ‖τ‖^7 := by rw [h_pow7_eq]; ring
    have h_τ7_to_6 : (4 * 10^9 * pn^7 * s^7) * ‖τ‖^7 ≤ (4 * 10^9 * pn^7 * s^7) * ‖τ‖^6 :=
      mul_le_mul_of_nonneg_left hτ7_le_6 (by positivity)
    linarith [h_pre, h_chain, h_τ7_to_6]
  -- Term 1b bound.
  have hT1b : 1000000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 7 ≤
              (10^9 * qn^7 * s^7) * ‖τ‖^6 := by
    rw [hηq_eq]
    have h_pow7 : (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^7 ≤ (qn * s * ‖τ‖)^7 :=
      pow_le_pow_left₀ hηq_nn hηq_le 7
    have h_pow7_eq : (qn * s * ‖τ‖)^7 = qn^7 * s^7 * ‖τ‖^7 := by ring
    have h_pre : 1000000000 * (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^7 ≤
                 1000000000 * (qn * s * ‖τ‖)^7 :=
      mul_le_mul_of_nonneg_left h_pow7 (by norm_num)
    have h_chain : 1000000000 * (qn * s * ‖τ‖)^7 = (10^9 * qn^7 * s^7) * ‖τ‖^7 := by
      rw [h_pow7_eq]; ring
    have h_τ7_to_6 : (10^9 * qn^7 * s^7) * ‖τ‖^7 ≤ (10^9 * qn^7 * s^7) * ‖τ‖^6 :=
      mul_le_mul_of_nonneg_left hτ7_le_6 (by positivity)
    linarith [h_pre, h_chain, h_τ7_to_6]
  -- Term 1c bound.
  have hT1c : 1000000000 * (‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                            ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖) ^ 7 ≤
              (10^9 * 40002^7 * (4 * pn + qn)^7 * s^7) * ‖τ‖^6 := by
    have h_pow7 : (‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                   ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^7 ≤
                  (40002 * (4 * pn + qn) * s * ‖τ‖)^7 :=
      pow_le_pow_left₀ hL_nn hL_bnd 7
    have h_pow7_eq : (40002 * (4 * pn + qn) * s * ‖τ‖)^7 =
                     40002^7 * (4 * pn + qn)^7 * s^7 * ‖τ‖^7 := by ring
    have h_pre : 1000000000 * (‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                               ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^7 ≤
                 1000000000 * (40002 * (4 * pn + qn) * s * ‖τ‖)^7 :=
      mul_le_mul_of_nonneg_left h_pow7 (by norm_num)
    have h_chain : 1000000000 * (40002 * (4 * pn + qn) * s * ‖τ‖)^7 =
                   (10^9 * 40002^7 * (4 * pn + qn)^7 * s^7) * ‖τ‖^7 := by
      rw [h_pow7_eq]; ring
    have h_τ7_to_6 : (10^9 * 40002^7 * (4 * pn + qn)^7 * s^7) * ‖τ‖^7 ≤
                     (10^9 * 40002^7 * (4 * pn + qn)^7 * s^7) * ‖τ‖^6 :=
      mul_le_mul_of_nonneg_left hτ7_le_6 (by positivity)
    linarith [h_pre, h_chain, h_τ7_to_6]
  linarith [hT1a, hT1b, hT1c]

/-- Helper: derive `‖τ‖ ≤ 1` from the regime hypothesis. -/
private lemma tau_le_one_aux (τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) : ‖τ‖ ≤ 1 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have h_pqs_ge : (1 : ℝ) ≤ pn * qn * s := by
    have : (1 : ℝ) ≤ pn * qn := by nlinarith
    nlinarith
  have h11pqs_ge : (1 : ℝ) ≤ 10^11 * pn * qn * s := by nlinarith
  have hδ_le_one : 1 / (10^11 * pn * qn * s) ≤ 1 := by
    have h2 : (0 : ℝ) < 10^11 * pn * qn * s := by linarith
    calc 1 / (10^11 * pn * qn * s) ≤ 1 / 1 :=
          one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) h11pqs_ge
      _ = 1 := by norm_num
  linarith

set_option maxHeartbeats 2000000 in
/-- T2a bound: `(3/2)·N·D² ≤ K_T2a·‖τ‖⁶`. -/
private lemma RHS_T2a_le_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    (3 / 2 : ℝ) *
        ((‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖) *
         (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
          ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
            (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2) ≤
      (2 * 10^18 * pn^11 * qn^11 * s^11) * ‖τ‖^6 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hτ_le_one : ‖τ‖ ≤ 1 := tau_le_one_aux τ pn qn s hpn_ge hqn_ge hs_ge hτ_lt
  have hτ7_le_6 : ‖τ‖ ^ 7 ≤ ‖τ‖ ^ 6 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 6 ≤ 7)
  -- Bound N ≤ 5·pn·qn·s·|τ|.
  have hAB_norm_le : ‖A + B‖ ≤ s := le_trans (norm_add_le _ _) hAB_le
  have h4_norm : ‖(4 : ℝ)‖ = 4 := by simp
  have h4pτ_eq : (4 * p * τ : ℝ) = 4 * (p * τ) := by ring
  have h4pτ_norm : ‖(4 * p * τ : ℝ)‖ = 4 * ‖p‖ * ‖τ‖ := by
    rw [h4pτ_eq, norm_mul, h4_norm, norm_mul]; ring
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  have h4pτAB_le : ‖((4 * p * τ : ℝ)) • (A + B)‖ ≤ 4 * pn * s * ‖τ‖ := by
    rw [norm_smul, h4pτ_norm]
    calc 4 * ‖p‖ * ‖τ‖ * ‖A + B‖
        = (4 * ‖p‖) * (‖τ‖ * ‖A + B‖) := by ring
      _ ≤ (4 * pn) * (‖τ‖ * ‖A + B‖) := by
          apply mul_le_mul_of_nonneg_right (by linarith); positivity
      _ = 4 * pn * ‖τ‖ * ‖A + B‖ := by ring
      _ ≤ 4 * pn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_norm_le; positivity
      _ = 4 * pn * s * ‖τ‖ := by ring
  have hqτAB_le : ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ ≤ qn * s * ‖τ‖ := by
    rw [norm_smul, hqτ_norm]
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * ‖A + B‖
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * ‖A + B‖) := by ring
      _ ≤ qn * (‖τ‖ * ‖A + B‖) := by
          apply mul_le_mul_of_nonneg_right hq_le; positivity
      _ = qn * ‖τ‖ * ‖A + B‖ := by ring
      _ ≤ qn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_norm_le; positivity
      _ = qn * s * ‖τ‖ := by ring
  have hN_nn : 0 ≤ ‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ := by
    positivity
  have hN_le' : ‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ ≤
                5 * pn * qn * s * ‖τ‖ := by
    have h4pq_le : 4 * pn + qn ≤ 5 * pn * qn := by nlinarith
    have hsτ_nn : 0 ≤ s * ‖τ‖ := by positivity
    have h_step : 4 * pn * s * ‖τ‖ + qn * s * ‖τ‖ = (4 * pn + qn) * s * ‖τ‖ := by ring
    have hh : (4 * pn + qn) * s * ‖τ‖ ≤ 5 * pn * qn * s * ‖τ‖ := by
      have : (4 * pn + qn) * (s * ‖τ‖) ≤ (5 * pn * qn) * (s * ‖τ‖) :=
        mul_le_mul_of_nonneg_right h4pq_le hsτ_nn
      linarith
    linarith [h4pτAB_le, hqτAB_le]
  -- Bound D via D_bound_aux.
  have hD_le := D_bound_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hD_nn : 0 ≤ ‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                   ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                     (((1 - 4 * p) * τ : ℝ)) • (A + B)‖ := by positivity
  -- D² bound.
  have hD2_le :
      (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
        ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
          (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2 ≤
      (5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3)^2 :=
    pow_le_pow_left₀ hD_nn hD_le 2
  have hD2_eq : (5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3)^2 =
                25 * 10^16 * pn^10 * qn^10 * s^10 * ‖τ‖^6 := by ring
  -- N · D^2
  have h_step1 :
      (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖) *
      (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
        ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
          (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2 ≤
      (5 * pn * qn * s * ‖τ‖) * (25 * 10^16 * pn^10 * qn^10 * s^10 * ‖τ‖^6) := by
    have hD2_nn : 0 ≤ (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                       ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                         (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2 := by positivity
    have h5pqsn_nn : 0 ≤ 5 * pn * qn * s * ‖τ‖ := by positivity
    have hsq_pol_le : (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                         ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                           (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2 ≤
                      25 * 10^16 * pn^10 * qn^10 * s^10 * ‖τ‖^6 := by
      have := hD2_le
      linarith [hD2_eq]
    calc (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖) *
         (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
           ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
             (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2
        ≤ (5 * pn * qn * s * ‖τ‖) *
          (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
            ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
              (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2 :=
          mul_le_mul_of_nonneg_right hN_le' hD2_nn
      _ ≤ (5 * pn * qn * s * ‖τ‖) * (25 * 10^16 * pn^10 * qn^10 * s^10 * ‖τ‖^6) :=
          mul_le_mul_of_nonneg_left hsq_pol_le h5pqsn_nn
  have h_chain : (5 * pn * qn * s * ‖τ‖) * (25 * 10^16 * pn^10 * qn^10 * s^10 * ‖τ‖^6) =
                 (125 * 10^16 * pn^11 * qn^11 * s^11) * ‖τ‖^7 := by ring
  -- Multiply by (3/2)
  have h_step2 : (3 / 2 : ℝ) *
      ((‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖) *
       (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
        ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
          (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 2) ≤
      (3 / 2 : ℝ) * ((5 * pn * qn * s * ‖τ‖) *
        (25 * 10^16 * pn^10 * qn^10 * s^10 * ‖τ‖^6)) :=
    mul_le_mul_of_nonneg_left h_step1 (by norm_num : (0:ℝ) ≤ 3/2)
  -- Compose to K·|τ|^7 ≤ K·|τ|^6
  have h_final_eq : (3 / 2 : ℝ) * ((5 * pn * qn * s * ‖τ‖) *
                    (25 * 10^16 * pn^10 * qn^10 * s^10 * ‖τ‖^6)) =
                    ((3 / 2 : ℝ) * 125 * 10^16 * pn^11 * qn^11 * s^11) * ‖τ‖^7 := by ring
  have h_τ7_to_6 : ((3 / 2 : ℝ) * 125 * 10^16 * pn^11 * qn^11 * s^11) * ‖τ‖^7 ≤
                   ((3 / 2 : ℝ) * 125 * 10^16 * pn^11 * qn^11 * s^11) * ‖τ‖^6 :=
    mul_le_mul_of_nonneg_left hτ7_le_6 (by positivity)
  have h_const_lift : ((3 / 2 : ℝ) * 125 * 10^16 * pn^11 * qn^11 * s^11) * ‖τ‖^6 ≤
                      (2 * 10^18 * pn^11 * qn^11 * s^11) * ‖τ‖^6 := by
    have hpqsτ_nn : 0 ≤ pn^11 * qn^11 * s^11 * ‖τ‖^6 := by positivity
    have h_c_le : ((3 / 2 : ℝ) * 125 * 10^16 : ℝ) ≤ 2 * 10^18 := by norm_num
    nlinarith [h_c_le, hpqsτ_nn]
  linarith [h_step2, h_final_eq, h_τ7_to_6, h_const_lift]

set_option maxHeartbeats 1000000 in
/-- T2b bound: `(1/2)·D³ ≤ K_T2b·‖τ‖⁶`. -/
private lemma RHS_T2b_le_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    (1 / 2 : ℝ) *
        (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
         ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
           (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 3 ≤
      (10^26 * pn^15 * qn^15 * s^15) * ‖τ‖^6 := by
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hτ_le_one : ‖τ‖ ≤ 1 := tau_le_one_aux τ pn qn s hpn_ge hqn_ge hs_ge hτ_lt
  have hτ9_le_6 : ‖τ‖ ^ 9 ≤ ‖τ‖ ^ 6 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 6 ≤ 9)
  have hD_le := D_bound_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hD_nn : 0 ≤ ‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                   ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                     (((1 - 4 * p) * τ : ℝ)) • (A + B)‖ := by positivity
  have hD3_le :
      (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
        ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
          (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 3 ≤
      (5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3)^3 :=
    pow_le_pow_left₀ hD_nn hD_le 3
  have hD3_eq : (5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3)^3 =
                125 * 10^24 * pn^15 * qn^15 * s^15 * ‖τ‖^9 := by ring
  have hD3_pol : (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                  ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                    (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 3 ≤
                 125 * 10^24 * pn^15 * qn^15 * s^15 * ‖τ‖^9 := by linarith
  have h_step : (1 / 2 : ℝ) *
                (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                 ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                   (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ^ 3 ≤
                (1 / 2 : ℝ) * (125 * 10^24 * pn^15 * qn^15 * s^15 * ‖τ‖^9) :=
    mul_le_mul_of_nonneg_left hD3_pol (by norm_num)
  have h_eq : (1 / 2 : ℝ) * (125 * 10^24 * pn^15 * qn^15 * s^15 * ‖τ‖^9) =
              ((1 / 2 : ℝ) * 125 * 10^24 * pn^15 * qn^15 * s^15) * ‖τ‖^9 := by ring
  have h_τ_step : ((1 / 2 : ℝ) * 125 * 10^24 * pn^15 * qn^15 * s^15) * ‖τ‖^9 ≤
                  ((1 / 2 : ℝ) * 125 * 10^24 * pn^15 * qn^15 * s^15) * ‖τ‖^6 :=
    mul_le_mul_of_nonneg_left hτ9_le_6 (by positivity)
  have h_c_step : ((1 / 2 : ℝ) * 125 * 10^24 * pn^15 * qn^15 * s^15) * ‖τ‖^6 ≤
                  (10^26 * pn^15 * qn^15 * s^15) * ‖τ‖^6 := by
    have hnn : 0 ≤ pn^15 * qn^15 * s^15 * ‖τ‖^6 := by positivity
    have h_c_le : ((1 / 2 : ℝ) * 125 * 10^24 : ℝ) ≤ 10^26 := by norm_num
    nlinarith [h_c_le, hnn]
  linarith [h_step, h_eq, h_τ_step, h_c_step]

set_option maxHeartbeats 4000000 in
/-- T2c bound: `(1/6)·‖4pτ+2(1-4p)τ‖·‖A+B‖²·QQ ≤ K_T2c·‖τ‖⁶`. -/
private lemma RHS_T2c_le_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ * ‖A + B‖ ^ 2 *
        (‖(((1 - 4 * p) * τ) : ℝ)‖ *
            (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
         ‖((4 * p * τ) : ℝ)‖ *
            (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5)) ≤
      (10^8 * pn^6 * qn^6 * s^7) * ‖τ‖^6 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hτ_le_one : ‖τ‖ ≤ 1 := tau_le_one_aux τ pn qn s hpn_ge hqn_ge hs_ge hτ_lt
  have hτ7_le_6 : ‖τ‖ ^ 7 ≤ ‖τ‖ ^ 6 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 6 ≤ 7)
  -- Norm equalities and η bounds.
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ := norm_nonneg _
  have hAB_nn : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have hAB_norm_le : ‖A + B‖ ≤ s := le_trans (norm_add_le _ _) hAB_le
  have h2_norm : ‖(2 : ℝ)‖ = 2 := by simp
  have h4_norm : ‖(4 : ℝ)‖ = 4 := by simp
  have hpτ_norm : ‖(p * τ : ℝ)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  have h4pτ_eq : (4 * p * τ : ℝ) = 4 * (p * τ) := by ring
  have h4pτ_norm : ‖(4 * p * τ : ℝ)‖ = 4 * ‖p‖ * ‖τ‖ := by
    rw [h4pτ_eq, norm_mul, h4_norm, norm_mul]; ring
  have hsmul_pτA : ‖(p * τ) • A‖ = ‖(p * τ : ℝ)‖ * ‖A‖ := norm_smul _ _
  have hsmul_pτB : ‖(p * τ) • B‖ = ‖(p * τ : ℝ)‖ * ‖B‖ := norm_smul _ _
  have hsmul_qτA : ‖((1 - 4 * p) * τ) • A‖ = ‖((1 - 4 * p) * τ : ℝ)‖ * ‖A‖ := norm_smul _ _
  have hsmul_qτB : ‖((1 - 4 * p) * τ) • B‖ = ‖((1 - 4 * p) * τ : ℝ)‖ * ‖B‖ := norm_smul _ _
  have hηp_eq : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ = ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_pτA, hsmul_pτB, hpτ_norm]; ring
  have hηq_eq : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ =
                ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by
    rw [hsmul_qτA, hsmul_qτB, hqτ_norm]; ring
  have hηp_le : ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hp_le; positivity
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = pn * s * ‖τ‖ := by ring
  have hηq_le : ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hq_le; positivity
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = qn * s * ‖τ‖ := by ring
  have hηp_nn : 0 ≤ ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
  have hηq_nn : 0 ≤ ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖) := by positivity
  -- ‖2(1-2p)τ‖ ≤ 6·pn·|τ|
  have hsum_eq : (4 * p * τ + 2 * ((1 - 4 * p) * τ) : ℝ) = (2 - 4 * p) * τ := by ring
  have habs_2_4p : ‖((2 - 4 * p) : ℝ)‖ ≤ 6 * pn := by
    have h_step : ‖((2 - 4 * p) : ℝ)‖ ≤ ‖(2 : ℝ)‖ + ‖(4 * p : ℝ)‖ := by
      have h_eq : ((2 - 4 * p) : ℝ) = 2 + -(4 * p) := by ring
      rw [h_eq]
      calc ‖(2 + -(4 * p) : ℝ)‖ ≤ ‖(2 : ℝ)‖ + ‖-(4 * p : ℝ)‖ := norm_add_le _ _
        _ = ‖(2 : ℝ)‖ + ‖(4 * p : ℝ)‖ := by rw [norm_neg]
    have h4p : ‖(4 * p : ℝ)‖ = 4 * ‖p‖ := by rw [norm_mul]; simp
    have hh : ‖((2 - 4 * p) : ℝ)‖ ≤ 2 + 4 * ‖p‖ := by linarith [h_step, h2_norm, h4p]
    linarith
  have hsum_norm_le : ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ ≤ 6 * pn * ‖τ‖ := by
    rw [hsum_eq, norm_mul]
    have : ‖((2 - 4 * p) : ℝ)‖ * ‖τ‖ ≤ (6 * pn) * ‖τ‖ :=
      mul_le_mul_of_nonneg_right habs_2_4p hτ_nn
    linarith
  -- ‖A+B‖² ≤ s²
  have hAB_sq_le : ‖A + B‖ ^ 2 ≤ s^2 := by
    have h_nn : 0 ≤ ‖A + B‖ := norm_nonneg _
    exact pow_le_pow_left₀ h_nn hAB_norm_le 2
  -- ‖(1-4p)τ‖ ≤ qn·|τ|
  have hqτ_le : ‖((1 - 4 * p) * τ : ℝ)‖ ≤ qn * ‖τ‖ := by
    rw [hqτ_norm]
    have : ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ ≤ qn * ‖τ‖ :=
      mul_le_mul_of_nonneg_right hq_le hτ_nn
    linarith
  -- ‖4pτ‖ ≤ 4·pn·|τ|
  have h4pτ_le : ‖((4 * p * τ) : ℝ)‖ ≤ 4 * pn * ‖τ‖ := by
    rw [h4pτ_norm]
    have : 4 * ‖p‖ ≤ 4 * pn := by linarith
    nlinarith [hτ_nn]
  -- Q1 := ‖(1-4p)τ‖·4·10⁷·η_p^5 ≤ 4·10⁷·pn^5·qn·s^5·|τ|^6
  have hηp5_le : (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤ pn^5 * s^5 * ‖τ‖^5 := by
    have h_pow : (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤ (pn * s * ‖τ‖)^5 :=
      pow_le_pow_left₀ hηp_nn hηp_le 5
    have heq : (pn * s * ‖τ‖)^5 = pn^5 * s^5 * ‖τ‖^5 := by ring
    linarith
  have hηq5_le : (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤ qn^5 * s^5 * ‖τ‖^5 := by
    have h_pow : (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤ (qn * s * ‖τ‖)^5 :=
      pow_le_pow_left₀ hηq_nn hηq_le 5
    have heq : (qn * s * ‖τ‖)^5 = qn^5 * s^5 * ‖τ‖^5 := by ring
    linarith
  have hQ1_le : ‖(((1 - 4 * p) * τ) : ℝ)‖ *
                (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) ≤
                4 * 10^7 * pn^5 * qn * s^5 * ‖τ‖^6 := by
    rw [hηp_eq]
    have h_inner_pol : 10000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤ 10000000 * (pn^5 * s^5 * ‖τ‖^5) :=
      mul_le_mul_of_nonneg_left hηp5_le (by norm_num)
    have h_4_inner : 4 * (10000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5) ≤
                     4 * (10000000 * (pn^5 * s^5 * ‖τ‖^5)) := by linarith
    have h_4inner_nn : 0 ≤ 4 * (10000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5) := by positivity
    have h_qτ_nn : 0 ≤ qn * ‖τ‖ := by positivity
    have h_first : ‖((1 - 4 * p) * τ : ℝ)‖ * (4 * (10000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5)) ≤
                   (qn * ‖τ‖) * (4 * (10000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5)) :=
      mul_le_mul_of_nonneg_right hqτ_le h_4inner_nn
    have h_second : (qn * ‖τ‖) * (4 * (10000000 * (‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5)) ≤
                    (qn * ‖τ‖) * (4 * (10000000 * (pn^5 * s^5 * ‖τ‖^5))) :=
      mul_le_mul_of_nonneg_left h_4_inner h_qτ_nn
    have h_eq : (qn * ‖τ‖) * (4 * (10000000 * (pn^5 * s^5 * ‖τ‖^5))) =
                4 * 10^7 * pn^5 * qn * s^5 * ‖τ‖^6 := by ring
    linarith
  -- Q2 := ‖4pτ‖·10⁷·η_q^5 ≤ 4·10⁷·pn·qn^5·s^5·|τ|^6
  have hQ2_le : ‖((4 * p * τ) : ℝ)‖ *
                (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5) ≤
                4 * 10^7 * pn * qn^5 * s^5 * ‖τ‖^6 := by
    rw [hηq_eq]
    have h_inner_pol : 10000000 * (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 ≤
                       10000000 * (qn^5 * s^5 * ‖τ‖^5) :=
      mul_le_mul_of_nonneg_left hηq5_le (by norm_num)
    have h_inner_nn : 0 ≤ 10000000 * (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5 := by positivity
    have h_4pτ_nn : 0 ≤ 4 * pn * ‖τ‖ := by positivity
    have h_first : ‖((4 * p * τ) : ℝ)‖ *
                   (10000000 * (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5) ≤
                   (4 * pn * ‖τ‖) * (10000000 * (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5) :=
      mul_le_mul_of_nonneg_right h4pτ_le h_inner_nn
    have h_second : (4 * pn * ‖τ‖) * (10000000 * (‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖))^5) ≤
                    (4 * pn * ‖τ‖) * (10000000 * (qn^5 * s^5 * ‖τ‖^5)) :=
      mul_le_mul_of_nonneg_left h_inner_pol h_4pτ_nn
    have h_eq : (4 * pn * ‖τ‖) * (10000000 * (qn^5 * s^5 * ‖τ‖^5)) =
                4 * 10^7 * pn * qn^5 * s^5 * ‖τ‖^6 := by ring
    linarith
  -- QQ_sum ≤ 8·10⁷·pn^5·qn^5·s^5·|τ|^6 (using pn^5·qn ≤ pn^5·qn^5, pn·qn^5 ≤ pn^5·qn^5)
  have h_qn4_ge : (1 : ℝ) ≤ qn^4 := one_le_pow₀ hqn_ge
  have h_pn4_ge : (1 : ℝ) ≤ pn^4 := one_le_pow₀ hpn_ge
  have h_pn5q_le : pn^5 * qn ≤ pn^5 * qn^5 := by
    have := mul_le_mul_of_nonneg_left h_qn4_ge (by positivity : (0:ℝ) ≤ pn^5 * qn)
    nlinarith
  have h_pq5_le : pn * qn^5 ≤ pn^5 * qn^5 := by
    have := mul_le_mul_of_nonneg_left h_pn4_ge (by positivity : (0:ℝ) ≤ pn * qn^5)
    nlinarith
  have hsτ_nn : 0 ≤ s^5 * ‖τ‖^6 := by positivity
  have h_QQ_sum_le :
      4 * 10^7 * pn^5 * qn * s^5 * ‖τ‖^6 + 4 * 10^7 * pn * qn^5 * s^5 * ‖τ‖^6 ≤
      8 * 10^7 * pn^5 * qn^5 * s^5 * ‖τ‖^6 := by
    have h_part1 : 4 * 10^7 * pn^5 * qn * s^5 * ‖τ‖^6 ≤ 4 * 10^7 * pn^5 * qn^5 * s^5 * ‖τ‖^6 := by
      have h_step : 4 * 10^7 * (pn^5 * qn) ≤ 4 * 10^7 * (pn^5 * qn^5) :=
        mul_le_mul_of_nonneg_left h_pn5q_le (by norm_num)
      nlinarith [h_step, hsτ_nn]
    have h_part2 : 4 * 10^7 * pn * qn^5 * s^5 * ‖τ‖^6 ≤ 4 * 10^7 * pn^5 * qn^5 * s^5 * ‖τ‖^6 := by
      have h_step : 4 * 10^7 * (pn * qn^5) ≤ 4 * 10^7 * (pn^5 * qn^5) :=
        mul_le_mul_of_nonneg_left h_pq5_le (by norm_num)
      nlinarith [h_step, hsτ_nn]
    linarith
  -- Combine: T2c ≤ (1/6)·6·pn·|τ|·s²·8·10⁷·pn^5·qn^5·s^5·|τ|^6
  have hQQ_sum_nn : 0 ≤ ‖(((1 - 4 * p) * τ) : ℝ)‖ *
                     (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
                     ‖((4 * p * τ) : ℝ)‖ *
                     (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5) := by
    positivity
  have hQQ_le_pol :
      ‖(((1 - 4 * p) * τ) : ℝ)‖ *
        (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
      ‖((4 * p * τ) : ℝ)‖ *
        (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5) ≤
      8 * 10^7 * pn^5 * qn^5 * s^5 * ‖τ‖^6 := by linarith [hQ1_le, hQ2_le, h_QQ_sum_le]
  -- Multiply: (1/6) * ‖4pτ+2(1-4p)τ‖ * ‖A+B‖² * QQ
  have h_inner1 : (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ ≤
                  (1 / 6 : ℝ) * (6 * pn * ‖τ‖) :=
    mul_le_mul_of_nonneg_left hsum_norm_le (by norm_num)
  have h_inner1_nn : 0 ≤ (1 / 6 : ℝ) * (6 * pn * ‖τ‖) := by positivity
  have h_inner2 : (1 / 6 : ℝ) * (6 * pn * ‖τ‖) * ‖A + B‖^2 ≤
                  (1 / 6 : ℝ) * (6 * pn * ‖τ‖) * s^2 :=
    mul_le_mul_of_nonneg_left hAB_sq_le h_inner1_nn
  have h_inner2_nn : 0 ≤ (1 / 6 : ℝ) * (6 * pn * ‖τ‖) * s^2 := by positivity
  -- Combine the four factors with three multiplication steps.
  have h_AB_sq_nn : 0 ≤ ‖A + B‖^2 := by positivity
  have h_inner_step1 :
      (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ * ‖A + B‖^2 ≤
      (1 / 6 : ℝ) * (6 * pn * ‖τ‖) * ‖A + B‖^2 := by
    nlinarith [h_inner1, h_AB_sq_nn]
  have h_step1_nn : 0 ≤ (1 / 6 : ℝ) * (6 * pn * ‖τ‖) * ‖A + B‖^2 := by positivity
  have h_inner_step2 :
      (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ * ‖A + B‖^2 ≤
      (1 / 6 : ℝ) * (6 * pn * ‖τ‖) * s^2 := le_trans h_inner_step1 h_inner2
  have h_QQ_step :
      (1 / 6 : ℝ) * ‖((4 * p * τ + 2 * ((1 - 4 * p) * τ)) : ℝ)‖ * ‖A + B‖^2 *
        (‖(((1 - 4 * p) * τ) : ℝ)‖ *
            (4 * (10000000 * (‖(p * τ) • A‖ + ‖(p * τ) • B‖) ^ 5)) +
         ‖((4 * p * τ) : ℝ)‖ *
            (10000000 * (‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖) ^ 5)) ≤
      ((1 / 6 : ℝ) * (6 * pn * ‖τ‖) * s^2) * (8 * 10^7 * pn^5 * qn^5 * s^5 * ‖τ‖^6) :=
    mul_le_mul h_inner_step2 hQQ_le_pol hQQ_sum_nn h_inner2_nn
  -- Final: simplify constants.
  have h_chain : ((1 / 6 : ℝ) * (6 * pn * ‖τ‖) * s^2) *
                 (8 * 10^7 * pn^5 * qn^5 * s^5 * ‖τ‖^6) =
                 (8 * 10^7 * pn^6 * qn^5 * s^7) * ‖τ‖^7 := by ring
  have hτ7_to_6 : (8 * 10^7 * pn^6 * qn^5 * s^7) * ‖τ‖^7 ≤
                  (8 * 10^7 * pn^6 * qn^5 * s^7) * ‖τ‖^6 :=
    mul_le_mul_of_nonneg_left hτ7_le_6 (by positivity)
  have hqn5_le_6 : qn^5 ≤ qn^6 := pow_le_pow_right₀ hqn_ge (by norm_num : 5 ≤ 6)
  have h_const_lift : (8 * 10^7 * pn^6 * qn^5 * s^7) * ‖τ‖^6 ≤
                      (10^8 * pn^6 * qn^6 * s^7) * ‖τ‖^6 := by
    have hpn6s7τ6_nn : 0 ≤ pn^6 * s^7 * ‖τ‖^6 := by positivity
    have h_qn_step : 8 * 10^7 * pn^6 * qn^5 ≤ 8 * 10^7 * pn^6 * qn^6 := by
      have h_pn6_nn : 0 ≤ 8 * 10^7 * pn^6 := by positivity
      exact mul_le_mul_of_nonneg_left hqn5_le_6 h_pn6_nn
    have h_const_step : (8 * 10^7 : ℝ) ≤ 10^8 := by norm_num
    have hpn6qn6_nn : 0 ≤ pn^6 * qn^6 := by positivity
    have h_const_pn_qn : 8 * 10^7 * pn^6 * qn^6 ≤ 10^8 * pn^6 * qn^6 := by
      nlinarith [h_const_step, hpn6qn6_nn]
    have h_combined : 8 * 10^7 * pn^6 * qn^5 ≤ 10^8 * pn^6 * qn^6 := by linarith
    nlinarith [h_combined, hpn6s7τ6_nn]
  linarith [h_QQ_step, h_chain, hτ7_to_6, h_const_lift]

set_option maxHeartbeats 4000000 in
/-- T3 bound: `2·(N+‖4X‖+‖Y‖)^4·D ≤ K_T3·‖τ‖⁶`. -/
private lemma RHS_T3_le_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    2 * (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
          ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
          ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖) ^ 4 *
      (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
       ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
         (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ≤
      (2 * 10^30 * pn^9 * qn^9 * s^9) * ‖τ‖^6 := by
  have hpn_pos : (0 : ℝ) < pn := by linarith
  have hqn_pos : (0 : ℝ) < qn := by linarith
  have hs_pos : (0 : ℝ) < s := by linarith
  have hτ_nn : 0 ≤ ‖τ‖ := norm_nonneg _
  have hτ_le_one : ‖τ‖ ≤ 1 := tau_le_one_aux τ pn qn s hpn_ge hqn_ge hs_ge hτ_lt
  have hτ7_le_6 : ‖τ‖ ^ 7 ≤ ‖τ‖ ^ 6 :=
    pow_le_pow_of_le_one hτ_nn hτ_le_one (by norm_num : 6 ≤ 7)
  -- Bounds on each of the 4 norms.
  have hAB_norm_le : ‖A + B‖ ≤ s := le_trans (norm_add_le _ _) hAB_le
  have h4_norm : ‖(4 : ℝ)‖ = 4 := by simp
  have h4pτ_eq : (4 * p * τ : ℝ) = 4 * (p * τ) := by ring
  have h4pτ_norm : ‖(4 * p * τ : ℝ)‖ = 4 * ‖p‖ * ‖τ‖ := by
    rw [h4pτ_eq, norm_mul, h4_norm, norm_mul]; ring
  have hqτ_norm : ‖((1 - 4 * p) * τ : ℝ)‖ = ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ := norm_mul _ _
  have h4pτAB_le : ‖((4 * p * τ : ℝ)) • (A + B)‖ ≤ 4 * pn * s * ‖τ‖ := by
    rw [norm_smul, h4pτ_norm]
    calc 4 * ‖p‖ * ‖τ‖ * ‖A + B‖
        = (4 * ‖p‖) * (‖τ‖ * ‖A + B‖) := by ring
      _ ≤ (4 * pn) * (‖τ‖ * ‖A + B‖) := by
          apply mul_le_mul_of_nonneg_right (by linarith); positivity
      _ = 4 * pn * ‖τ‖ * ‖A + B‖ := by ring
      _ ≤ 4 * pn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_norm_le; positivity
      _ = 4 * pn * s * ‖τ‖ := by ring
  have hqτAB_le : ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ ≤ qn * s * ‖τ‖ := by
    rw [norm_smul, hqτ_norm]
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * ‖A + B‖
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * ‖A + B‖) := by ring
      _ ≤ qn * (‖τ‖ * ‖A + B‖) := by
          apply mul_le_mul_of_nonneg_right hq_le; positivity
      _ = qn * ‖τ‖ * ‖A + B‖ := by ring
      _ ≤ qn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_norm_le; positivity
      _ = qn * s * ‖τ‖ := by ring
  -- Strang block linear bounds.
  have hp_reg := p_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hAB_le hτ_lt
  have hq_reg := q_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hq_le hAB_le hτ_lt
  have hsbp := norm_strangBlock_log_linear (𝕂 := ℝ) A B p τ hp_reg
  have hsbq := norm_strangBlock_log_linear (𝕂 := ℝ) A B (1 - 4 * p) τ hq_reg
  have hpτ_norm : ‖(p * τ : ℝ)‖ = ‖p‖ * ‖τ‖ := norm_mul _ _
  have hηp_le : ‖(p * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ pn * s * ‖τ‖ := by
    rw [hpτ_norm]
    calc ‖p‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖p‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ pn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hp_le; positivity
      _ = pn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ pn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = pn * s * ‖τ‖ := by ring
  have hηq_le : ‖((1 - 4 * p) * τ : ℝ)‖ * (‖A‖ + ‖B‖) ≤ qn * s * ‖τ‖ := by
    rw [hqτ_norm]
    calc ‖((1 : ℝ) - 4 * p)‖ * ‖τ‖ * (‖A‖ + ‖B‖)
        = ‖((1 : ℝ) - 4 * p)‖ * (‖τ‖ * (‖A‖ + ‖B‖)) := by ring
      _ ≤ qn * (‖τ‖ * (‖A‖ + ‖B‖)) := by
          apply mul_le_mul_of_nonneg_right hq_le; positivity
      _ = qn * ‖τ‖ * (‖A‖ + ‖B‖) := by ring
      _ ≤ qn * ‖τ‖ * s := by
          apply mul_le_mul_of_nonneg_left hAB_le; positivity
      _ = qn * s * ‖τ‖ := by ring
  have hsbp_bnd : ‖strangBlock_log ℝ A B p τ‖ ≤ 40002 * (pn * s * ‖τ‖) := by linarith
  have hsbq_bnd : ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ ≤ 40002 * (qn * s * ‖τ‖) := by linarith
  have h4smul : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ = 4 * ‖strangBlock_log ℝ A B p τ‖ := by
    rw [norm_smul, h4_norm]
  have h4sbp_bnd : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ ≤ 4 * (40002 * (pn * s * ‖τ‖)) := by
    rw [h4smul]
    exact mul_le_mul_of_nonneg_left hsbp_bnd (by norm_num : (0:ℝ) ≤ 4)
  -- M ≤ 200015·pn·qn·s·|τ|.
  have hM_nn : 0 ≤ ‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
                   ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                   ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ := by positivity
  have hM_le : ‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
               ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
               ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ ≤ 200015 * pn * qn * s * ‖τ‖ := by
    have h_chain : 4 * pn * s * ‖τ‖ + qn * s * ‖τ‖ +
                   4 * (40002 * (pn * s * ‖τ‖)) +
                   40002 * (qn * s * ‖τ‖) = 40003 * (4 * pn + qn) * s * ‖τ‖ := by ring
    have h4pq_le : 4 * pn + qn ≤ 5 * pn * qn := by nlinarith
    have h_sτ_nn : 0 ≤ s * ‖τ‖ := by positivity
    have h_step1 : 40003 * (4 * pn + qn) * s * ‖τ‖ ≤ 40003 * (5 * pn * qn) * s * ‖τ‖ := by
      have hh : 40003 * (4 * pn + qn) ≤ 40003 * (5 * pn * qn) := by
        apply mul_le_mul_of_nonneg_left h4pq_le; norm_num
      nlinarith [h_sτ_nn]
    have h_step2 : 40003 * (5 * pn * qn) * s * ‖τ‖ = 200015 * pn * qn * s * ‖τ‖ := by ring
    linarith [h4pτAB_le, hqτAB_le, h4sbp_bnd, hsbq_bnd]
  -- M^4 ≤ (200015)^4·pn^4·qn^4·s^4·|τ|^4 ≤ 2·10^21·pn^4·qn^4·s^4·|τ|^4
  have hM4_le : (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
                 ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                 ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^4 ≤
                (200015 * pn * qn * s * ‖τ‖)^4 :=
    pow_le_pow_left₀ hM_nn hM_le 4
  have hM4_eq : (200015 * pn * qn * s * ‖τ‖)^4 = 200015^4 * pn^4 * qn^4 * s^4 * ‖τ‖^4 := by ring
  have h_const_M4 : (200015 : ℝ)^4 ≤ 2 * 10^21 := by norm_num
  have hM4_pol : (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
                  ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                  ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^4 ≤
                 2 * 10^21 * pn^4 * qn^4 * s^4 * ‖τ‖^4 := by
    have hpqstn_nn : 0 ≤ pn^4 * qn^4 * s^4 * ‖τ‖^4 := by positivity
    have h_lift : 200015^4 * pn^4 * qn^4 * s^4 * ‖τ‖^4 ≤
                  2 * 10^21 * pn^4 * qn^4 * s^4 * ‖τ‖^4 := by
      nlinarith [h_const_M4, hpqstn_nn]
    linarith [hM4_le, hM4_eq, h_lift]
  -- D bound.
  have hD_le := D_bound_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hD_nn : 0 ≤ ‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                   ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                     (((1 - 4 * p) * τ : ℝ)) • (A + B)‖ := by positivity
  have hM4pol_nn : 0 ≤ 2 * 10^21 * pn^4 * qn^4 * s^4 * ‖τ‖^4 := by positivity
  -- M^4 · D
  have h_M4D_step : (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
                     ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                     ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^4 *
                    (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                     ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                       (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) ≤
                    (2 * 10^21 * pn^4 * qn^4 * s^4 * ‖τ‖^4) *
                    (5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3) :=
    mul_le_mul hM4_pol hD_le hD_nn hM4pol_nn
  -- 2 * (M^4 * D)
  have h_2M4D_step : 2 * ((‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
                          ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                          ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^4 *
                         (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                          ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                            (((1 - 4 * p) * τ : ℝ)) • (A + B)‖)) ≤
                    2 * ((2 * 10^21 * pn^4 * qn^4 * s^4 * ‖τ‖^4) *
                         (5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3)) :=
    mul_le_mul_of_nonneg_left h_M4D_step (by norm_num : (0:ℝ) ≤ 2)
  -- Associativity: 2 * M^4 * D = 2 * (M^4 * D)
  have h_assoc : 2 * (‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
                      ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                      ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^4 *
                     (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                      ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                        (((1 - 4 * p) * τ : ℝ)) • (A + B)‖) =
                2 * ((‖((4 * p * τ : ℝ)) • (A + B)‖ + ‖(((1 - 4 * p) * τ : ℝ)) • (A + B)‖ +
                      ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                      ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖)^4 *
                     (‖(4 : ℝ) • strangBlock_log ℝ A B p τ - ((4 * p * τ : ℝ)) • (A + B)‖ +
                      ‖strangBlock_log ℝ A B (1 - 4 * p) τ -
                        (((1 - 4 * p) * τ : ℝ)) • (A + B)‖)) := by ring
  -- 2 * (...) reduces to K · ‖τ‖^7
  have h_chain : 2 * ((2 * 10^21 * pn^4 * qn^4 * s^4 * ‖τ‖^4) *
                      (5 * 10^8 * pn^5 * qn^5 * s^5 * ‖τ‖^3)) =
                 (2 * 10^30 * pn^9 * qn^9 * s^9) * ‖τ‖^7 := by ring
  have hτ7_to_6_K : (2 * 10^30 * pn^9 * qn^9 * s^9) * ‖τ‖^7 ≤
                    (2 * 10^30 * pn^9 * qn^9 * s^9) * ‖τ‖^6 :=
    mul_le_mul_of_nonneg_left hτ7_le_6 (by positivity)
  linarith [h_2M4D_step, h_assoc, h_chain, hτ7_to_6_K]

set_option maxHeartbeats 4000000 in
/-- Combined RHS bound: `suzuki5_bch_sub_R5_RHS A B p τ ≤ K·‖τ‖⁶` for the
explicit polynomial constant K = sum of T1, T2a, T2b, T2c, T3 bounds. -/
private lemma suzuki5_bch_sub_R5_RHS_le_aux
    (A B : 𝔸) (p τ : ℝ) (pn qn s : ℝ)
    (hpn_ge : (1 : ℝ) ≤ pn) (hqn_ge : (1 : ℝ) ≤ qn) (hs_ge : (1 : ℝ) ≤ s)
    (hp_le : ‖p‖ ≤ pn) (hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn)
    (hAB_le : ‖A‖ + ‖B‖ ≤ s)
    (hτ_lt : ‖τ‖ < 1 / (10^11 * pn * qn * s)) :
    suzuki5_bch_sub_R5_RHS A B p τ ≤
      (4 * 10^9 * pn^7 * s^7 + 10^9 * qn^7 * s^7 +
       10^9 * 40002^7 * (4 * pn + qn)^7 * s^7 +
       2 * 10^18 * pn^11 * qn^11 * s^11 +
       10^26 * pn^15 * qn^15 * s^15 +
       10^8 * pn^6 * qn^6 * s^7 +
       2 * 10^30 * pn^9 * qn^9 * s^9) * ‖τ‖^6 := by
  unfold suzuki5_bch_sub_R5_RHS
  have hT1 := RHS_T1_le_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hT2a := RHS_T2a_le_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hT2b := RHS_T2b_le_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hT2c := RHS_T2c_le_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hT3 := RHS_T3_le_aux A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  linarith [hT1, hT2a, hT2b, hT2c, hT3]

set_option maxHeartbeats 4000000 in
theorem norm_suzuki5_bch_sub_smul_sub_R5_le
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, ‖τ‖ < δ →
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖
        ≤ K * ‖τ‖ ^ 6 := by
  set pn : ℝ := ‖p‖ + 1 with hpn_def
  set qn : ℝ := ‖((1 : ℝ) - 4 * p)‖ + 1 with hqn_def
  set s : ℝ := ‖A‖ + ‖B‖ + 1 with hs_def
  have hpn_ge : (1 : ℝ) ≤ pn := by rw [hpn_def]; linarith [norm_nonneg p]
  have hqn_ge : (1 : ℝ) ≤ qn := by rw [hqn_def]; linarith [norm_nonneg ((1 : ℝ) - 4 * p)]
  have hs_ge : (1 : ℝ) ≤ s := by rw [hs_def]; linarith [norm_nonneg A, norm_nonneg B]
  have hp_le : ‖p‖ ≤ pn := by rw [hpn_def]; linarith
  have hq_le : ‖((1 : ℝ) - 4 * p)‖ ≤ qn := by rw [hqn_def]; linarith
  have hAB_le : ‖A‖ + ‖B‖ ≤ s := by rw [hs_def]; linarith
  refine ⟨1 / (10^11 * pn * qn * s), by positivity,
          4 * 10^9 * pn^7 * s^7 + 10^9 * qn^7 * s^7 +
            10^9 * 40002^7 * (4 * pn + qn)^7 * s^7 +
            2 * 10^18 * pn^11 * qn^11 * s^11 +
            10^26 * pn^15 * qn^15 * s^15 +
            10^8 * pn^6 * qn^6 * s^7 +
            2 * 10^30 * pn^9 * qn^9 * s^9,
          by positivity, ?_⟩
  intro τ hτ_lt
  -- Derive 6 regime hypotheses.
  have hp_reg := p_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hp_le hAB_le hτ_lt
  have hq_reg := q_regime_of_tau_small A B p τ pn qn s hpn_ge hqn_ge hs_ge hq_le hAB_le hτ_lt
  have hreg := reg_lt_quarter_of_tau_small A B p τ pn qn s
                 hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hR := R_lt_log_two_of_tau_small A B p τ pn qn s
               hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hZ1 := Z1_lt_log_two_of_tau_small A B p τ pn qn s
                hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  have hZ2 := Z2_lt_log_two_of_tau_small A B p τ pn qn s
                hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  -- Convert hreg's `< 1/4` to the `< 1/4` form expected by under_regime.
  have hreg_quarter : ‖(4 : ℝ) • strangBlock_log ℝ A B p τ‖ +
                      ‖strangBlock_log ℝ A B (1 - 4 * p) τ‖ < 1 / 4 := hreg
  -- Apply the under-regime helper.
  have h_under :=
    norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime A B p τ hcubic
      hR hp_reg hq_reg hreg_quarter hZ1 hZ2
  -- Bound the RHS by the polynomial.
  have h_RHS_bnd :=
    suzuki5_bch_sub_R5_RHS_le_aux A B p τ pn qn s
      hpn_ge hqn_ge hs_ge hp_le hq_le hAB_le hτ_lt
  -- Compose: h_under ≤ EXPLICIT_RHS = suzuki5_bch_sub_R5_RHS ≤ K·|τ|^6.
  exact le_trans h_under h_RHS_bnd

/-!
## Bridge corollary: quintic-magnitude bound via the Childs 4-fold sum

Direct consequence of `norm_suzuki5_bch_sub_smul_sub_R5_le` combined with
`norm_suzuki5_R5_le_bchFourFoldSum` via the triangle inequality:

  ‖suzuki5_bch − τ•(A+B)‖
    ≤ ‖suzuki5_bch − τ•(A+B) − τ⁵•R₅‖ + ‖τ⁵•R₅‖
    ≤ K·τ⁶ + τ⁵ · bchFourFoldSum A B

This is the form consumed by Lean-Trotter's axiom
`bch_w4Deriv_quintic_level2` in `LieTrotter/Suzuki4ViaBCH.lean`.

(Module placement note: the bridge corollary naturally belongs in
`Palindromic.lean` per the phase-1 task spec, but the import direction
`Palindromic → Suzuki5Quintic → ChildsBasis` forces it here since the
proof references `norm_suzuki5_bch_sub_smul_sub_R5_le` and
`norm_suzuki5_R5_le_bchFourFoldSum`, both in this file.)
-/

/-- **Bridge corollary**: under `IsSuzukiCubic p`, the quintic-magnitude BCH
bound `‖suzuki5_bch − τ•(A+B)‖ ≤ τ⁵·bchFourFoldSum A B + K·τ⁶` for small
non-negative `τ`. Combines the explicit `suzuki5_R5` identification with
its unit-coefficient Childs-sum norm bound.

Signature shape matches the form consumed by Lean-Trotter's axiom
`bch_w4Deriv_quintic_level2`. -/
theorem suzuki5_log_product_quintic_of_IsSuzukiCubic
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B)‖ ≤
        τ ^ 5 * bchFourFoldSum A B + K * τ ^ 6 := by
  obtain ⟨δ, hδ_pos, K, hK_nn, hbound⟩ :=
    norm_suzuki5_bch_sub_smul_sub_R5_le A B p hcubic
  refine ⟨δ, hδ_pos, K, hK_nn, ?_⟩
  intro τ hτ_nn hτ_lt
  -- Convert `τ < δ` under `0 ≤ τ` to `‖τ‖ < δ`.
  have hτ_norm : ‖τ‖ < δ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hτ_nn]; exact hτ_lt
  -- The O(τ⁶) bound on the quintic residual.
  have h_resid :
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖ ≤
        K * ‖τ‖ ^ 6 := hbound τ hτ_norm
  -- The τ⁵ R₅ term's norm.
  have hR5_bnd : ‖suzuki5_R5 A B p‖ ≤ bchFourFoldSum A B :=
    norm_suzuki5_R5_le_bchFourFoldSum A B p hcubic
  -- Bound ‖τ⁵ • R₅‖.
  have hτ5_nn : 0 ≤ τ ^ 5 := pow_nonneg hτ_nn 5
  have hτ5_norm : ‖(τ ^ 5 : ℝ)‖ = τ ^ 5 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hτ5_nn]
  have h_smul_bnd :
      ‖τ ^ 5 • suzuki5_R5 A B p‖ ≤ τ ^ 5 * bchFourFoldSum A B := by
    calc ‖τ ^ 5 • suzuki5_R5 A B p‖
        ≤ ‖(τ ^ 5 : ℝ)‖ * ‖suzuki5_R5 A B p‖ := norm_smul_le _ _
      _ = τ ^ 5 * ‖suzuki5_R5 A B p‖ := by rw [hτ5_norm]
      _ ≤ τ ^ 5 * bchFourFoldSum A B := by gcongr
  -- Convert ‖τ‖^6 under `0 ≤ τ` to τ^6.
  have hτ6_eq : ‖τ‖ ^ 6 = τ ^ 6 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hτ_nn]
  have h_resid' :
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖ ≤
        K * τ ^ 6 := by rw [← hτ6_eq]; exact h_resid
  -- Algebraic decomposition: X = (X - Y) + Y, triangle ‖X‖ ≤ ‖X - Y‖ + ‖Y‖.
  have h_triangle :
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B)‖ ≤
        ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖ +
        ‖τ ^ 5 • suzuki5_R5 A B p‖ := by
    calc ‖suzuki5_bch ℝ A B p τ - τ • (A + B)‖
        = ‖(suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p) +
            (τ ^ 5 • suzuki5_R5 A B p)‖ := by congr 1; abel
      _ ≤ ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖ +
            ‖τ ^ 5 • suzuki5_R5 A B p‖ := norm_add_le _ _
  -- Combine.
  linarith [h_triangle, h_resid', h_smul_bnd]

end HeadlineTheorem

/-!
## Tight bridge at Suzuki p

For `p = 1/(4 − 4^(1/3))` (the unique real root of the Suzuki cubic),
the τ⁵ coefficient `suzuki5_R5 A B p` has norm bounded by the
*weighted* Childs sum `bchTightPrefactors.boundSum A B` — strictly
tighter than the unit-coefficient `bchFourFoldSum A B`.

This section adds:

* `suzukiP` — the canonical real root of the Suzuki cubic.
* `rpow_one_third_cube` — auxiliary: `((4 : ℝ) ^ (1/3))^3 = 4`.
* `IsSuzukiCubic_suzukiP` — `IsSuzukiCubic suzukiP`, proved directly
  from the algebraic identity `4p³ + (1−4p)³ = (4 − r³)/(4−r)³`.
* `norm_suzuki5_R5_at_suzukiP_le_bchTightPrefactors_boundSum` — the
  tight norm bound (currently axiom-chained; see the embedded
  `private axiom suzuki5_R5_at_suzukiP_tight_bound_axiom`).
* `suzuki5_log_product_quintic_tight_at_suzukiP` — the bridge theorem
  matching Lean-Trotter's `bch_w4Deriv_level3_tight` axiom shape.
-/

section TightBridge

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
  [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The canonical real Suzuki parameter `p = 1/(4 − 4^(1/3)) ≈ 0.4145`. -/
noncomputable def suzukiP : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))

/-- Auxiliary: `((4 : ℝ) ^ (1/3))^3 = 4`. -/
lemma rpow_one_third_cube : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 4 := by
  have h4_nn : (0 : ℝ) ≤ 4 := by norm_num
  rw [← Real.rpow_natCast ((4 : ℝ) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul h4_nn]
  norm_num

/-- `4^(1/3) > 1` (since `1^3 = 1 < 4`). -/
lemma one_lt_rpow_one_third : (1 : ℝ) < (4 : ℝ) ^ ((1 : ℝ) / 3) := by
  have h4_nn : (0 : ℝ) ≤ 4 := by norm_num
  have h : (1 : ℝ) ^ 3 < ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
    rw [rpow_one_third_cube]; norm_num
  have hrpow_nn : 0 ≤ (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg h4_nn _
  nlinarith [sq_nonneg ((4 : ℝ) ^ ((1 : ℝ) / 3)),
             sq_nonneg ((4 : ℝ) ^ ((1 : ℝ) / 3) - 1)]

/-- `4^(1/3) < 4` (since `4^(1/3))^3 = 4 < 64 = 4^3`). -/
lemma rpow_one_third_lt_four : (4 : ℝ) ^ ((1 : ℝ) / 3) < 4 := by
  have h4_nn : (0 : ℝ) ≤ 4 := by norm_num
  have h : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < (4 : ℝ) ^ 3 := by
    rw [rpow_one_third_cube]; norm_num
  have hrpow_nn : 0 ≤ (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg h4_nn _
  nlinarith [sq_nonneg ((4 : ℝ) ^ ((1 : ℝ) / 3)),
             sq_nonneg ((4 : ℝ) ^ ((1 : ℝ) / 3) + 4),
             sq_nonneg ((4 : ℝ) ^ ((1 : ℝ) / 3) - 4)]

/-- `4 − 4^(1/3) > 0`. -/
lemma four_sub_rpow_pos : (0 : ℝ) < 4 - (4 : ℝ) ^ ((1 : ℝ) / 3) := by
  linarith [rpow_one_third_lt_four]

/-- `IsSuzukiCubic suzukiP`: the canonical real Suzuki root satisfies
`4p³ + (1−4p)³ = 0`. -/
theorem IsSuzukiCubic_suzukiP : IsSuzukiCubic suzukiP := by
  rw [IsSuzukiCubic_iff]
  unfold suzukiP
  set r : ℝ := (4 : ℝ) ^ ((1 : ℝ) / 3) with hr_def
  have hr3 : r ^ 3 = 4 := rpow_one_third_cube
  have h4_sub_r : 4 - r ≠ 0 := ne_of_gt four_sub_rpow_pos
  -- Algebraic identity: 4·(1/(4−r))³ + (1 − 4/(4−r))³ = (4 − r³)/(4−r)³ = 0.
  have key :
      4 * (1 / (4 - r)) ^ 3 + (1 - 4 * (1 / (4 - r))) ^ 3 =
        (4 - r ^ 3) / (4 - r) ^ 3 := by
    field_simp
    ring
  rw [key, hr3, sub_self, zero_div]

/-- **Tight rational interval bound** `41449/100000 < suzukiP <
41450/100000`. Proved from the expanded Suzuki cubic
`−60p³ + 48p² − 12p + 1 = 0` via `nlinarith` with polynomial hints at
the interval endpoints.

Exactly `suzukiP ≈ 0.4144908`; the gap to the endpoints (~8·10⁻⁶ and
~0.9·10⁻⁶) is enough slack for the subsequent per-i `|βᵢ(suzukiP)|
≤ γᵢ` bounds via `nlinarith`. -/
theorem suzukiP_mem_rational_interval :
    41449 / 100000 < suzukiP ∧ suzukiP < 41450 / 100000 := by
  have hcubic : IsSuzukiCubic suzukiP := IsSuzukiCubic_suzukiP
  have hbounds : 0 < suzukiP ∧ suzukiP < 1 :=
    IsSuzukiCubic_real_strict_bound suzukiP hcubic
  obtain ⟨hp_pos, hp_lt⟩ := hbounds
  rw [IsSuzukiCubic_iff] at hcubic
  have hg : -60 * suzukiP ^ 3 + 48 * suzukiP ^ 2 - 12 * suzukiP + 1 = 0 := by
    have heq : 4 * suzukiP ^ 3 + (1 - 4 * suzukiP) ^ 3 =
               -60 * suzukiP ^ 3 + 48 * suzukiP ^ 2 - 12 * suzukiP + 1 := by ring
    linarith [heq]
  refine ⟨?_, ?_⟩
  · -- Lower bound: 41449/100000 < suzukiP.
    by_contra hc
    push_neg at hc
    nlinarith [hg, hp_pos, hc,
               sq_nonneg (suzukiP - 41449/100000), sq_nonneg (suzukiP - 1/5),
               sq_nonneg suzukiP,
               mul_pos hp_pos hp_pos,
               mul_pos hp_pos (mul_pos hp_pos hp_pos)]
  · -- Upper bound: suzukiP < 41450/100000.
    by_contra hc
    push_neg at hc
    nlinarith [hg, hp_pos, hp_lt, hc,
               sq_nonneg (suzukiP - 41450/100000), sq_nonneg (suzukiP - 1/3),
               sq_nonneg (1 - suzukiP),
               mul_pos hp_pos hp_pos,
               mul_pos hp_pos (mul_pos hp_pos hp_pos)]

/-!
### Per-i numerical bounds `|βᵢ(suzukiP)| ≤ γᵢ`

For each `i ∈ {1, 2, 4, 5, 6, 8}` (the six non-zero γᵢ), proved via
`nlinarith` on `suzukiP_mem_rational_interval` + polynomial hints at
the tight interval endpoints.
-/

/-- `|β₁(suzukiP)| ≤ γ₁ = 260/10⁶`. -/
lemma abs_suzuki5_β₁_at_suzukiP_le_γ₁ :
    |suzuki5_β₁ suzukiP| ≤ 260 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  unfold suzuki5_β₁
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [hlo, hhi, sq_nonneg suzukiP,
               sq_nonneg (suzukiP - 41449/100000),
               sq_nonneg (suzukiP - 41450/100000)]

/-- `|β₂(suzukiP)| ≤ γ₂ = 663/10⁶` (ceiling). -/
lemma abs_suzuki5_β₂_at_suzukiP_le_γ₂ :
    |suzuki5_β₂ suzukiP| ≤ 663 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  unfold suzuki5_β₂
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [hlo, hhi, sq_nonneg suzukiP,
               sq_nonneg (suzukiP - 41449/100000),
               sq_nonneg (suzukiP - 41450/100000)]

/-- `|β₃(suzukiP)| ≤ γ₃ = 0` (both exactly 0). -/
lemma abs_suzuki5_β₃_at_suzukiP_le_γ₃ :
    |suzuki5_β₃ suzukiP| ≤ 0 := by
  unfold suzuki5_β₃; simp

/-- `|β₄(suzukiP)| ≤ γ₄ = 132/10⁶`. -/
lemma abs_suzuki5_β₄_at_suzukiP_le_γ₄ :
    |suzuki5_β₄ suzukiP| ≤ 132 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  unfold suzuki5_β₄
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [hlo, hhi, sq_nonneg suzukiP,
               sq_nonneg (suzukiP - 41449/100000),
               sq_nonneg (suzukiP - 41450/100000)]

/-- `|β₅(suzukiP)| ≤ γ₅ = 376/10⁶`. -/
lemma abs_suzuki5_β₅_at_suzukiP_le_γ₅ :
    |suzuki5_β₅ suzukiP| ≤ 376 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  unfold suzuki5_β₅
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [hlo, hhi, sq_nonneg suzukiP,
               sq_nonneg (suzukiP - 41449/100000),
               sq_nonneg (suzukiP - 41450/100000)]

/-- `|β₆(suzukiP)| ≤ γ₆ = 1128/10⁶` (ceiling). -/
lemma abs_suzuki5_β₆_at_suzukiP_le_γ₆ :
    |suzuki5_β₆ suzukiP| ≤ 1128 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  unfold suzuki5_β₆
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [hlo, hhi, sq_nonneg suzukiP,
               sq_nonneg (suzukiP - 41449/100000),
               sq_nonneg (suzukiP - 41450/100000)]

/-- `|β₇(suzukiP)| ≤ γ₇ = 0` (both exactly 0). -/
lemma abs_suzuki5_β₇_at_suzukiP_le_γ₇ :
    |suzuki5_β₇ suzukiP| ≤ 0 := by
  unfold suzuki5_β₇; simp

/-- `|β₈(suzukiP)| ≤ γ₈ = 442/10⁶`. -/
lemma abs_suzuki5_β₈_at_suzukiP_le_γ₈ :
    |suzuki5_β₈ suzukiP| ≤ 442 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  unfold suzuki5_β₈
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [hlo, hhi, sq_nonneg suzukiP,
               sq_nonneg (suzukiP - 41449/100000),
               sq_nonneg (suzukiP - 41450/100000)]

/-- **Tight R₅ norm bound**: at the canonical real Suzuki `p`, the
τ⁵ coefficient's norm is bounded by the weighted Childs sum with
rational ceiling prefactors `γᵢ`.

Proof: triangle inequality on the Childs-basis expansion of
`suzuki5_R5`, combined with the six numerical bounds
`abs_suzuki5_βᵢ_at_suzukiP_le_γᵢ` for `i ∈ {1, 2, 4, 5, 6, 8}` (the
cases `i ∈ {3, 7}` trivialize since both `βᵢ(suzukiP) = γᵢ = 0`). -/
theorem norm_suzuki5_R5_at_suzukiP_le_bchTightPrefactors_boundSum
    (A B : 𝔸) :
    ‖suzuki5_R5 A B suzukiP‖ ≤ bchTightPrefactors.boundSum A B := by
  unfold suzuki5_R5 BCHPrefactors.boundSum bchTightPrefactors
  have h₁ := abs_suzuki5_β₁_at_suzukiP_le_γ₁
  have h₂ := abs_suzuki5_β₂_at_suzukiP_le_γ₂
  have h₃ := abs_suzuki5_β₃_at_suzukiP_le_γ₃
  have h₄ := abs_suzuki5_β₄_at_suzukiP_le_γ₄
  have h₅ := abs_suzuki5_β₅_at_suzukiP_le_γ₅
  have h₆ := abs_suzuki5_β₆_at_suzukiP_le_γ₆
  have h₇ := abs_suzuki5_β₇_at_suzukiP_le_γ₇
  have h₈ := abs_suzuki5_β₈_at_suzukiP_le_γ₈
  -- Per-term norm bounds via norm_smul_le + Real.norm_eq_abs.
  have hC₁ : ‖suzuki5_β₁ suzukiP • childsComm₁ A B‖ ≤
      260 / 1000000 * ‖childsComm₁ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
  have hC₂ : ‖suzuki5_β₂ suzukiP • childsComm₂ A B‖ ≤
      663 / 1000000 * ‖childsComm₂ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
  have hC₃ : ‖suzuki5_β₃ suzukiP • childsComm₃ A B‖ ≤
      0 * ‖childsComm₃ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)
  have hC₄ : ‖suzuki5_β₄ suzukiP • childsComm₄ A B‖ ≤
      132 / 1000000 * ‖childsComm₄ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₄ (norm_nonneg _)
  have hC₅ : ‖suzuki5_β₅ suzukiP • childsComm₅ A B‖ ≤
      376 / 1000000 * ‖childsComm₅ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₅ (norm_nonneg _)
  have hC₆ : ‖suzuki5_β₆ suzukiP • childsComm₆ A B‖ ≤
      1128 / 1000000 * ‖childsComm₆ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₆ (norm_nonneg _)
  have hC₇ : ‖suzuki5_β₇ suzukiP • childsComm₇ A B‖ ≤
      0 * ‖childsComm₇ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₇ (norm_nonneg _)
  have hC₈ : ‖suzuki5_β₈ suzukiP • childsComm₈ A B‖ ≤
      442 / 1000000 * ‖childsComm₈ A B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h₈ (norm_nonneg _)
  -- Triangle inequality: chain of seven norm_add_le applications.
  have htri : ‖suzuki5_β₁ suzukiP • childsComm₁ A B + suzuki5_β₂ suzukiP • childsComm₂ A B +
        suzuki5_β₃ suzukiP • childsComm₃ A B + suzuki5_β₄ suzukiP • childsComm₄ A B +
        suzuki5_β₅ suzukiP • childsComm₅ A B + suzuki5_β₆ suzukiP • childsComm₆ A B +
        suzuki5_β₇ suzukiP • childsComm₇ A B + suzuki5_β₈ suzukiP • childsComm₈ A B‖
      ≤ ‖suzuki5_β₁ suzukiP • childsComm₁ A B‖ + ‖suzuki5_β₂ suzukiP • childsComm₂ A B‖ +
        ‖suzuki5_β₃ suzukiP • childsComm₃ A B‖ + ‖suzuki5_β₄ suzukiP • childsComm₄ A B‖ +
        ‖suzuki5_β₅ suzukiP • childsComm₅ A B‖ + ‖suzuki5_β₆ suzukiP • childsComm₆ A B‖ +
        ‖suzuki5_β₇ suzukiP • childsComm₇ A B‖ + ‖suzuki5_β₈ suzukiP • childsComm₈ A B‖ := by
    have := norm_add_le
          (suzuki5_β₁ suzukiP • childsComm₁ A B + suzuki5_β₂ suzukiP • childsComm₂ A B +
           suzuki5_β₃ suzukiP • childsComm₃ A B + suzuki5_β₄ suzukiP • childsComm₄ A B +
           suzuki5_β₅ suzukiP • childsComm₅ A B + suzuki5_β₆ suzukiP • childsComm₆ A B +
           suzuki5_β₇ suzukiP • childsComm₇ A B)
          (suzuki5_β₈ suzukiP • childsComm₈ A B)
    have := norm_add_le
          (suzuki5_β₁ suzukiP • childsComm₁ A B + suzuki5_β₂ suzukiP • childsComm₂ A B +
           suzuki5_β₃ suzukiP • childsComm₃ A B + suzuki5_β₄ suzukiP • childsComm₄ A B +
           suzuki5_β₅ suzukiP • childsComm₅ A B + suzuki5_β₆ suzukiP • childsComm₆ A B)
          (suzuki5_β₇ suzukiP • childsComm₇ A B)
    have := norm_add_le
          (suzuki5_β₁ suzukiP • childsComm₁ A B + suzuki5_β₂ suzukiP • childsComm₂ A B +
           suzuki5_β₃ suzukiP • childsComm₃ A B + suzuki5_β₄ suzukiP • childsComm₄ A B +
           suzuki5_β₅ suzukiP • childsComm₅ A B)
          (suzuki5_β₆ suzukiP • childsComm₆ A B)
    have := norm_add_le
          (suzuki5_β₁ suzukiP • childsComm₁ A B + suzuki5_β₂ suzukiP • childsComm₂ A B +
           suzuki5_β₃ suzukiP • childsComm₃ A B + suzuki5_β₄ suzukiP • childsComm₄ A B)
          (suzuki5_β₅ suzukiP • childsComm₅ A B)
    have := norm_add_le
          (suzuki5_β₁ suzukiP • childsComm₁ A B + suzuki5_β₂ suzukiP • childsComm₂ A B +
           suzuki5_β₃ suzukiP • childsComm₃ A B)
          (suzuki5_β₄ suzukiP • childsComm₄ A B)
    have := norm_add_le
          (suzuki5_β₁ suzukiP • childsComm₁ A B + suzuki5_β₂ suzukiP • childsComm₂ A B)
          (suzuki5_β₃ suzukiP • childsComm₃ A B)
    have := norm_add_le
          (suzuki5_β₁ suzukiP • childsComm₁ A B) (suzuki5_β₂ suzukiP • childsComm₂ A B)
    linarith
  linarith [hC₁, hC₂, hC₃, hC₄, hC₅, hC₆, hC₇, hC₈, htri]

/-- **Tight bridge theorem at Suzuki p** — matches Lean-Trotter's
`bch_w4Deriv_level3_tight` axiom shape. Combines the headline τ⁵
identification with the tight R₅ norm bound via triangle inequality:

    ‖suzuki5_bch − τ•(A+B)‖
      ≤ τ⁵ · bchTightPrefactors.boundSum A B + K·τ⁶

for small non-negative τ. -/
theorem suzuki5_log_product_quintic_tight_at_suzukiP (A B : 𝔸) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, 0 ≤ τ → τ < δ →
      ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B)‖ ≤
        τ ^ 5 * bchTightPrefactors.boundSum A B + K * τ ^ 6 := by
  obtain ⟨δ, hδ_pos, K, hK_nn, hbound⟩ :=
    norm_suzuki5_bch_sub_smul_sub_R5_le A B suzukiP IsSuzukiCubic_suzukiP
  refine ⟨δ, hδ_pos, K, hK_nn, ?_⟩
  intro τ hτ_nn hτ_lt
  have hτ_norm : ‖τ‖ < δ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hτ_nn]; exact hτ_lt
  have h_resid :
      ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B)
         - τ ^ 5 • suzuki5_R5 A B suzukiP‖ ≤
        K * ‖τ‖ ^ 6 := hbound τ hτ_norm
  have hR5_bnd : ‖suzuki5_R5 A B suzukiP‖ ≤ bchTightPrefactors.boundSum A B :=
    norm_suzuki5_R5_at_suzukiP_le_bchTightPrefactors_boundSum A B
  have hτ5_nn : 0 ≤ τ ^ 5 := pow_nonneg hτ_nn 5
  have hτ5_norm : ‖(τ ^ 5 : ℝ)‖ = τ ^ 5 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hτ5_nn]
  have h_smul_bnd :
      ‖τ ^ 5 • suzuki5_R5 A B suzukiP‖ ≤
        τ ^ 5 * bchTightPrefactors.boundSum A B := by
    calc ‖τ ^ 5 • suzuki5_R5 A B suzukiP‖
        ≤ ‖(τ ^ 5 : ℝ)‖ * ‖suzuki5_R5 A B suzukiP‖ := norm_smul_le _ _
      _ = τ ^ 5 * ‖suzuki5_R5 A B suzukiP‖ := by rw [hτ5_norm]
      _ ≤ τ ^ 5 * bchTightPrefactors.boundSum A B := by gcongr
  have hτ6_eq : ‖τ‖ ^ 6 = τ ^ 6 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hτ_nn]
  have h_resid' :
      ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B)
         - τ ^ 5 • suzuki5_R5 A B suzukiP‖ ≤ K * τ ^ 6 := by
    rw [← hτ6_eq]; exact h_resid
  have h_triangle :
      ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B)‖ ≤
        ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B) -
          τ ^ 5 • suzuki5_R5 A B suzukiP‖ +
        ‖τ ^ 5 • suzuki5_R5 A B suzukiP‖ := by
    calc ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B)‖
        = ‖(suzuki5_bch ℝ A B suzukiP τ - τ • (A + B) -
            τ ^ 5 • suzuki5_R5 A B suzukiP) +
            (τ ^ 5 • suzuki5_R5 A B suzukiP)‖ := by congr 1; abel
      _ ≤ ‖suzuki5_bch ℝ A B suzukiP τ - τ • (A + B) -
            τ ^ 5 • suzuki5_R5 A B suzukiP‖ +
            ‖τ ^ 5 • suzuki5_R5 A B suzukiP‖ := norm_add_le _ _
  linarith [h_triangle, h_resid', h_smul_bnd]

end TightBridge

end BCH
