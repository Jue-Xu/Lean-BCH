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

This theorem is currently accepted from a scoped **Tier-2 axiom**
(`suzuki5_R5_identification_axiom`). The underlying fact is the symbolic
5-factor BCH composition identity: after substituting the quintic Taylor
expansions of each `strangBlock_log` block into the 5-factor decomposition

    suzuki5_bch = bch(bch(2•X, Y), 2•X)      -- X = sb_log_p, Y = sb_log_q

and collecting terms, the τ⁵ coefficient projects onto the 8 Childs 4-fold
commutators with the polynomial prefactors `βᵢ(p)` enumerated earlier in
this file (matching the CAS pipeline at
`Lean-Trotter/scripts/compute_bch_prefactors.py`).

Removing the axiom requires three tiers of Lean-BCH work:

* **Tier 1** (~1–2 days): quintic Taylor expansion of each
  `strangBlock_log A B c τ`, identifying the τ³ coefficient as
  `(cτ)³•symmetric_bch_cubic_poly A B` (already in `Basic.lean`) and the
  τ⁵ coefficient as a new `strangBlock_R5 A B`. Template: the 2-factor
  `norm_symmetric_bch_cubic_sub_smul_le` in `Basic.lean`.

* **Tier 2** (~1 week, the hardest): symbolic triple-BCH composition in
  the free algebra. Substitute the Tier 1 expansion into the 5-factor
  decomposition and expand via the BCH cubic remainder
  `norm_bch_sub_add_sub_bracket_le` (H1). Collect the τ⁵ coefficient and
  apply Gauss-Jordan in the 4-fold commutator basis to match
  `suzuki5_R5`. LCM of denominators ≈ 144000 — use scalar-clearing
  `noncomm_ring` after multiplying both sides.

* **Tier 3** (~1 day): triangle-inequality residual bounding. Combine
  Tier 1/Tier 2 symbolic residuals with the existing
  `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (quintic-magnitude M4b
  bound) to get the O(τ⁶) tail.

The axiom is introduced `private` to its declaring section so that only
`norm_suzuki5_bch_sub_smul_sub_R5_le` (and the downstream bridge corollary)
appears as a `theorem` in the public API.
-/

section HeadlineTheorem

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
  [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **[Tier-2 axiom, pending]** — The symbolic 5-factor BCH identification
that the τ⁵ coefficient of `suzuki5_bch` in the Childs 4-fold commutator
basis is `suzuki5_R5`.

This axiom captures what would otherwise require a multi-week symbolic
non-commutative BCH expansion in Lean (see docstring of
`norm_suzuki5_bch_sub_smul_sub_R5_le` for the Tier 1/2/3 roadmap).

Introduced `private` so only the public
`norm_suzuki5_bch_sub_smul_sub_R5_le` theorem is visible to downstream
callers. -/
private axiom suzuki5_R5_identification_axiom
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, ‖τ‖ < δ →
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖
        ≤ K * ‖τ‖ ^ 6

/-- **Headline theorem (τ⁵ identification)**: Under `IsSuzukiCubic p`,
`suzuki5_bch` has leading-order quintic expansion

    suzuki5_bch ℝ A B p τ = τ•(A+B) + τ⁵ • suzuki5_R5 A B p + O(τ⁶)

where `suzuki5_R5 A B p` is the explicit Childs 4-fold commutator
projection with polynomial prefactors `βᵢ(p)` (see
`Suzuki5Quintic.lean` header).

Quantitatively: `∃ δ > 0, ∃ K ≥ 0, ∀ τ, |τ| < δ →
  ‖suzuki5_bch ℝ A B p τ − τ•(A+B) − τ⁵•suzuki5_R5 A B p‖ ≤ K·|τ|⁶`.

**Status**: Currently derived from the scoped Tier-2 axiom
`suzuki5_R5_identification_axiom`. The public signature is preserved so
downstream proofs (e.g. the bridge corollary
`suzuki5_log_product_quintic_of_IsSuzukiCubic` in `Palindromic.lean` and
Lean-Trotter's `bch_w4Deriv_quintic_level2`) depend only on this theorem,
not on the private axiom. Removing the axiom requires the Tier 1/2/3 work
described in the module header. -/
theorem norm_suzuki5_bch_sub_smul_sub_R5_le
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, ‖τ‖ < δ →
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖
        ≤ K * ‖τ‖ ^ 6 :=
  suzuki5_R5_identification_axiom A B p hcubic

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
