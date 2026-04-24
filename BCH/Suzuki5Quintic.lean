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

end BCH
