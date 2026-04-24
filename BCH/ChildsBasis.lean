/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH/ChildsBasis — Childs 4-fold commutator basis

Defines the 8 nested 4-fold commutators that form an over-complete basis
for weight-5 elements of the free Lie algebra on `{A, B}`, used for
Suzuki S₄ BCH bounds.

These definitions mirror `LieTrotter/Suzuki4ChildsForm.lean` in the
Lean-Trotter project so that after a rev bump, Lean-Trotter can use
Lean-BCH's versions as rfl-compatible thin wrappers.

## Main definitions

* `BCH.commBr X Y` — plain ring commutator `X*Y - Y*X`.
* `BCH.childsComm₁ A B, …, BCH.childsComm₈ A B` — the 8 nested
  `[X₁,[X₂,[X₃,[B,A]]]]` with `Xᵢ ∈ {A,B}`.
* `BCH.bchFourFoldSum A B` — `Σᵢ ‖childsCommᵢ A B‖`.

The `BCHPrefactors` structure and `bchTightPrefactors` etc. from
Lean-Trotter are deferred to a later module; axiom 1 needs only the
unit-coefficient sum.
-/

import Mathlib.Analysis.Normed.Ring.Basic

namespace BCH

section CommBr

variable {𝔸 : Type*} [Ring 𝔸]

/-- Plain ring commutator `[X, Y] = X·Y - Y·X`. -/
def commBr (X Y : 𝔸) : 𝔸 := X * Y - Y * X

/-!
## The 8 Childs commutators

We enumerate `[X₁, [X₂, [X₃, [B, A]]]]` for `X₁, X₂, X₃ ∈ {A, B}`.
-/

/-- Childs commutator 1: `[A,[A,[A,[B,A]]]]`. -/
def childsComm₁ (A B : 𝔸) : 𝔸 := commBr A (commBr A (commBr A (commBr B A)))

/-- Childs commutator 2: `[A,[A,[B,[B,A]]]]`. -/
def childsComm₂ (A B : 𝔸) : 𝔸 := commBr A (commBr A (commBr B (commBr B A)))

/-- Childs commutator 3: `[A,[B,[A,[B,A]]]]`. -/
def childsComm₃ (A B : 𝔸) : 𝔸 := commBr A (commBr B (commBr A (commBr B A)))

/-- Childs commutator 4: `[A,[B,[B,[B,A]]]]`. -/
def childsComm₄ (A B : 𝔸) : 𝔸 := commBr A (commBr B (commBr B (commBr B A)))

/-- Childs commutator 5: `[B,[A,[A,[B,A]]]]`. -/
def childsComm₅ (A B : 𝔸) : 𝔸 := commBr B (commBr A (commBr A (commBr B A)))

/-- Childs commutator 6: `[B,[A,[B,[B,A]]]]`. -/
def childsComm₆ (A B : 𝔸) : 𝔸 := commBr B (commBr A (commBr B (commBr B A)))

/-- Childs commutator 7: `[B,[B,[A,[B,A]]]]`. -/
def childsComm₇ (A B : 𝔸) : 𝔸 := commBr B (commBr B (commBr A (commBr B A)))

/-- Childs commutator 8: `[B,[B,[B,[B,A]]]]`. -/
def childsComm₈ (A B : 𝔸) : 𝔸 := commBr B (commBr B (commBr B (commBr B A)))

end CommBr

/-!
## Sum of 4-fold commutator norms (unit coefficients)

The Level-2 BCH bound uses this as the RHS: every one of the 8 `βᵢ(p)`
coefficients in the quintic expansion of `log(suzuki5Product τ)` at
IsSuzukiCubic `p` satisfies `|βᵢ(p)| ≤ 1`, so the sum `Σᵢ βᵢ(p)·Cᵢ`
has norm ≤ `bchFourFoldSum A B`.
-/

section FourFoldSum

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Sum of norms of the 8 Childs 4-fold commutators with unit coefficients. -/
def bchFourFoldSum (A B : 𝔸) : ℝ :=
  ‖childsComm₁ A B‖ + ‖childsComm₂ A B‖ + ‖childsComm₃ A B‖ + ‖childsComm₄ A B‖ +
  ‖childsComm₅ A B‖ + ‖childsComm₆ A B‖ + ‖childsComm₇ A B‖ + ‖childsComm₈ A B‖

lemma bchFourFoldSum_nonneg (A B : 𝔸) : 0 ≤ bchFourFoldSum A B := by
  unfold bchFourFoldSum; positivity

end FourFoldSum

/-!
## Weighted Childs-basis sum (BCHPrefactors)

For the Level-3 tight BCH bound, we need a generalization of
`bchFourFoldSum` that uses 8 per-commutator prefactors instead of unit
coefficients.

This mirrors Lean-Trotter's `BCHPrefactors` structure in
`LieTrotter/Suzuki4ViaBCH.lean` so that after a rev bump, Lean-Trotter
can thin-wrap these definitions.
-/

section Prefactors

/-- Structure holding the 8 per-commutator prefactors for Level-3 BCH
bounds. Each `γᵢ` weights the norm of the corresponding
`childsCommᵢ A B`. -/
structure BCHPrefactors where
  γ₁ : ℝ  -- coefficient of ‖[A,[A,[A,[B,A]]]]‖
  γ₂ : ℝ  -- coefficient of ‖[A,[A,[B,[B,A]]]]‖
  γ₃ : ℝ  -- coefficient of ‖[A,[B,[A,[B,A]]]]‖
  γ₄ : ℝ  -- coefficient of ‖[A,[B,[B,[B,A]]]]‖
  γ₅ : ℝ  -- coefficient of ‖[B,[A,[A,[B,A]]]]‖
  γ₆ : ℝ  -- coefficient of ‖[B,[A,[B,[B,A]]]]‖
  γ₇ : ℝ  -- coefficient of ‖[B,[B,[A,[B,A]]]]‖
  γ₈ : ℝ  -- coefficient of ‖[B,[B,[B,[B,A]]]]‖
  nonneg₁ : 0 ≤ γ₁ := by norm_num
  nonneg₂ : 0 ≤ γ₂ := by norm_num
  nonneg₃ : 0 ≤ γ₃ := by norm_num
  nonneg₄ : 0 ≤ γ₄ := by norm_num
  nonneg₅ : 0 ≤ γ₅ := by norm_num
  nonneg₆ : 0 ≤ γ₆ := by norm_num
  nonneg₇ : 0 ≤ γ₇ := by norm_num
  nonneg₈ : 0 ≤ γ₈ := by norm_num

/-- Childs's heuristic prefactors (2021) — balanced-factoring values from
the reference paper. -/
noncomputable def childsPrefactors : BCHPrefactors where
  γ₁ := 0.0047
  γ₂ := 0.0057
  γ₃ := 0.0046
  γ₄ := 0.0074
  γ₅ := 0.0097
  γ₆ := 0.0097
  γ₇ := 0.0173
  γ₈ := 0.0284
  nonneg₁ := by norm_num
  nonneg₂ := by norm_num
  nonneg₃ := by norm_num
  nonneg₄ := by norm_num
  nonneg₅ := by norm_num
  nonneg₆ := by norm_num
  nonneg₇ := by norm_num
  nonneg₈ := by norm_num

/-- **BCH-derived tight prefactors** — rational CEILINGS of
`|βᵢ(suzukiP)|` at the 1/10⁶ grid, where `βᵢ(p)` are the degree-2
polynomial coefficients from the CAS pipeline
`scripts/compute_bch_prefactors.py` (Lean-Trotter) and
`suzuki5_βᵢ` (Lean-BCH).

At Suzuki `p = 1/(4 − 4^(1/3)) ≈ 0.4144908`, the 8 numerical
`|βᵢ(suzukiP)|` values are:
  |β₁| ≈ 0.0002595,  |β₂| ≈ 0.0006624,  |β₃| = 0,       |β₄| ≈ 0.0001317,
  |β₅| ≈ 0.0003757,  |β₆| ≈ 0.0011272,  |β₇| = 0,       |β₈| ≈ 0.0004416.

We store ceilings at the 1/10⁶ grid so that `γᵢ ≥ |βᵢ(suzukiP)|` holds
rigorously (slack ~10⁻⁷ per coefficient). Earlier versions used
truncations which failed the strict inequality for γ₂ and γ₆.

**Every ceiling value is strictly smaller than Childs's heuristic
coefficient** (~9× to ~64× tighter for non-zero values; two are
exactly 0).

Caveat: the Childs 8-commutator basis is over-complete (2 free
parameters in the projection because the weight-5 free Lie algebra is
6-dimensional). We chose the projection setting both free parameters
to zero (giving `γ₃ = γ₇ = 0`). -/
noncomputable def bchTightPrefactors : BCHPrefactors where
  γ₁ := 260 / 1000000   -- ceiling of |β₁(suzukiP)| ≈ 0.0002595
  γ₂ := 663 / 1000000   -- ceiling of |β₂(suzukiP)| ≈ 0.0006624
  γ₃ := 0               -- exact
  γ₄ := 132 / 1000000   -- ceiling of |β₄(suzukiP)| ≈ 0.0001317
  γ₅ := 376 / 1000000   -- ceiling of |β₅(suzukiP)| ≈ 0.0003757
  γ₆ := 1128 / 1000000  -- ceiling of |β₆(suzukiP)| ≈ 0.0011272
  γ₇ := 0               -- exact
  γ₈ := 442 / 1000000   -- ceiling of |β₈(suzukiP)| ≈ 0.0004416
  nonneg₁ := by norm_num
  nonneg₂ := by norm_num
  nonneg₃ := by norm_num
  nonneg₄ := by norm_num
  nonneg₅ := by norm_num
  nonneg₆ := by norm_num
  nonneg₇ := by norm_num
  nonneg₈ := by norm_num

section BoundSum

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Weighted sum of Childs commutator norms:
`Σᵢ γᵢ · ‖childsCommᵢ A B‖`. -/
def BCHPrefactors.boundSum (γ : BCHPrefactors) (A B : 𝔸) : ℝ :=
  γ.γ₁ * ‖childsComm₁ A B‖ + γ.γ₂ * ‖childsComm₂ A B‖ +
  γ.γ₃ * ‖childsComm₃ A B‖ + γ.γ₄ * ‖childsComm₄ A B‖ +
  γ.γ₅ * ‖childsComm₅ A B‖ + γ.γ₆ * ‖childsComm₆ A B‖ +
  γ.γ₇ * ‖childsComm₇ A B‖ + γ.γ₈ * ‖childsComm₈ A B‖

lemma BCHPrefactors.boundSum_nonneg (γ : BCHPrefactors) (A B : 𝔸) :
    0 ≤ γ.boundSum A B := by
  unfold BCHPrefactors.boundSum
  have h₁ := γ.nonneg₁; have h₂ := γ.nonneg₂; have h₃ := γ.nonneg₃
  have h₄ := γ.nonneg₄; have h₅ := γ.nonneg₅; have h₆ := γ.nonneg₆
  have h₇ := γ.nonneg₇; have h₈ := γ.nonneg₈
  have hC₁ := norm_nonneg (childsComm₁ A B)
  have hC₂ := norm_nonneg (childsComm₂ A B)
  have hC₃ := norm_nonneg (childsComm₃ A B)
  have hC₄ := norm_nonneg (childsComm₄ A B)
  have hC₅ := norm_nonneg (childsComm₅ A B)
  have hC₆ := norm_nonneg (childsComm₆ A B)
  have hC₇ := norm_nonneg (childsComm₇ A B)
  have hC₈ := norm_nonneg (childsComm₈ A B)
  positivity

/-- The tight prefactors' bound sum is ≤ the unit-coefficient
`bchFourFoldSum`, since every `γᵢ ≤ 1` in `bchTightPrefactors`
(and actually ≪ 1). -/
lemma bchTightPrefactors_boundSum_le_bchFourFoldSum (A B : 𝔸) :
    bchTightPrefactors.boundSum A B ≤ bchFourFoldSum A B := by
  unfold BCHPrefactors.boundSum bchTightPrefactors bchFourFoldSum
  simp only
  have hC₁ := norm_nonneg (childsComm₁ A B)
  have hC₂ := norm_nonneg (childsComm₂ A B)
  have hC₃ := norm_nonneg (childsComm₃ A B)
  have hC₄ := norm_nonneg (childsComm₄ A B)
  have hC₅ := norm_nonneg (childsComm₅ A B)
  have hC₆ := norm_nonneg (childsComm₆ A B)
  have hC₇ := norm_nonneg (childsComm₇ A B)
  have hC₈ := norm_nonneg (childsComm₈ A B)
  nlinarith

end BoundSum

end Prefactors

end BCH
