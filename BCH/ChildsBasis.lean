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

end BCH
