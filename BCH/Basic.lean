/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BCH Basic: Truncated Baker-Campbell-Hausdorff bounds

The first non-trivial BCH bound:
  `exp(A) * exp(B) = exp(A + B + [A,B]/2 + R₃)`
where `‖R₃‖ ≤ C(‖A‖²‖B‖ + ‖A‖‖B‖²) exp(‖A‖+‖B‖)`.
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open NormedSpace

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

-- TODO: BCH bounds to be implemented
-- See README.md for the proof plan
