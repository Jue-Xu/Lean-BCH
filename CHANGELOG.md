# Changelog — Lean-BCH Formalization

Lab notes: completed tasks, failed approaches, and key decisions.

---

## 2026-04-22: Symmetric BCH quintic — algebraic core complete

**What:** Closed the algebraic core of `norm_symmetric_bch_cubic_sub_poly_le`,
the symmetric BCH quintic remainder theorem. All ring identities and the
decomposition equality are proven; only a constant-bound bookkeeping step
remains (the stated constant `4000` is mathematically too small).

**Closed this session:**

1. **`symmetric_bch_quartic_identity`** — the four degree-4 contributions
   to `sym_bch_cubic - sym_E₃` sum to zero as a ring identity:
   `½[C₃(a',b),a'] + C₄(a',b) + (-(1/96)·[b,DC_a]) + C₄(a'+b,a') = 0`.
   Proved via 192-scaling + scalar clearing (5-level deep) + `noncomm_ring`.
   Mathematical content: `[DC_b, a] = [b, DC_a]` (both expand to
   `b²a² - 2baba + 2abab - a²b²` in any associative algebra).

2. **`symmetric_bch_cubic_poly_alt_form`** — closed-form and alt-form
   representations of `sym_E₃` agree:
   `-(1/24)[a,[a,b]] + (1/12)[b,[b,a]] = C₃(½a,b) + C₃(½a+b,½a) - (1/16)·DC_a`.
   Proved via 48-scaling + 3-level scalar clearing + `ofNat_smul_eq_nsmul`
   + `noncomm_ring`.

3. **`symmetric_bch_cubic_poly`** + **`symmetric_bch_cubic_poly_smul`** —
   the explicit cubic-poly definition of sym_E₃ and its c³-homogeneity.

4. **Decomposition equality** (inside `norm_symmetric_bch_cubic_sub_poly_le`):
   ```
   sym_bch_cubic - sym_E₃ = R₁ + R₂ + ½[R₁,a'] + ½[C₄(a',b),a']
                          + (C₃(z,a') - C₃(a'+b,a') + (96)⁻¹·[b,DC_a])
                          + (C₄(z,a') - C₄(a'+b,a'))
   ```
   Proved by combining (A) R₂-def substitution, (B) R₁-def substitution,
   (C) the quartic identity, (D) the alt-form identity. Final step uses
   `linear_combination (norm := abel)` with the witness
   `(2:𝕂)⁻¹•a + (2:𝕂)⁻¹•a = a` to bridge a mixed ℕ-smul/𝕂-smul gap that
   `smul_smul` couldn't close directly.

5. **`norm_symmetric_bch_cubic_sub_smul_le`** (main user-facing theorem) is
   now sorry-free — both large-s (crude bound) and small-s (helper-based)
   cases closed, contingent on the helper bound holding.

**Open issue:** the helper's stated constant `4000·s⁵` is mathematically
incorrect for s near 1/4 — `R₂` alone yields `~400000·s⁵` because
`s₂ = ‖z‖+‖a'‖ ≈ 0.523 ≫ s` near the boundary. To close the remaining
triangle-inequality sorry, the helper bound needs either a larger constant
(~10⁶) or a denominator `(2-exp(2s))` analogous to `norm_bch_quintic_remainder_le`.

**Build:** Clean: 26:41.90; Cached: 23:43.32; Incremental BCH module: ~10s.

**Commit count this session:** 13 commits totaling significant Lean code
(several hundred lines), 1 sorry remaining (constant-bound bookkeeping).

---

## 2026-04-21: Quintic BCH sorry-free — `quintic_pure_identity` closed

**What:** Closed the last sorry in `norm_bch_quintic_remainder_le` by closing
the `quintic_pure_identity` ring identity (line 2260). The fifth-order BCH
theorem is now fully proved.

**Problem:** Prior attempt converted against `quintic_pure_identity_cleared`
(a scalar-free version) via `convert ... using 2`, leaving residual nsmul
instance-equality goals from the `NormedAlgebra 𝕂` vs `NormedRing` nsmul
diamond — couldn't be closed by `rfl`.

**Solution:** Dropped the convert detour entirely. Two fixes make direct
`noncomm_ring` work after scalar clearing:

1. **Pre-expand powers:** Added `simp only [pow_succ, pow_zero, one_mul]`
   before the main distribution pass. This unfolds `P₂^2`, `(a+b)^4`, etc.
   into explicit products so that the `(2:𝕂)⁻¹ •` smuls hiding inside
   `P₂ = ab + ½a² + ½b²` participate in scalar clearing.

2. **Intermediate cancellation rules:** Added
   `(12:𝕂) * (2:𝕂)⁻¹ = 6`, `(6:𝕂) * (2:𝕂)⁻¹ = 3`, `(4:𝕂) * (2:𝕂)⁻¹ = 2`,
   `(8:𝕂) * (2:𝕂)⁻¹ = 4`, `(12:𝕂) * ((2:𝕂)⁻¹ * (2:𝕂)⁻¹) = 3` to handle
   the partial-cancellation forms that simp produces when scalars combine
   in different orders (e.g. after `(24:𝕂) * (2:𝕂)⁻¹ = 12` fires, the
   remaining `(12:𝕂) * (2:𝕂)⁻¹` needed its own rule).

After clearing, the goal is a pure ring/nsmul identity and `noncomm_ring`
handles it directly — no dependency on `quintic_pure_identity_cleared`.

**Status:** `norm_bch_quintic_remainder_le` is sorry-free. One sorry
remains (small-s case of `norm_symmetric_bch_cubic_sub_smul_le`, line 3624)
— requires a new *symmetric* BCH quintic remainder theorem to bridge from
the regular BCH quintic to the symmetric composition.

---

## 2026-04-02: M1 + documentation — Lie bracket bridge, README, CLAUDE.md

**What:** Added Lie bracket notation wrappers (`norm_bch_sub_add_sub_lie_le`, etc.)
via `import Mathlib.Algebra.Lie.OfAssociative`. Updated README with full results table,
relation to [Lean-Trotter](https://github.com/Jue-Xu/Lean-Trotter) project, and file structure.
Created CLAUDE.md with project constraints and key techniques.

**Lean-Trotter connection:**
- Lean-Trotter proves first-order Lie–Trotter and second-order Strang via direct exp bounds
- Lean-BCH H2 gives an alternative BCH-based proof that Strang is second-order
- Lean-BCH H1 provides the commutator extraction needed for fourth-order Suzuki S₄ (future)

---

## 2026-04-02: H2 complete — Symmetric BCH (Strang splitting), 0 sorry's

**What:** Proved `norm_symmetric_bch_sub_add_le`: the cubic remainder bound
`‖bch(bch(a/2,b),a/2) - (a+b)‖ ≤ 300·s³` for `s = ‖a‖+‖b‖ < 1/4`.

This shows the Strang splitting `exp(a/2)·exp(b)·exp(a/2) = exp(a+b+O(s³))` — the
commutator `[a/2,b]` from the two BCH applications cancels, leaving only cubic error.

**Proof strategy:**
1. Apply H1 twice: `z = bch(a/2,b) = a/2+b+½[a/2,b]+R₃'` and `bch(z,a/2) = z+a/2+½[z,a/2]+R₃''`
2. Ring identity: `[z,a'] + [a',b] = [z-a'-b, a']` (commutator cancellation)
3. Since `‖z-a'-b‖ = O(s²)`, the bracket `[z-a'-b, a']` is `O(s³)`
4. Remaining terms `R₃'`, `R₃''` are cubic by H1

**Key challenge:** Verifying `‖z‖+‖a/2‖ < ln 2` for the second BCH application,
using `‖bch(a',b)-(a'+b)‖ ≤ 3s₁²/(2-exp s₁)` and `s < 1/4`.

---

## 2026-04-02: H1 complete — Commutator extraction, 0 sorry's

**What:** Proved `norm_bch_sub_add_sub_bracket_le`: the cubic remainder bound
`‖bch(a,b) - (a+b) - ½(ab-ba)‖ ≤ 10s³/(2-eˢ)` where `s = ‖a‖+‖b‖ < ln 2`.

**New lemmas (LogSeries.lean):**
- `logSeriesTerm_one`: `logSeriesTerm x 1 = -(2⁻¹ • x²)`
- `summable_logSeriesTerm_shift2`: double-shifted summability
- `logOnePlus_sub_sub_eq_tsum`: `logOnePlus(x) - x + ½x² = ∑' logSeriesTerm(x, n+2)`
- `norm_logOnePlus_sub_sub_le`: `‖logOnePlus(x) - x + ½x²‖ ≤ ‖x‖³/(1-‖x‖)`

**New lemmas (Basic.lean):**
- `norm_exp_sub_one_sub_sub_le`: third-order exp remainder `‖exp(x)-1-x-½x²‖ ≤ exp(‖x‖)-1-‖x‖-‖x‖²/2`
- `real_exp_third_order_le_div`: `exp(s)-1-s-s²/2 ≤ s³/(6(1-s))` for `0 ≤ s < 1`
- `real_exp_third_order_le_cube`: `exp(s)-1-s-s²/2 ≤ s³` for `0 ≤ s < 5/6`
- `norm_bch_sub_add_sub_bracket_le`: the main theorem

**Proof strategy:**
1. Decompose `bch - (a+b) - [a,b]/2` into piece A (cubic log tail) + piece B (algebraic)
2. Piece A: `logOnePlus(y) - y + ½y²` bounded by `(eˢ-1)³/(2-eˢ)` via `norm_logOnePlus_sub_sub_le`
3. Piece B: Use the identity `W = 2(E₁+E₂+aD₂+D₁b+D₁D₂) - (a+b)P - P(a+b) - P²`
   proved by multiplying through by 2 (avoiding ½ scalar issues) then `noncomm_ring`
4. Bound each component, combine with `nlinarith` using Taylor bound `exp(s) ≤ 1+s+s²`

**Key technique for the algebraic identity:**
The scalar `(2:𝕂)⁻¹ •` doesn't interact with `noncomm_ring` or `abel`. Solution: multiply
both sides by `(2:𝕂)`, clear the scalar via `smul_smul` + `inv_mul_cancel₀` + `one_smul`,
then use `noncomm_ring` on the resulting scalar-free identity. The injectivity of `(2:𝕂) • ·`
recovers the original.

**Cleanup:** Deleted the commented-out old proof attempt for `norm_bch_sub_add_le` (TODO item M3).

---

## 2026-03-31: Phase 2 complete — 0 sorry's, full build passes

**What:** Filled the two remaining sorry's. The BCH structural layer is now fully proved.

**`logOnePlus_exp_sub_one` — log inverts exp:**
- Statement: `logOnePlus(exp(a) - 1) = a` for `‖a‖ < ln 2`
- Proof strategy: **chain-of-neighborhoods** (avoids computing derivatives of `logOnePlus(exp(ta)-1)`)
  1. Define `h(t) = logOnePlus(exp(ta)-1) - ta` on `[0,1]`
  2. Show `h(0) = 0` and `exp(h(t)) = 1` algebraically (via `exp_logOnePlus` + commutativity)
  3. Prove `logOnePlus` is continuous on closed balls (`continuousOn_logOnePlus` via `continuousOn_tsum`)
  4. By uniform continuity on compact `[0,1]`, find `δ > 0`
  5. Induction with step `1/N < δ`: each step uses `exp_eq_one_of_norm_lt`
  6. Conclude `h(1) = 0`

**`norm_bch_sub_add_le` — BCH remainder bound:**
- **Bound corrected** from `2s²·exp(s)` to `3s²/(2-exp(s))`.
  The original bound was provably wrong (fails at `s ≈ 0.4` — the decomposition bound
  `(exp(s)-1)/(2-exp(s)) - s` diverges as `s → ln 2`, so no fixed `C·s²·exp(s)` works).
- The corrected bound `3s²/(2-exp(s))` is tight near `s = 0` (leading term `3s²/2`)
  and correctly diverges at `s = ln 2`.
- Key inequality: `exp(s)(1+s) ≤ 1+2s+3s²` for `s < ln 2`, proved via
  `Real.norm_exp_sub_one_sub_id_le` (gives `exp(s) ≤ 1+s+s²`) and `s³ ≤ s²`.

**New helper lemmas:**
- `continuous_logSeriesTerm`: each `y ↦ logSeriesTerm y n` is continuous
- `continuousOn_logOnePlus`: `logOnePlus` is continuous on `closedBall 0 r` for `r < 1`

**Failed approaches for `logOnePlus_exp_sub_one`:**
- Direct norm bound `‖L-a‖ < ln 2`: diverges for `‖a‖ > 0.44`, only works for small norms
- ODE/derivative approach on `logOnePlus(exp(ta)-1)`: requires chain rule for `logOnePlus`
  as a function of its Banach algebra argument — would need term-by-term differentiation
  of `∑ cₙ(exp(ta)-1)^{n+1}`, too heavy
- Linear parameterization `logOnePlus(t·(exp(a)-1))`: its derivative is NOT `a`
  (it's `(1+t·y)⁻¹·y` where `y = exp(a)-1`), so ODE constancy doesn't apply

**Lessons learned:**
- The chain-of-neighborhoods argument is simpler than the ODE approach when you only need
  the function VALUE (not its derivative). Uniform continuity + local injectivity replaces
  the entire derivative computation.
- `continuousOn_tsum` (Weierstrass M-test) is the right tool for continuity of power series
  on closed balls. Works cleanly with `ContinuousOn.comp` for compositions.
- Always check bounds numerically before attempting a Lean proof. The `2s²·exp(s)` bound
  would have wasted days if we'd tried to prove it.

---

## 2026-03-31: Phase 2 infrastructure — helper lemmas (`e56f49f`)

**What:** Added building blocks for the two remaining sorry's.

**New proved lemmas:**
- `norm_exp_sub_one_sub_le`: B4 bound `‖exp(x)-1-x‖ ≤ exp(‖x‖)-1-‖x‖`
- `exp_eq_one_of_norm_lt`: local injectivity `exp(z)=1 ∧ ‖z‖<ln2 → z=0`
- `commute_logOnePlus_of_commute`: `Commute x a → Commute (logOnePlus x) a`

**Two sorry's remain:**
1. `logOnePlus_exp_sub_one` — strategy: connectedness on [0,1], blocked on `restrictScalars` typeclass
2. `norm_bch_sub_add_le` — strategy: decompose + B4, may need to adjust constant

---

## 2026-03-31: Phase 2 core — `exp(bch a b) = exp a * exp b` (`1672886`)

**What:** The structural BCH theorem. For `‖a‖+‖b‖ < ln 2`:
- Defined `bch(a,b) = logOnePlus(exp(a)*exp(b) - 1)`
- Proved `exp(bch a b) = exp a * exp b` via `exp_logOnePlus`
- Proved smallness condition `‖exp(a)exp(b)-1‖ < 1`
- Proved `norm_exp_le` and `norm_exp_sub_one_le` for general Banach algebras

---

## 2026-03-31: Phase 1 complete — `exp(logOnePlus x) = 1+x` (`18a2f85`)

**What:** The hardest lemma in the project, fully proved.

**Proof (ODE argument):**
1. Define `Q(t) = exp(-logOnePlus(tx)) · (1+tx)`
2. Show `Q(0) = 1`
3. Show `Q` differentiable via `hasDerivAt_tsum` for the log series
4. Show `Q'(t) = 0`: L'(t) = (1+tx)⁻¹·x (Neumann series), cancellation in product rule
5. Conclude `Q ≡ 1` by `is_const_of_deriv_eq_zero`

**Key insight:** Commutativity in the x-algebra ensures the exp chain rule applies.

**Failed approaches:**
- `variable (𝕂) in` with doc comments — parser issues (same as Trotter)
- Direct power series composition — too heavy, Mathlib's `FormalMultilinearSeries.comp` is unwieldy
- Real case extension — proved `exp_logOnePlus_real` and `exp_logOnePlus_complex` but couldn't extend to general 𝔸 without the ODE argument

---

## 2026-03-30: Phase 1 partial — log series + ℝ/ℂ cases (`f9a62d9`)

**What:** Log series infrastructure + exp∘log identity for ℝ and ℂ.

**Proved:**
- `logOnePlus` definition via alternating power series
- 9 lemmas: summability, norm bounds, shifted series
- `logOnePlus_real_eq`: log series = `Real.log(1+t)` via `Real.hasSum_pow_mul_geometric`
- `exp_logOnePlus_real`: exp∘log = id for ℝ via `Real.exp_log`
- `hasSum_logSeriesTerm_complex`: log series = `Complex.log(1+z)` via `Complex.hasSum_taylorSeries_log`
- `exp_logOnePlus_complex`: exp∘log = id for ℂ

---

## 2026-03-30: Initial commit (`e710047`)

**What:** Project scaffold with Lean 4.29.0-rc8 + Mathlib dependency. Stub files.

**Repository:** https://github.com/Jue-Xu/Lean-BCH (private)
