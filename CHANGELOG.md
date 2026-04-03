# Changelog — Lean-BCH Formalization

Lab notes: completed tasks, failed approaches, and key decisions.

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
