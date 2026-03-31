# Changelog — Lean-BCH Formalization

Lab notes: completed tasks, failed approaches, and key decisions.

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
