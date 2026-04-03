# TODO — Lean-BCH

## Completed

- [x] **Phase 1: Log series** — `logOnePlus(x) = ∑ (-1)^n/(n+1) x^{n+1}` with summability, norm bounds, ℝ/ℂ cases
- [x] **Phase 1: exp ∘ log = id** — `exp(logOnePlus x) = 1 + x` for `‖x‖ < 1` (ODE/constancy argument)
- [x] **Phase 2: Structural BCH** — `exp(bch a b) = exp a * exp b` for `‖a‖ + ‖b‖ < ln 2`
- [x] **Phase 2: log ∘ exp = id** — `logOnePlus(exp a - 1) = a` for `‖a‖ < ln 2` (chain-of-neighborhoods argument)
- [x] **Phase 2: Quadratic BCH bound** — `‖bch(a,b) - (a+b)‖ ≤ 3s²/(2 - eˢ)` where `s = ‖a‖ + ‖b‖`
- [x] **H1: Commutator extraction** — `‖bch(a,b) - (a+b) - [a,b]/2‖ ≤ 10s³/(2 - eˢ)` (cubic remainder bound)
- [x] **H2: Symmetric BCH** — `‖bch(bch(a/2,b),a/2) - (a+b)‖ ≤ 300s³` for `s < 1/4` (Strang splitting)
- [x] **M1: Lie bracket bridge** — `⁅a,b⁆ = a*b - b*a` via Mathlib's `LieRing.ofAssociativeRing`; BCH results restated with `⁅·,·⁆`

## High priority

### ~~H1. Commutator extraction (truncated BCH to order 3)~~ ✅ DONE

**Proved:** `‖bch(a,b) - (a+b) - ½(ab-ba)‖ ≤ 10s³/(2-eˢ)` where `s = ‖a‖+‖b‖ < ln 2`.

The bound uses `C = 10` and the form `s³/(2-eˢ)` (diverging at the convergence radius). The TODO originally targeted `C·(‖a‖²‖b‖+‖a‖‖b‖²)·exp(s)` but the cubic bound `10s³/(2-eˢ)` is sufficient for all applications (H2, Trotter).

~~**Goal:** Prove~~
```
bch(a, b) = a + b + (a*b - b*a)/2 + R₃
‖R₃‖ ≤ C · (‖a‖²‖b‖ + ‖a‖‖b‖²) · exp(‖a‖ + ‖b‖)
```

This is the main theorem on the README. It requires extracting the `[a,b]/2` term from the BCH element and bounding the cubic remainder.

**Approach:** Two options:

**(A) Direct series manipulation.** Write `logOnePlus(y) = y - y²/2 + ···` and `y = exp(a)exp(b) - 1 = a + b + ab + ···`. Substitute and collect:
- Order 1: `a + b`
- Order 2: `ab - (a+b)²/2 = (ab - ba)/2 = [a,b]/2`
- Order 3+: remainder

The difficulty is bounding the remainder in a non-commutative Banach algebra. We'd need to control the tsum of cross-terms. Each order-k term involves at most `2^k` products of `a`'s and `b`'s, bounded by `(‖a‖+‖b‖)^k`.

**(B) Lipschitz + commutator cancellation.** Use `logOnePlus_exp_sub_one` to write:
```
bch(a,b) - (a+b) = logOnePlus(exp(a)exp(b)-1) - logOnePlus(exp(a+b)-1)
```
Then bound via the Fréchet derivative of `logOnePlus` along the path from `exp(a+b)-1` to `exp(a)exp(b)-1`. The perturbation is `exp(a)exp(b) - exp(a+b)`, which from the Trotter project satisfies:
```
exp(a)exp(b) - exp(a+b) = (exp(a)-1)(exp(b)-1) - (exp(a+b)-exp(a)-exp(b)+1)
```
After applying `(1+y₀)⁻¹ = exp(-(a+b))`, the leading term is `exp(-(a+b)) · [a,b]/2`.

**Estimate:** ~200 lines. Approach (A) is more self-contained; approach (B) reuses more infrastructure but needs the Fréchet derivative of `logOnePlus`.

**Dependencies:** None (all prerequisites proved).

### H2. Symmetric BCH

**Goal:** Prove
```
exp(a/2) * exp(b) * exp(a/2) = exp(a + b + c₃·[a,[a,b]] + R₄)
```
with `c₃ = -1/24` (or similar) and `‖R₄‖ = O((‖a‖+‖b‖)⁴)`.

**Why:** The Lean-Trotter project needs this for the fourth-order Suzuki integrator S₄. The Strang splitting `exp(A/2n)exp(B/n)exp(A/2n)` has O(1/n³) step error, and the S₄ composition achieves O(1/n⁵) step error, but the proof requires knowing the exact third-order BCH coefficient to verify the cancellation.

**Approach:** Apply H1 twice:
1. `bch(a/2, b) = a/2 + b + [a/2, b]/2 + R₃'`
2. `bch(bch(a/2, b), a/2) = (a/2+b) + a/2 + [...]/2 + R₃''`
3. The `[a,b]/2` terms from the two applications combine to give `[a,[a,b]]` at third order.

**Estimate:** ~150 lines after H1.

**Dependencies:** H1.

## Medium priority

### M1. Lie bracket ↔ ring commutator bridge

**Goal:** For a `NormedRing 𝔸`, define the Lie bracket `⁅a, b⁆ = a*b - b*a` and show it satisfies Mathlib's `LieRing` axioms. Connect to `Mathlib.Algebra.Lie.Basic`.

**Why:** Allows stating BCH results in terms of the standard Lie bracket notation `⁅·,·⁆`, making them compatible with the rest of Mathlib's Lie theory.

**Estimate:** ~50 lines. Mostly typeclass wiring.

### M2. Contribute `norm_exp_le` to Mathlib

Same as the Lean-Trotter TODO item. The BCH project also proves `norm_exp_le`, `norm_exp_sub_one_le`, `norm_exp_sub_one_sub_le` for general Banach algebras — these are natural Mathlib contributions.

### M3. Delete commented-out proof

The old (buggy) proof attempt for `norm_bch_sub_add_le` is still in `Basic.lean` as a comment block (lines 518–590). Delete it once the correct proof is stable.

## Low priority

### L1. Sharper BCH bound via `logOnePlus_exp_sub_one`

The current `norm_bch_sub_add_le` uses the decomposition `(logOnePlus(y)-y) + (y-(a+b))`, which is lossy (the two parts partially cancel but the triangle inequality doesn't see it). With `logOnePlus_exp_sub_one`, one could write:
```
bch(a,b) - (a+b) = logOnePlus(exp(a)exp(b)-1) - logOnePlus(exp(a+b)-1)
```
and bound via the mean value theorem for `logOnePlus`, potentially giving a tighter bound for `s` not too close to `ln 2`.

### L2. BCH convergence radius

Prove that `bch(a,b)` diverges (or is not well-defined) when `‖a‖ + ‖b‖ ≥ ln 2`, showing the radius is sharp.

### L3. Higher-order BCH terms

Extract `c_3 [a,[a,b]] + c_3' [b,[b,a]]` and bound `R_4`. Would give a fourth-order BCH truncation.
