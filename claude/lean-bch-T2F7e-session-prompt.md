# T2-F7e Session Prompt — Discharge Parent Tier-2 Axiom

## Goal

Prove **T2-F7e** (algebraic deg-5 identification of `polynomial_in_y` as
`sym_E₅`) → discharges the parent Tier-2 axiom
`symmetric_bch_quintic_sub_poly_axiom` via the existing
`symmetric_bch_quintic_sub_poly_le_via_T2F7g` helper.

## Current State (after session 17)

- **0 sorries**, **3 axioms** (parent + alt-form stepping stone + axiom 3).
- **15 working lemmas** in T2-F framework (see CLAUDE.md).
- **T2-F7g ⟺ parent axiom** Lean-proved (bidirectional equivalence,
  modulo small tail term).
- The parent's discharge is reduced to proving **T2-F7g**:
  ```
  ‖polynomial_in_y(y) − (a+b) − sym_E₃ − sym_E₅‖ ≤ K · s⁷
  ```
  where `polynomial_in_y(y) = y − y²/2 + y³/3 − y⁴/4 + y⁵/5 − y⁶/6` and
  `y = exp(½a)·exp(b)·exp(½a) − 1`.

## Strategy (recommended)

### Option A: Algebraic identity via explicit polynomial expansion

Show that for `y = exp(½a)·exp(b)·exp(½a) − 1`, the polynomial-in-y
expression equals `(a+b) + sym_E₃ + sym_E₅ + R₇⁺` where `R₇⁺` is
deg-7+ and bounded by O(s⁷).

**Sub-tasks** (T2-F7a-g):
- T2-F7a: deg-1 part of polynomial_in_y = a+b (trivial: y_d1 = a+b)
- T2-F7b: deg-2 part of polynomial_in_y = 0 (palindromic)
- T2-F7c: deg-3 part = sym_E₃ (uses cubic alt-form)
- T2-F7d: deg-4 part = 0 (palindromic)
- T2-F7e: **deg-5 part = sym_E₅** (uses alt-form axiom T2-B)
- T2-F7f: deg-6 part = 0 (palindromic)
- T2-F7g: deg-7+ residual ≤ K · s⁷ (sums per-term contributions)

**Challenge**: "deg-k part" isn't a Lean primitive. Must express via
explicit polynomial expansions of y, y², ..., y⁶ as polynomials in (a, b).

**Estimated effort**: ~500-1000 lines.

### Option B: Extend cubic template `norm_symmetric_bch_cubic_sub_poly_le`

The cubic template at `Basic.lean:5834-6614` (~800 lines) decomposes
`sym_bch_cubic - sym_E₃` into 6 algebraic pieces, each O(s⁵). Extend
to handle `sym_bch_cubic - sym_E₃ - sym_E₅` with 8-10 pieces, each O(s⁷).

**Key infrastructure needed**:
- `symmetric_bch_quintic_poly_alt_form` (currently axiom T2-B): identifies
  the deg-5 contributions as bqt(½a, b) + bqt(½a+b, ½a) + correction.
- `symmetric_bch_sextic_identity`: deg-6 contributions sum to zero
  (palindromic). Analog of `symmetric_bch_quartic_identity` (Basic.lean:5760).

**Per-piece bounds**: each new term needs explicit O(s⁷) constant.
The cubic template's `5×10⁶ + 5000 + ...` chain becomes a longer chain.

**Estimated effort**: ~1000-1500 lines.

## Recommended starting point

1. **Discharge the alt-form axiom T2-B first** (~150-200 lines).
   - Pure polynomial identity in (a, b).
   - Comprehensive scalar enumeration (~71 patterns) + noncomm_ring.
   - Pattern set is in `Lean-Trotter/scripts/discover_quintic_alt_form.py`.
   - Session 17 attempted but failed due to simp matching issues; needs
     goal-state inspection + targeted pattern fix.

2. **Pursue Option B (extend cubic template)** using the discharged alt-form.
   - Mirror the cubic template structure at `Basic.lean:5834`.
   - New decomposition has ~7 terms (per session 17 analysis).
   - Use `norm_bch_sextic_remainder_le` for inner/outer remainders
     (gives O(s⁶), refined by sextic_identity to O(s⁷)).

## Useful framework lemmas (already proved in session 17)

- `BCH.bch_bch_half_eq_logOnePlus_strangBlock_sub_one` — bridge
- `BCH.symmetric_bch_cubic_sub_polynomial_in_y_le` — combined framework
- `BCH.symmetric_bch_quintic_sub_poly_le_via_T2F7g` — parent discharge
  helper (takes T2-F7g witness K, returns parent bound K + tail)

Once T2-F7g is proved with `K = K' · s⁷`, apply this helper to discharge
the parent.

## Key references

- `BCH/Palindromic.lean` lines 730-1240: T2-F1 through T2-F-equiv lemmas.
- `BCH/Basic.lean:5834` — cubic template (norm_symmetric_bch_cubic_sub_poly_le).
- `BCH/Basic.lean:5760` — symmetric_bch_quartic_identity.
- `BCH/Basic.lean:5708` — symmetric_bch_cubic_poly_alt_form.
- `BCH/SymmetricQuintic.lean:1330` — alt-form axiom (T2-B).
- `Lean-Trotter/scripts/discover_quintic_alt_form.py` — CAS pipeline.

## Success criteria

- Parent axiom `symmetric_bch_quintic_sub_poly_axiom` discharged.
- Repository: 0 sorries, 2 axioms (alt-form + axiom 3, both stepping stones).
- All downstream theorems still build:
  `BCH.norm_symmetric_bch_quintic_sub_poly_le`,
  `BCH.norm_strangBlock_log_sub_quintic_target_le`.
