# T2-F7e Session Prompt — Discharge Parent Tier-2 Axiom

## Current State (after session 18)

- **0 sorries**, **2 axioms** (parent + axiom 3 — alt-form discharged session 18).
- **16+ working lemmas** in T2-F framework + alt-form theorem.
- **T2-F7g ⟺ parent axiom** Lean-proved (bidirectional equivalence,
  modulo small tail term).
- **T2-B (alt-form) FULLY PROVED**: `symmetric_bch_quintic_poly_alt_form` in
  `SymmetricQuintic.lean` — 3-line proof via `match_scalars <;> ring`.

## Methodology breakthrough (session 18)

**`match_scalars <;> ring` for poly identities** with rational scalar
coefficients in 𝕂, replacing ×LCM + comprehensive scalar pattern enumeration:

```lean
unfold <all definitions>
simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
  smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
match_scalars <;> ring
```

The `← mul_assoc` is needed when expressions have multi-letter mul products
(e.g. `(½a) * b * (½a)` vs `((½a) * b) * (½a)`).

Refactored proofs:
- `symmetric_bch_cubic_poly_alt_form`: 28 → 5 lines
- `symmetric_bch_quartic_identity`: 56 → 5 lines
- `symmetric_bch_quintic_poly_alt_form` (new): 5 lines

## Goal (T2-F7e via Option B)

Prove the parent Tier-2 axiom:
```
‖sym_bch_cubic - sym_E₃ - sym_E₅‖ ≤ 10⁹ · s⁷ for s < 1/4
```

via extending the cubic template at `Basic.lean:5834` to deg-5 cancellation,
using the sextic identity for deg-6 cancellation.

## Strategy: Extend the cubic template

The cubic template (`norm_symmetric_bch_cubic_sub_poly_le`, ~700 lines)
uses the structural decomposition:

```
sym_bch_cubic - sym_E₃ = R₁ + R₂ + ½[R₁, a'] + ½[C₄(a',b), a']
                       + (C₃(z,a') - C₃(a'+b, a') - C_d4)
                       + (C₄(z,a') - C₄(a'+b, a'))
```

with `quartic_identity` cancelling the deg-4 contributions to get O(s⁵).

For T2-F7e, extend by one degree using:

### Step 1: Extend inner/outer BCH to deg-5
Define:
```
inner_R₆ := bch(a', b) - (a' + b) - ½[a', b] - C₃(a',b)
          - C₄(a', b) - bqt(a', b)
```
(deg-6+ remainder after subtracting the explicit deg-5 contribution).
Bound: `‖inner_R₆‖ ≤ K · s₁⁶` via `norm_bch_sextic_remainder_le`.

### Step 2: Sextic identity (CRITICAL — try `match_scalars <;> ring`)
The sextic identity should state: the sum of all deg-6 contributions
to `sym_bch_cubic - sym_E₃ - sym_E₅` equals zero (palindromic).

**Contributions to enumerate** (some transcendental, some polynomial):
- `bch_sextic_term(a', b)` — leading deg-6 of inner BCH
- `bch_sextic_term(a'+b, a')` — leading deg-6 of outer BCH at constant point
- `½[bqt(a', b), a']` — deg-6
- `(bqt(z, a') - bqt(a'+b, a'))` linear-in-w_d2 — deg-6
- `(C₄(z, a') - C₄(a'+b, a'))` at deg-6 — linear-in-w_d2
- `(C₃(z, a') - C₃(a'+b, a') - C_d4)` at deg-6
- subtraction of `correction` (deg-5 only — no deg-6 contribution)

**Two approaches**:
- **A**: Define `bch_sextic_term` explicitly, then formulate identity as
  pure polynomial in {a, b}. Try `match_scalars <;> ring` (likely works).
- **B**: Directly bound the deg-6 contributions WITHOUT a sextic identity,
  using `norm_bch_septic_remainder_le` (would need new infrastructure).

**Recommendation**: pursue **A** — derive sextic identity via CAS first,
then use `match_scalars <;> ring`.

### Step 3: Extended hdecomp
Mirror `hdecomp` at `Basic.lean:5921`, but with sym_E₅ subtracted and the
deg-5 contributions absorbed via the alt-form lemma:
```
sym_bch_cubic - sym_E₃ - sym_E₅ =
  inner_R₆ + outer_R₆ + ½[bqt(a',b), a'] + ½[inner_R₆, a']
  + (bqt(z, a') - bqt(a'+b, a'))
  + (deg-5 perturbation terms - correction)  [≡ 0 by alt-form]
  + (deg-6 cancellation via sextic identity)
  + (deg-7+ residuals)
```

After cancellations, each remaining piece is O(s⁷).

### Step 4: Per-piece O(s⁷) bounds
Each piece needs an explicit constant. Estimated total: O(K·s⁷) for some
large K (10⁸–10⁹).

## Estimated effort

- **Sextic identity** (if `match_scalars` works): ~50 lines for definition
  of `bch_sextic_term` + 5 lines for the identity proof.
- **Extended hdecomp**: ~150 lines.
- **Per-piece bounds**: ~700 lines.
- **Total**: ~900 lines (down from previous 1500 estimate, leveraging the
  match_scalars methodology).

## Useful framework lemmas

- `BCH.symmetric_bch_quintic_poly_alt_form` — alt-form (NEW session 18, 5 lines)
- `BCH.symmetric_bch_quintic_correction_poly` — the 25-term correction
- `BCH.norm_symmetric_bch_quintic_correction_poly_le` — `‖correction‖ ≤ s⁵`
- `BCH.norm_bch_sextic_remainder_le` — sextic BCH remainder bound
- `BCH.symmetric_bch_quintic_sub_poly_le_via_T2F7g` — parent discharge helper
- `BCH.symmetric_bch_quartic_identity` — deg-4 cancellation (now 5 lines)

## Key references

- `BCH/Basic.lean:5834` — cubic template (~700 lines).
- `BCH/Basic.lean:5708` — `symmetric_bch_cubic_poly_alt_form` (now 5 lines).
- `BCH/Basic.lean:5760` — `symmetric_bch_quartic_identity` (now 5 lines).
- `BCH/SymmetricQuintic.lean:1599` — alt-form theorem (5 lines).
- `Lean-Trotter/scripts/discover_quintic_alt_form.py` — CAS pipeline.

## Success criteria

- Parent axiom `symmetric_bch_quintic_sub_poly_axiom` discharged.
- Repository: 0 sorries, 1 scoped axiom (just axiom 3).
- All downstream theorems still build:
  `BCH.norm_symmetric_bch_quintic_sub_poly_le`,
  `BCH.norm_strangBlock_log_sub_quintic_target_le`.
