# T2-F7e Session Prompt — Discharge Parent Tier-2 Axiom

## Current State (after session 18)

- **0 sorries**, **2 axioms** (parent + axiom 3 — alt-form discharged session 18).
- **16+ working lemmas** in T2-F framework + alt-form theorem + sextic term infrastructure.
- **T2-F7g ⟺ parent axiom** Lean-proved (bidirectional equivalence,
  modulo small tail term).
- **T2-B (alt-form) FULLY PROVED**: `symmetric_bch_quintic_poly_alt_form` in
  `SymmetricQuintic.lean` — 3-line proof via `match_scalars <;> ring`.
- **`bch_sextic_term` defined** (NEW session 18): explicit 28-term polynomial
  in {a,b} (LCM 1440, numerators in {±1, ±4, ±6, ±24}). Plus c⁶ homogeneity
  and norm bound `‖Z₆(a,b)‖ ≤ (‖a‖+‖b‖)⁶`.

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

For T2-F7e, extend by one degree. The two key new pieces:

### Piece A: `norm_bch_septic_remainder_le` (~750 lines, MAJOR work)

Need to prove an analog of `norm_bch_quintic_remainder_le` (Basic.lean:2873)
but at one higher degree:

```
‖bch(a, b) - (a+b) - ½[a,b] - C₃(a,b) - C₄(a,b) - bqt(a,b)
            - bch_sextic_term(a, b)‖ ≤ K · s⁷ / (2 - exp(s))
```

(deg-7+ remainder of bch series — uses bch_sextic_term, which is now defined).

This requires:
- A `quintic_identity` analog of `quartic_identity` (at deg-5 cancellation).
- Per-piece O(s⁷) bounds for each algebraic decomposition piece.
- Small-s and large-s case split (mirrors quintic remainder structure).

### Piece B: Extended hdecomp + sextic identity

After `norm_bch_septic_remainder_le` is in place:
1. Replace R₁ with `R₁_new = bch(a',b) - through-deg-6 expansion` (O(s⁷)).
2. Similarly for R₂.
3. Sextic identity: deg-6 contributions sum to zero.
4. Per-piece O(s⁷) bounds.

The sextic identity uses bch_sextic_term(a', b) and bch_sextic_term(a'+b, a')
plus various commutator/perturbation terms. Try `match_scalars <;> ring`
once formulated via CAS.

## Sub-task ordering (recommended)

1. **`quintic_identity` (deg-5 cancellation analog of `quartic_identity`)**
   — pure polynomial identity in (ea, eb, a, b). Try `match_scalars <;> ring`.
   ~10-50 lines.
2. **`norm_bch_septic_remainder_le`** — order-7 BCH remainder bound.
   Mirrors `norm_bch_quintic_remainder_le` (Basic.lean:2873, ~750 lines).
   Has small-s/large-s split.
3. **Extended hdecomp + sextic identity** — algebraic decomposition of
   `sym_bch_cubic - sym_E₃ - sym_E₅` with deg-6 cancellation via sextic
   identity (verifiable via CAS, then `match_scalars <;> ring`).
4. **Per-piece bounds** — analog of cubic template's TERM 1-6 bounds
   but at deg-7. ~300-400 lines.

## Estimated effort

- **`bch_sextic_term`** (DONE session 18): ~365 lines (def + homogeneity + norm bound)
- **`quintic_identity`** (small): ~50 lines
- **`norm_bch_septic_remainder_le`**: ~750 lines (matches quintic remainder template)
- **Extended hdecomp + sextic identity**: ~150 lines
- **Per-piece bounds**: ~400 lines
- **Total remaining**: ~1350 lines

## Useful framework lemmas

- `BCH.symmetric_bch_quintic_poly_alt_form` — alt-form (NEW session 18, 5 lines)
- `BCH.symmetric_bch_quintic_correction_poly` — the 25-term correction
- `BCH.norm_symmetric_bch_quintic_correction_poly_le` — `‖correction‖ ≤ s⁵`
- `BCH.norm_bch_sextic_remainder_le` — sextic BCH remainder bound
- `BCH.symmetric_bch_quintic_sub_poly_le_via_T2F7g` — parent discharge helper
- `BCH.symmetric_bch_quartic_identity` — deg-4 cancellation (now 5 lines)
- `BCH.bch_sextic_term` — deg-6 of bch series (NEW session 18, 28 terms)
- `BCH.bch_sextic_term_smul` — homogeneity (NEW)
- `BCH.norm_bch_sextic_term_le` — `‖Z₆(a,b)‖ ≤ s⁶` (NEW)

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
