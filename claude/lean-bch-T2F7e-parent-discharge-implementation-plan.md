# T2-F7e Parent Discharge — Detailed Implementation Plan

**Target axiom**: `BCH.symmetric_bch_quintic_sub_poly_axiom` in
`BCH/SymmetricQuintic.lean:1690`.

**Statement to prove** (for `‖a‖+‖b‖ < 1/4`):
```
‖symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b
    − symmetric_bch_quintic_poly 𝕂 a b‖ ≤ 10⁹ · (‖a‖+‖b‖)⁷
```

**Strategy**: Extend the cubic template
`norm_symmetric_bch_cubic_sub_poly_le` (`Basic.lean:8601`) to one
degree higher.

## Mathematical structure

### Setup (mirrors cubic template)

- `a' := (1/2)·a`
- `s := ‖a‖+‖b‖`, `s₁ := ‖a'‖+‖b‖ ≤ s`, `s₂ := ‖z‖+‖a'‖ ≤ (57/22)·s`
- `z := bch(a', b)`
- `W := z − (a'+b)`

### Inner+outer septic remainders (NEW vs cubic template)

```
R₁_sept := bch(a',b) − (a'+b) − ½[a',b] − C₃(a',b) − C₄(a',b)
                                         − C₅(a',b) − C₆(a',b)
```
Bound: `‖R₁_sept‖ ≤ 1000010 · s₁⁷ / (2 − exp(s₁))` via
`norm_bch_septic_remainder_le`.

```
R₂_sept := bch(z,a') − (z+a') − ½[z,a'] − C₃(z,a') − C₄(z,a')
                                          − C₅(z,a') − C₆(z,a')
```
Bound: `‖R₂_sept‖ ≤ 1000010 · s₂⁷ / (2 − exp(s₂))` via
`norm_bch_septic_remainder_le`.

### Key derivation (algebraic)

From the inner+outer septic expansions:
```
sym_bch_cubic = bch(z,a') − (a+b)
              = ½[a',b] + C₃(a',b) + C₄(a',b) + C₅(a',b) + C₆(a',b) + R₁_sept
                + ½[z,a'] + C₃(z,a') + C₄(z,a') + C₅(z,a') + C₆(z,a') + R₂_sept
```

Using `½[z,a'] = ½[(a'+b)+W, a'] = −½[a',b] + ½[W,a']`:
```
sym_bch_cubic = ½[W,a'] + C₃(a',b) + C₄(a',b) + C₅(a',b) + C₆(a',b) + R₁_sept
              + C₃(z,a') + C₄(z,a') + C₅(z,a') + C₆(z,a') + R₂_sept
```

Using `½[W,a'] = ¼[[a',b],a'] + ½[C₃(a',b),a'] + ½[C₄(a',b),a']
              + ½[C₅(a',b),a'] + ½[C₆(a',b),a'] + ½[R₁_sept,a']`:
and `¼[[a',b],a'] = −(1/16)·DC_a` where `DC_a = a·[a,b] − [a,b]·a`:

Apply alt-form for `sym_E₃ = C₃(a',b) + C₃(a'+b, a') − (1/16)·DC_a`
(absorbs `−(1/16)·DC_a + C₃(a',b)` into the sym_E₃ subtraction).

Apply alt-form for `sym_E₅ = C₅(a',b) + C₅(a'+b, a') + correction(a, b)`
(absorbs `+C₅(a',b)`).

Apply quartic_identity to absorb `½[C₃(a',b),a'] + C₄(a',b)` into
`(1/96)·[b,DC_a] − C₄(a'+b, a')`.

Result: **EXTENDED HDECOMP** (11 pieces):
```
sym_bch_cubic − sym_E₃ − sym_E₅ =
  R₁_sept + R₂_sept + ½[R₁_sept, a']            -- DEG-7+ pieces, obvious O(s⁷)
+ ½[C₆(a',b), a'] + ½[C₆(z,a') − C₆(a'+b,a'),a'] -- DEG-7+ pieces
+ T₅ + T₆ + ½[C₄(a',b), a'] − correction         -- DEG-5 cancellation group
+ ½[C₅(a',b), a'] + C₆(a',b) + C₆(a'+b, a')      -- DEG-6 cancellation group  
+ (C₅(z,a') − C₅(a'+b, a'))                      -- DEG-6+ residual
```

Where:
- `T₅ := (C₃(z,a') − C₃(a'+b,a')) + (1/96)·[b, DC_a]` (cubic template's T₅)
- `T₆ := C₄(z,a') − C₄(a'+b, a')` (cubic template's T₆)

## Algebraic identities needed

### Identity 1: deg-5 cancellation
The deg-5 contributions of `T₅ + T₆ + ½[C₄(a',b), a']` should equal
`correction` modulo deg-7+ residuals. Specifically, in the polynomial
ring 𝕂⟨a, b⟩:

**deg-5 contributions**:
- ½[C₄(a',b), a'] is purely deg-5.
- deg-5 of T₅ = (quadratic-W₂² in C₃ at z=W₂+W₂) + (linear-W₃ in C₃ at z=W₃)
  where W₂ = ½[a',b], W₃ = C₃(a',b).
- deg-5 of T₆ = linear-W₂ in C₄ at z=W₂.

**Identity**: The above sum minus `correction(a, b)` is a deg-7+ polynomial
in (a, b). Specifically:
```
½[C₄(a',b), a'] + (deg-5 of T₅) + (deg-5 of T₆) − correction = 0
```

Provable by `match_scalars <;> ring` after explicit polynomial expansion.

### Identity 2: deg-6 cancellation
The deg-6 contributions sum to 0 (palindromic vanishing):
```
½[C₅(a',b), a'] + C₆(a',b) + C₆(a'+b, a')
+ (deg-6 of T₅) + (deg-6 of T₆) + (deg-6 of (C₅(z,a') − C₅(a'+b,a')))
= 0
```

Where:
- deg-6 of T₅ = linear-W₄ + (W₂·W₃) + (W₃·W₂) + cubic-W₂³ in C₃.
- deg-6 of T₆ = linear-W₃ + quadratic-W₂² in C₄.
- deg-6 of (C₅(z,a') − C₅(a'+b, a')) = linear-W₂ in C₅.

Provable by `match_scalars <;> ring` after explicit polynomial expansion.

### Combined approach (recommended)

Rather than two separate identities, prove ONE combined identity expressing
the full deg-5+6 cancellation as an explicit polynomial equation. The
RHS would be the explicit deg-7+ polynomial residue (computed by CAS).

## Per-piece norm bounds

| Piece | Estimated bound | Notes |
|-------|----------------|-------|
| `R₁_sept` | ≤ K · s⁷ | direct from `norm_bch_septic_remainder_le` |
| `R₂_sept` | ≤ K · s⁷ | direct from `norm_bch_septic_remainder_le` |
| `½[R₁_sept, a']` | ≤ K · s⁸ ≤ K' · s⁷ | commutator with deg-1 |
| `½[C₆(a',b), a']` | ≤ K · s⁷ | commutator: s⁶ · s |
| `½[C₆(z,a') − C₆(a'+b,a'), a']` | ≤ K · s⁸ | linear-W contribution to C₆ |
| Deg-5+6 cancellation residue | ≤ K · s⁷ | via algebraic identity |

Total constant: should be ≤ 10⁵·s⁷, well within the 10⁹ budget.

## File organization

The proof should go in `BCH/SymmetricQuintic.lean`:
1. Replace the `private axiom symmetric_bch_quintic_sub_poly_axiom`
   (line 1690) with the proven theorem.
2. Add helper lemmas above as `private lemma`s.

Estimated total: ~1000-1500 lines.

## Recommended session breakdown

- **Session 1**: Phase A — set up the `set` chain (a', s₁, z, s₂, R₁_sept, R₂_sept), prove the inner+outer septic bounds + s₂ bounds. ~200 lines.
- **Session 2**: Phase B — formulate and prove the deg-5 cancellation identity via `match_scalars <;> ring`. ~150 lines (mostly the identity statement).
- **Session 3**: Phase C — formulate and prove the deg-6 cancellation identity. ~200 lines.
- **Session 4**: Phase D — extended hdecomp proof, combining identities. ~150 lines.
- **Session 5**: Phase E — per-piece norm bounds + triangle assembly + axiom replacement. ~300 lines.
- **Session 6** (buffer): Heartbeat tuning, refactor, doc updates. ~100 lines.

## CAS support needed

The deg-5+6 algebraic identities are provable by `match_scalars <;> ring`,
but their EXPLICIT RHS (the deg-7+ residual polynomial) needs to be
computed by a CAS pipeline.

Recommended CAS work:
- Compute the explicit deg-7+ residual of the full sum
  `T₅ + T₆ + ½[C₄(a',b), a'] − correction
   + ½[C₅(a',b), a'] + C₆(a',b) + C₆(a'+b, a') + (C₅(z,a') − C₅(a'+b,a'))`
  with z = (a'+b) + W where W is the explicit Taylor expansion to deg-6.
- Express the residue as an explicit polynomial in (a, b) (with rational
  coefficients) — this becomes the RHS of the algebraic identity.

## Tactical notes

- `match_scalars <;> ring` is the recommended tactic for polynomial
  identities. Use heartbeat budget 8M-32M depending on complexity.
- For LARGE identities (200+ monomials), consider splitting into
  sub-identities first.
- The cubic template uses `linear_combination (norm := abel)` for the
  scalar-clearing pattern; `match_scalars <;> ring` is the modern
  replacement.
- The cubic template proof is 700 lines; the quintic version is
  estimated at 1000-1500 lines (more pieces, more bounds).

## Cross-reference to existing infrastructure

- `Basic.lean:8601` `norm_symmetric_bch_cubic_sub_poly_le` — cubic template
- `Basic.lean:8577` `symmetric_bch_quartic_identity` — deg-4 cancellation
- `Basic.lean:8550` `symmetric_bch_cubic_poly_alt_form` — sym_E₃ alt form
- `SymmetricQuintic.lean:1600` `symmetric_bch_quintic_poly_alt_form` — sym_E₅ alt form
- `SymmetricQuintic.lean:1280` `symmetric_bch_quintic_correction_poly` — the 25-term correction
- `Basic.lean:7930` `norm_bch_septic_remainder_le` — order-7 BCH remainder
- `Basic.lean:7123` `norm_bch_sextic_remainder_le` — order-6 BCH remainder
