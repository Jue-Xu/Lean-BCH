# Lean-BCH Next Session — Discharge T2-F7e Parent Axiom

> **Detailed implementation plan**: see
> `claude/lean-bch-T2F7e-parent-discharge-implementation-plan.md` for the
> full extended hdecomp derivation (11 pieces), the 2 algebraic identities
> needed (deg-5 + deg-6 cancellations), and per-piece bound estimates
> produced in session 20.

## Session 20 progress (2026-05-09)

**Lipschitz infrastructure complete** (~2034 lines added in `BCH/Basic.lean`):
- `norm_bch_cubic_term_diff_le`: `‖C₃(z, y) − C₃(x, y)‖ ≤ M² · ‖z − x‖`
- `norm_bch_quintic_term_diff_le`: `‖C₅(z, y) − C₅(x, y)‖ ≤ M⁴ · ‖z − x‖`
  (built from 4 per-group bounds: group_1, group_4, group_6, group_24)
- `norm_bch_sextic_term_diff_le`: `‖C₆(z, y) − C₆(x, y)‖ ≤ M⁵ · ‖z − x‖`
  (built from 28 per-word bounds + 6 position helpers; needs heartbeat 16M
  for whnf processing of the 28-summand identity)

These bound the C-difference pieces of the extended hdecomp. With
`z = (a'+b)+W` (‖W‖=O(s²)): give O(s⁴), O(s⁶), O(s⁷) bounds respectively.

## Next-session work (Phase A + B)

**Phase A** (~200 lines, in main theorem body):
- Setup chain: `a' := (1/2)·a`, `s := ‖a‖+‖b‖`, `s₁ := ‖a'‖+‖b‖`,
  `z := bch(a', b)`, `s₂ := ‖z‖+‖a'‖`.
- Bounds: `s₁ ≤ s`, `s₂ ≤ (57/22)·s` (from cubic template).
- Inner septic: `R₁_sept := bch(a',b) − through_deg6(a', b)`, with
  `‖R₁_sept‖ ≤ K · s₁⁷ / (2 − exp s₁)` via `norm_bch_septic_remainder_le`.
- Outer septic: `R₂_sept := bch(z, a') − through_deg6(z, a')`, with
  `‖R₂_sept‖ ≤ K · s₂⁷ / (2 − exp s₂)` via `norm_bch_septic_remainder_le`.

**Phase B** (~150 lines, requires CAS support):
- Deg-5 cancellation algebraic identity:
  `½[C₄(a',b), a'] + (deg-5 of T₅) + (deg-5 of T₆) − correction(a, b) = 0`
- The "(deg-5 of T_k)" pieces are explicit polynomials in (a, b) that
  must be CAS-computed (e.g. via extending `discover_quintic_alt_form.py`
  to the deg-5 Taylor coefficient of `(C_k((a'+b)+W, a') − C_k(a'+b, a'))`).
- Once polynomial form known: prove via `match_scalars <;> ring`.

## Current state (after session 19, 2026-05-09)

- **0 sorries**, **2 scoped private axioms** (was 3 — one discharged):
  - `BCH.symmetric_bch_quintic_sub_poly_axiom` — parent T2-F7e (final
    target for this session).
  - `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` — Lean-Trotter axiom 3.
- All T2-F7e infrastructure is in place:
  - `BCH.norm_bch_septic_remainder_le` — order-7 BCH remainder
    `‖bch a b - (a+b) - ½[a,b] - C₃ - C₄ - C₅ - C₆‖ ≤ 1000010·s⁷/(2-exp(s))`
    fully proven (session 19 step 22).
  - `BCH.norm_bch_sextic_remainder_le` — order-6 BCH remainder
    `‖bch a b - (a+b) - ½[a,b] - C₃ - C₄ - C₅‖ ≤ 100000·s⁶/(2-exp(s))`
    fully proven (session 16).
  - `BCH.symmetric_bch_quintic_poly_alt_form` — alt-form decomposition
    proven (session 18).
  - `BCH.bch_sextic_term`, `BCH.norm_bch_sextic_term_le`,
    `BCH.bch_sextic_term_smul`, `BCH.septic_pure_identity` — degree-6
    machinery in place.
  - T2-F7g ⟺ parent axiom proven (bidirectional Lean equivalence).

## Goal

Discharge `BCH.symmetric_bch_quintic_sub_poly_axiom` in
`BCH/SymmetricQuintic.lean`. After this discharge, the only remaining
private axiom in Lean-BCH is the Suzuki-5 R₇ identification (axiom 3).

The axiom asserts, for `‖a‖ + ‖b‖ < 1/4`:
```
‖symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b
    − symmetric_bch_quintic_poly 𝕂 a b‖ ≤ 10⁹ · (‖a‖+‖b‖)⁷
```

Where `symmetric_bch_cubic 𝕂 a b = bch(bch(½a, b), ½a) - (a+b)` is the
3-factor symmetric BCH expansion remainder.

## Strategy

**Option B** (recommended, per CLAUDE.md): extend the cubic template
`norm_symmetric_bch_cubic_sub_poly_le` (`Basic.lean:5834`) by one degree.
The cubic template proves:
```
‖sym_bch_cubic - sym_E₃‖ ≤ 2·10⁷·s⁵
```
via inner/outer BCH expansions truncated at deg-3 plus the symmetric
quartic identity (palindromic deg-4 vanishing).

For the quintic version, we need:
```
‖sym_bch_cubic - sym_E₃ - sym_E₅‖ ≤ K · s⁷
```
where K is a constant (10⁹ is plenty of slack — 10⁵ should suffice).

### Recommended structure (estimated 1000-1500 lines)

1. **Inner BCH expansion to deg-6**: Define
   ```
   inner_R₇ := bch(½a, b) − (½a + b + ½[½a,b] + C₃(½a, b) + C₄(½a, b)
                              + C₅(½a, b) + C₆(½a, b))
   ```
   Bound: `‖inner_R₇‖ ≤ K_inner · s⁷` via `norm_bch_septic_remainder_le`
   applied with arguments scaled by ½. The `bch_*_term_smul` lemmas
   handle homogeneity.

2. **Outer BCH expansion to deg-6**: Similarly define `outer_R₇` for
   `bch(z + ε, ½a) − (deg-6 polynomial expansion)` where `ε` is the
   inner expansion residual. Use `norm_bch_septic_remainder_le`.

3. **Sextic identity** (the new algebraic component): An identity (analog
   of `symmetric_bch_quartic_identity` at `Basic.lean:5760`) showing that
   the deg-6 contribution to `sym_bch_cubic - sym_E₃ - sym_E₅` from the
   substituted polynomial expansion vanishes (palindromic vanishing of
   even degrees). **First attempt: `match_scalars <;> ring`** — same
   technique that worked for the alt-form discharge. If that fails,
   fall back to ×LCM scalar clearing + `noncomm_ring`.

4. **Extended hdecomp**: rewrite `sym_bch_cubic - sym_E₃ - sym_E₅` as a
   sum of ~7-9 pieces, each O(s⁷) using the sextic identity for the
   deg-6 cancellation and the inner/outer expansions for the residuals.

5. **Per-piece bounds**: each new term needs O(s⁷) constant. Constants
   are typically in 10² range; total absorbed by 10⁹.

### Alternative path (Option A, possibly easier given new infrastructure)

Apply `norm_bch_septic_remainder_le` directly to inner and outer BCH
expansions to get O(s⁷) bounds for inner_R₇ and outer_R₇. Then the
deg-1, deg-3, deg-5 contributions cancel against `sym_E₃ + sym_E₅` via
explicit polynomial identities (extending the cubic template), and the
deg-2, deg-4, deg-6 contributions vanish by palindromic symmetry.

The deg-6 vanishing identity is the new ingredient — analog of the
quartic identity at deg-4. Try `match_scalars <;> ring`.

### Key references in Lean-BCH

- **Cubic template**: `Basic.lean:5834` (`norm_symmetric_bch_cubic_sub_poly_le`).
- **Quartic identity**: `Basic.lean:5760` (`symmetric_bch_quartic_identity`).
  Pattern to extend at deg-6.
- **Septic remainder**: `Basic.lean:7161` (`norm_bch_septic_remainder_small_s_le`)
  + `Basic.lean:7188` (`norm_bch_septic_remainder_le`).
- **Sextic remainder**: `Basic.lean:6530` (`norm_bch_sextic_remainder_small_s_le`)
  + `Basic.lean:7106` (`norm_bch_sextic_remainder_le`).
- **Alt-form**: `SymmetricQuintic.lean` (`symmetric_bch_quintic_poly_alt_form`).
- **Sextic_term + septic_pure_identity**: `Basic.lean:1907` and `Basic.lean:3315`.
- **T2-F7g equivalence**: `Palindromic.lean`
  (`norm_polynomial_in_y_sub_add_sub_E3_sub_E5_via_parent` and
  `symmetric_bch_quintic_sub_poly_le_via_T2F7g`).

### Known landmines (from prior sessions)

- `linear_combination (norm := module)` is flaky for non-commutative
  ring + smul; prefer `match_scalars <;> ring` with simp lemmas to
  distribute smul, OR ×LCM scalar clearing + `noncomm_ring`.
- Long `noncomm_ring` proofs may exceed default heartbeats. Set
  `maxHeartbeats 8000000` (or higher) per identity. Verify with
  smallest-needed value at end.
- Identities in `(a, b)` ring with rational scalars: `match_scalars <;>
  ring` is the cleanest tactic (5-line proofs vs 50-200 lines via
  pattern enumeration).
- Set-bound vs let-bound mismatches: when `rw [pieceB_*_decomp]` unfolds
  let bindings, downstream `linarith` may fail because `set`-named
  hypotheses don't match. Add `simp only [hy_def, hz_def, ...]` to
  unfold set names in hypotheses before `linarith`. (See session 19
  step 22 in `Basic.lean:7898` for an example.)

### Testing strategy

After each major lemma, run `lake build BCH.SymmetricQuintic` to verify
incremental progress. The full build via `lake build` should complete
without errors or new warnings (modulo existing linter warnings).

After the parent axiom is replaced with a theorem, verify:
- `git status` should show only `BCH/SymmetricQuintic.lean`,
  `BCH/Basic.lean` (if helpers added), and `CLAUDE.md` modified.
- `grep -c "private axiom" BCH/*.lean` should give:
  - `BCH/SymmetricQuintic.lean: 0` (was 1)
  - `BCH/Suzuki5Quintic.lean: 1` (unchanged)
  - All others: 0
- `#print axioms BCH.symmetric_bch_quintic_sub_poly_axiom` should
  return only the standard Lean axioms (the axiom is no longer scoped).

## Downstream impact

Once the parent axiom is discharged:
- `BCH.norm_symmetric_bch_quintic_sub_poly_le` (B1.c bridge) — fully proven.
- `BCH.norm_strangBlock_log_sub_quintic_target_le` (B1.d per-block) — fully proven.
- Lean-Trotter's `bch_w4Deriv_quintic_level2` and `bch_w4Deriv_level3_tight`
  — depend only on standard Lean axioms (was: parent axiom).
- Lean-Trotter's transitive Lean-BCH-private axiom count: 2 → 1
  (only R₇ remains).

## Useful tactics for this session

- `match_scalars <;> ring` for polynomial identities.
- `noncomm_ring` for scalar-free ring identities.
- `linear_combination` for combining existing identities (with caveats).
- `convert` for handling minor structural differences modulo abel/ring.
- `nlinarith` for non-linear real arithmetic with explicit hints.
- `simp only [smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,
  ← mul_assoc]` to normalize smul algebraic expressions before
  `match_scalars`.

## Pointers

- Strategy details: `claude/lean-bch-B1c-session-prompt.md` (Tier 2 sub-tasks).
- Original T2-F7e plan: `claude/lean-bch-T2F7e-session-prompt.md` (now mostly
  obsolete — Phase A complete).
- Cubic template study: read `Basic.lean:5834` for the existing pattern.
- Git log: session-by-session implementation history.
