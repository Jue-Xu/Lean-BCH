# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status (session 17, 2026-05-07)

Branch: `trotter-5factor-palindromic`. Repository is **0 sorries**.

**Axiom count: 3 scoped `private axiom`s + Lean's 3 standard.**
- `BCH.symmetric_bch_quintic_sub_poly_axiom` — B1.c Tier-2 PARENT, in
  `SymmetricQuintic.lean`. Will be discharged via T2-D + T2-E using the alt-form
  axiom + sextic identity.
- `BCH.symmetric_bch_quintic_poly_alt_form_axiom` — Tier-2 stepping stone (NEW
  session 17), CAS-derived pure polynomial identity (T2-A + T2-B). Provable as a
  `noncomm_ring` identity but requires comprehensive scalar enumeration (~150-200
  lines).
- `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` — axiom 3 (septic at Suzuki p)
  in `Suzuki5Quintic.lean`.

**Session 17 progress (Tier-2 decomposition + initial attack)**:
- T2-A done: CAS pipeline `Lean-Trotter/scripts/discover_quintic_alt_form.py`
  discovers and prints the explicit decomposition. Verified residual = 0.
- T2-B done: alt-form lemma added (as scoped axiom for now); 25-term correction
  polynomial defined as `BCH.symmetric_bch_quintic_correction_poly`.
- T2-C/D/E pending: sextic identity, extended hdecomp, per-term bounds.

**Session 16 discharge of `norm_bch_sextic_remainder_small_s_le`** (Tier-1 small-s,
~580 lines): mirrors quintic proof's H1 + quartic_identity pattern. Bounds 4 sub-pieces
(S₁ ≤ 20·s⁶, S₂ ≤ 17·s⁶, S₃ ≤ 8·s⁶, S₄ ≤ 7·s⁶) via `pieceB_sextic_decomp` + helpers.
Combined with pieceA ≤ 2·s⁶/(2-exp(s)) gives 100·s⁶/(2-exp(s)).

**Key theorems** (Lean-Trotter interface):
- Axiom 1 (P1, `bch_w4Deriv_quintic_level2`): **discharged session 12** via
  `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` + bridge corollary.
- Axiom 2 (P2, `bch_w4Deriv_level3_tight`): **discharged session 8** via
  `BCH.suzuki5_log_product_quintic_tight_at_suzukiP`.
- Axiom 3 (`bch_uniform_integrated`): currently scoped axiom (session 14 added).

**Public theorems added session 16**:
- `BCH.norm_bch_sextic_remainder_le` (Tier-1 of B1.c discharge): public order-6 BCH
  remainder bound `‖LHS_sextic‖ ≤ 100000·s⁶/(2-exp(s))`. Uses
  `norm_bch_sextic_remainder_large_s_le` (proved) for s ≥ 1/10 and the small-s axiom
  for s < 1/10.

## Goal

Formalize BCH and its truncated bounds in a complete normed algebra, with
applications to product formula error analysis (Trotter, Strang, Suzuki).

## Constraints

- **Lean:** 4.29.0-rc8 (via `lean-toolchain`)
- **Mathlib:** pinned in `lake-manifest.json`
- **Typeclass setup:** `[NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]`
- `include 𝕂 in` needed before theorems where `𝕂` appears in proofs but not the type.

## File Structure

```
BCH/
├── LogSeries.lean         ← log(1+x) series, summability, exp∘log = id
├── Basic.lean             ← exp/log bounds, BCH def, H1/H2, quintic+sextic remainder,
│                            Tier-1 of B1.c (norm_bch_sextic_remainder_le)
├── SymmetricQuintic.lean  ← τ⁵ coefficient: 30-term polynomial, c⁵ homogeneity,
│                            B1.c quintic Taylor bridge (Tier-2 axiom)
├── Palindromic.lean       ← Suzuki-5 palindromic product, M1–M4b, M6 Trotter h4,
│                            B1.d per-block wrapper, B2.2.a-e, B2.5 T₂ bound
├── ChildsBasis.lean       ← 8 Childs 4-fold commutators + bchFourFoldSum
│                            + BCHPrefactors struct
└── Suzuki5Quintic.lean    ← βᵢ(p) polynomials, R₅ Childs def, headline τ⁵ theorem,
                             tight bridge at Suzuki p, septic axiom 3
```

Import chain: `Basic → SymmetricQuintic → Palindromic → ChildsBasis → Suzuki5Quintic`.

## Key Techniques

### Non-commutative scalar issue
`(2:𝕂)⁻¹ • x` (scalar smul) doesn't interact with `noncomm_ring` or `abel`.
**Solution:** Multiply both sides by `(2:𝕂)`, clear via `smul_smul` +
`inv_mul_cancel₀` + `one_smul`, then use `noncomm_ring` on the scalar-free
identity. Pattern: `apply hinj_N; simp only [smul_zero]; ...; noncomm_ring`.

### `dsimp only` BEFORE scalar clearing
Unfolds let-bindings transparently so `noncomm_ring` sees daggered (have-bound)
variables as proper atoms. Without it, the proof fails. Used in
`I1_residual_decomp_eq`, `sextic_pure_identity`, and similar.

### Algebraic identity templates (`quartic_identity` pattern)
Identities like `½W + ⅓z³ - C₃ = (deg-4+ residual)` proved via:
1. Sub-identity `hpure` (pure a, b) by ×LCM scalar clearing + `noncomm_ring`.
2. Full identity by ×LCM + `simp only [smul_smul, ...]` + `noncomm_ring`.

### Critical lesson: post-substitution decomposition
Pure {a, b, ea, eb} ring identities for the **deg-5** cancellation in
`bch_quintic_term` do NOT exist (verified by CAS — bbbba/bbbbA coupling).
The decomposition works only on SUBSTITUTED polynomials in {a, b}.
`sextic_pure_identity` exploits this.

### Tactics for non-comm + smul
- `linear_combination (norm := module)` works for `pieceB_sextic_decomp` (with
  let-bindings) but is unreliable in general; the underlying `module` calls
  `ring` which fails on non-comm products. **Workaround**: use scalar clearing
  + `noncomm_ring`, or `convert` + `abel` for term reordering.
- `noncomm_ring` doesn't handle `smul`; combine with `simp [smul_sub, smul_add,
  smul_mul_assoc, mul_smul_comm]` to distribute first.

### `convert` pattern for QPI/SPI applications
`convert quintic_pure_identity 𝕂 a b using 2 <;> simp [hz_def] <;> ring` —
matches a goal that differs from QPI by simple substitution + scalar reduction.
Used in the quintic proof's `hQPI` (line ~3258).

### Splitting monolithic noncomm_ring proofs
A 128-monomial `noncomm_ring` may time out at 1.6M heartbeats. Splitting into
two 64-monomial half-identities makes it tractable. Used for
`comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis` (B2.2.e).

### Per-term `private lemma`s for polynomial bookkeeping
For deeply nested polynomial expressions (P1 discharge, ~1100 lines), splitting
into per-term private lemmas avoids kernel whnf blowup. Final combination via
`le_trans` (not `linarith`) sidesteps def-unfolding arithmetic.

## Tier-1 of B1.c: `norm_bch_sextic_remainder_le`

Status: public theorem in place using `norm_bch_sextic_remainder_small_s_le` axiom.

### Proven (sessions 13-15, in `Basic.lean`)

- `bch_quintic_term`, `real_exp_sixth_order_le_sextic`,
  `norm_logOnePlus_sub_sub_sub_sub_sub_le` (order-6 log/exp tail bounds).
- `sextic_pure_identity`: deg-5 cancellation `½W5 + ⅓y3_5 - ¼y4_5 + ⅕z⁵ - C₅ = 0`
  on substituted polynomials in {a, b}. ×720 + `noncomm_ring`,
  `maxHeartbeats 4000000000`.
- `pieceB_sextic_decomp`: central decomposition pieceB'' = S₁+S₂-S₃+S₄ via
  `linear_combination (norm := module) hQPI + hSPI`.
- `I1_residual_decomp_eq` + `R_eq_neg_deg5_residual` (algebraic identities).
- Per-term norm bounds:
  - `norm_I1_residual_RHS_le` (≤ 20·s⁶ for S₁)
  - `norm_I2_residual_inner_le` (≤ 50·s⁶, ÷3 for S₂ → ≤17·s⁶)
  - `norm_y4_sub_z4_sub_y4_5_le` (≤ 31·s⁶, ÷4 for S₃ → ≤8·s⁶)
  - `norm_pow5_sub_zpow5_le` (≤ 31·s⁶, ÷5 for S₄ → ≤7·s⁶)
- Component bounds: `norm_R_residual_sum_le`, `norm_T22_sub_P2_etc_le`,
  `norm_P_sub_T2_sub_T3_le`, `norm_PzP_sub_T2zT2_le`, `norm_P2_sub_T22_le`.
- `norm_bch_sextic_remainder_large_s_le` (s ≥ 1/10 case, fully proved).

### Remaining (Task #17b: discharge `norm_bch_sextic_remainder_small_s_le`)

~250-300 lines. Must combine pieceA bound (via
`norm_logOnePlus_sub_sub_sub_sub_sub_le`) with pieceB'' = 4 sub-pieces
(via `pieceB_sextic_decomp`).

**Key Lean-tactic challenges**:
- T₃_QPI (= ⅙a³+⅙b³+½ab²+½a²b) and T₃_SPI (= ⅙a³+½a²b+½ab²+⅙b³) are
  equal as values but differ syntactically; QPI uses the former, SPI the
  latter. `pieceB_sextic_decomp` separates them via separate let-bindings.
- The S₁ bound requires the H1 + quartic_identity + I1_residual_decomp_eq
  chain; mirror the quintic proof's `hH1` + `hI₁_quartic` pattern (lines
  3208 and 3239 of `Basic.lean`).
- Avoid `linear_combination (norm := module)` for the per-piece equalities
  (it's flaky for non-comm + smul); use `convert` + `abel` for reordering,
  or scalar clearing + `noncomm_ring`.

See `claude/sextic_remainder_strategy.md` for the full proof plan and
per-piece bounds.

## Tier-2 of B1.c: `symmetric_bch_quintic_sub_poly_axiom`

Asserts for `‖a‖+‖b‖ < 1/4`:
```
‖symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b
    − symmetric_bch_quintic_poly 𝕂 a b‖ ≤ 10⁹ · (‖a‖+‖b‖)⁷
```

Public theorems depending on this axiom:
- `BCH.norm_symmetric_bch_quintic_sub_poly_le` (B1.c bridge).
- `BCH.norm_strangBlock_log_sub_quintic_target_le` (B1.d per-block wrapper).

CAS at `Lean-Trotter/scripts/verify_strangblock_degree7.py` confirms degrees
2, 4, 6 vanish identically (palindromic symmetry); degree-7 residual has
126 non-zero `{a,b}`-words.

**Discharge plan** (~1 week of dedicated Lean work):

Extends the cubic template `norm_symmetric_bch_cubic_sub_poly_le` (line
~5834 of `Basic.lean`, ~800 lines) by one degree higher. The cubic template's
6-term decomposition becomes 8-10 terms, with each new term capturing a
degree-5 correction:

1. **R₁_sextic, R₂_sextic** — replace `norm_bch_quintic_remainder_le` with
   the just-discharged `norm_bch_sextic_remainder_le` (Task #17b done).
   Each gives O(s⁶) instead of O(s⁵), so R₁_sextic = R₁_quintic - C₅(a',b)
   with ‖R₁_sextic‖ ≤ 100000·s₁⁶/(2-exp(s₁)).
2. **Extract C₅(a',b), C₅(z,a')** — explicit degree-5 contributions from
   inner/outer BCH expansions.
3. **Identify the degree-5 part of each existing term** via CAS (run
   `Lean-Trotter/scripts/compute_bch_prefactors.py` extended to degree 7).
   The sum of these degree-5 parts must equal `symmetric_bch_quintic_poly`
   (verified by CAS structurally).
4. **Bound each term's residual** (term minus its degree-5 part) by O(s⁷).

The CAS pipeline is the hardest bottleneck — it discovers the algebraic
decomposition mechanically. Without it, the per-term degree-5 identification
is intractable by hand.

**Estimated proof size**: ~1000-1200 lines (extending the existing 800-line
cubic template). Use `set_option maxHeartbeats 4000000000`.

**Recommendation for next session**:
- Run `compute_bch_prefactors.py` extended to degree 7; extract the 8-10
  term decomposition.
- Mirror the cubic template's structure (lines 5834-6614 of `Basic.lean`),
  replacing `norm_bch_quintic_remainder_le` calls with `norm_bch_sextic_remainder_le`.
- Per-term bounds: each new degree-5 cancellation term needs explicit O(s⁷)
  bound (similar to the cubic template's 5×10⁶ + 5000 + ... constant chain).

## Lean-Trotter interface (axioms 1–3)

`Lean-Trotter/LieTrotter/Suzuki4ViaBCH.lean` has three BCH-interface axioms:

1. `bch_w4Deriv_quintic_level2` — unit-coefficient pointwise τ⁵ bound.
   **Discharged session 12** via `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le`.
2. `bch_w4Deriv_level3_tight` — tight γᵢ at Suzuki p.
   **Discharged session 8** via `BCH.suzuki5_log_product_quintic_tight_at_suzukiP`.
3. `bch_uniform_integrated` — order-7 + R₇ + FTC-2 integrated bound.
   Currently `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` (Lean-BCH side).

**Key public theorems on this branch** (depend only on Lean's 3 standard +
B1.c Tier-2 axiom):
- `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` (P1 headline).
- `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` (P1 bridge corollary).
- `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` (P2 bridge).
- `BCH.norm_bch_sextic_remainder_le` (Tier-1 of B1.c, NEW session 16; depends
  also on small-s sextic axiom).

## Earlier core results

- **H1** (`norm_bch_sub_add_sub_bracket_le`): commutator extraction
  `bch(a,b) − (a+b) − [a,b]/2 = O(s³)`.
- **H2** (`norm_symmetric_bch_sub_add_le`): symmetric BCH cancellation
  `bch(bch(a/2,b),a/2) − (a+b) = O(s³)`.
- **Quintic BCH** (`norm_bch_quintic_remainder_le`): order-5 bound
  `‖bch − (a+b) − ½[a,b] − C₃ − C₄‖ ≤ 3000·s⁵/(2-exp(s))` (~750 lines,
  template for the sextic version).
- **Symmetric cubic** (`norm_symmetric_bch_cubic_sub_smul_le`): order-3 bound
  `‖bch(bch(ca/2,cb),ca/2) − c(a+b) − c³E_3‖ ≤ 2·10⁷·|c|³·s⁵`.
- **M6 Trotter h4** (`norm_s4Func_sub_exp_le_of_IsSuzukiCubic`): Suzuki S₄
  4th-order error bound.
- **M4b RHS quintic** (`suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`).

## Pointers

- `claude/sextic_remainder_strategy.md` — Tier-1 small-s discharge plan.
- `claude/lean-bch-B1c-session-prompt.md` — Tier-1/Tier-2 overview.
- `claude/lean-bch-B2-session-prompt.md` — B2 (5-factor BCH composition).
- `claude/lean-bch-B2.5-session-prompt.md` — B2.5 (T₂ bound).
- Git log preserves session-by-session implementation history.
