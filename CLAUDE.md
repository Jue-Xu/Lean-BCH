# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status (session 20, 2026-05-09)

Branch: `main`. Repository is **0 sorries**.

**Session 20 steps 2-6** (~870 lines in `Basic.lean`): Lipschitz bounds for
`bch_cubic_term` and `bch_quintic_term` in their first argument. These are
key infrastructure for the parent T2-F7e discharge — they provide the
O(s⁴)/O(s⁶) bounds on `‖C_k(z, y) − C_k(x, y)‖` when `‖z − x‖ = O(s²)`,
needed for the "obviously O(s⁷)" piece group of the extended hdecomp.

- `BCH.norm_bch_cubic_term_diff_le`: `‖C₃(z, y) − C₃(x, y)‖ ≤
  M² · ‖z − x‖` (M = ‖z‖+‖x‖+‖y‖). 12-summand telescoping + 11-step
  triangle. ~150 lines.
- `BCH.norm_bch_quintic_group_1_diff_le` (4 words, 10 summands, 117 lines).
- `BCH.norm_bch_quintic_group_4_diff_le` (10 words, 25 summands, 188 lines;
  uses new shared `norm_5prod_le` helper).
- `BCH.norm_bch_quintic_group_6_diff_le` (14 words, 35 summands, 270 lines;
  heartbeat 1.6M for the noncomm_ring telescope identity).
- `BCH.norm_bch_quintic_group_24_diff_le` (2 words, 5 summands, 60 lines).
- `BCH.norm_bch_quintic_term_diff_le` (combines all 4 groups via
  algebraic identity + triangle, ~80 lines): `‖C₅(z, y) − C₅(x, y)‖ ≤
  M⁴ · ‖z − x‖`. With z = (a'+b)+W (‖W‖ = O(s²)): gives O(s⁶) bound,
  the deg-6+ residual estimate needed in the extended hdecomp.

**Session 20 step 7-8** (~1150 lines): `bch_sextic_term` Lipschitz bound
complete. 28 per-word lemmas (`bch_sextic_word01_diff_le` through
`bch_sextic_word28_diff_le`) + 6 position helpers (`norm_6prod_pos1_le`
through `norm_6prod_pos6_le`) + combined `norm_bch_sextic_term_diff_le`:
  `‖C₆(z, y) − C₆(x, y)‖ ≤ M⁵ · ‖z − x‖`
with K = 492/1440 = 41/120. Heartbeat 16M for whnf processing of the
28-summand `hsplit` identity.

**Lipschitz infrastructure complete**: `norm_bch_cubic_term_diff_le`,
`norm_bch_quintic_term_diff_le`, `norm_bch_sextic_term_diff_le` — all
O(M^(k-1) · ‖z−x‖) bounds. With z=(a'+b)+W (‖W‖=O(s²)): give O(s⁴),
O(s⁶), O(s⁷) bounds respectively on the C-difference pieces of the
extended hdecomp.

**Next session priority**: Phase A of the discharge — inner+outer septic
remainders (`bch(½a, b) − through_deg6` and `bch(z, ½a) − through_deg6`)
with norm bounds via `norm_bch_septic_remainder_le`, plus the s₂ ≤ K·s
bound (extracted from cubic template). Estimated ~200 lines. After
Phase A, Phase B (deg-5 cancellation algebraic identity) follows.

**Session 20 step 1**: Detailed analysis of T2-F7e parent discharge (extending
the cubic template from `Basic.lean:8601`). Produced
`claude/lean-bch-T2F7e-parent-discharge-implementation-plan.md` with:
- Complete derivation of the **extended hdecomp** (11 pieces) for
  `sym_bch_cubic - sym_E₃ - sym_E₅`.
- Concrete formulation of the 2 algebraic identities needed:
  - **Deg-5 cancellation**: `½[C₄(a',b),a'] + (deg-5 of T₅,T₆) − correction = 0`
  - **Deg-6 cancellation** (palindromic): `½[C₅(a',b),a'] + C₆(a',b)
    + C₆(a'+b,a') + (deg-6 of T₅,T₆,C₅-diff) = 0`
- Per-piece norm-bound estimates (all within 10⁵ × s⁷ budget; well under
  the 10⁹ axiom constant).
- Recommended 6-session breakdown (~1000–1500 lines total, mirrors
  the cubic template's 700-line structure but at one degree higher).

The discharge requires CAS support to compute the explicit deg-7+
residual polynomials in (a, b) for the algebraic identities; a future
session will set up this CAS pipeline (similar to the existing
`Lean-Trotter/scripts/discover_quintic_alt_form.py`).

**Session 19 final**: T2-F7e Phase A complete. The septic remainder small-s
axiom is fully discharged (~700 lines added in `Basic.lean`), reducing the
total axiom count from 3 to **2 scoped `private axiom`s**.

**Session 19 progress**: Phase A.1 (S₃' bound) + Phase A.2 (I1/I2 algebraic
identities) + Phase A.4 (I2 wrapper input helpers complete) + Phase A.5
(septic small-s discharge).

- Step 8: `y4_sub_z4_sub_y4_5_sub_y4_6_decomp` (16-term identity) +
  `norm_y4_sub_z4_sub_y4_5_sub_y4_6_le` (≤ 85·s⁷). The S₃' piece bound for
  `pieceB_septic_decomp`. Uses compound `(y²-z²)·P²` and `z·(P²-T₂²)·z`
  forms (via existing `norm_pow2_sub_zpow2_le` and `norm_P2_sub_T22_le`).
- Step 9: Level-7 exp tail lemmas — `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le`
  (noncomm) + `real_exp_seventh_order_le_septic` (real, ≤ s⁷ for s < 3/4).
  Foundation for the H_a → I_a refinement.
- Step 10: `I1_septic_residual_decomp_eq` (12-term identity, extends
  `I1_residual_decomp_eq` by subtracting `corr₁_6 = ½·W6`). Pairs the 7
  monomial parts of `½·W6` with the deg-6 leading parts of the existing
  RHS (H₁ → I_a, G₁·b → H₁·b, etc.). Proof: `match_scalars <;> ring`.
- Step 11: `I2_septic_residual_decomp_eq` (pure ring identity in
  {z, P, T₂, T₃, T₄}, extends `I2_residual_decomp_eq` by subtracting `y3_6`).
  Proof: `noncomm_ring`.
- Step 12: `norm_I1_septic_residual_RHS_le` (≤ (7 + (C₁+C₂+C₃)/2)·s⁷,
  parameterized over 3 "tricky" bounds) + `norm_I2_septic_residual_RHS_le`
  (≤ (3·K_PmT4 + 2·K_P2 + K_PzP + K_P3)·s⁷, parameterized over 4 inputs).
  Both wrappers combine precomputed bounds via triangle inequality.
- Step 13: `norm_P3_sub_T23_le` (≤ 15·s⁷ via telescope). Concrete K_P3 = 15.
- Step 14: `norm_P_sub_T2_sub_T3_sub_T4_le` (≤ 6·s⁵ via 7-term decomposition
  G₁+G₂+a·F₂+F₁·b+E₁·E₂+½·E₁·b²+½·a²·E₂). Concrete K_PmT4 = 6 input for I2.
  Algebraic identity proved via `linear_combination` from
  `R_eq_neg_deg5_residual` (avoiding the failing standalone match_scalars
  attempt: scalar mismatch in canonical form).
- Step 15: `norm_PzP_sub_T2zT2_etc_le` (≤ 13·s⁷ via 6-term decomposition
  using P=T₂+T₃+(P-T₂-T₃)). Concrete K_PzP = 13 input for I2.
- Step 16: `R_plus_T5_eq_neg_deg6_residual` — algebraic identity
  `T₃ - E₁ - E₂ - Q + T₄ + T₅ = -(H₁+H₂+a·G₂+G₁·b+E₁·E₂+½·F₁·b²+½·a²·F₂)`.
  Each RHS piece is deg-6+ in s. The deg-5 cancellation `R₅ = -T₅` exposed
  algebraically. Foundation for the future combined tricky bound.
  Proof: `linear_combination` from `R_eq_neg_deg5_residual` with
  `match_scalars + ring` for scalar normalization (12⁻¹ vs 2⁻¹·6⁻¹).
- Step 17: `norm_R_plus_T5_residual_sum_le` (≤ 6·s⁶ via 7 component bounds).
  Analog of `norm_R_residual_sum_le` at one degree higher. All inputs
  uniformly at deg-6 (no small-s constraint needed).
- Step 18: `norm_combined_tricky_le` (≤ 28·s⁷ for s ≤ 1/10). The
  combined bound for `(z·R+R·z) + T22 + T_extra`. Algebraic identity
  reduces to `z·(R+T₅) + (R+T₅)·z - P²_deg≥7`, where P²_deg≥7 is the
  10-term decomposition `T₃T₄ + T₄T₃ + T₂·D₅ + D₅·T₂ + T₄² + T₃·D₅ + D₅·T₃ + T₄·D₅ + D₅·T₄ + D₅²`
  using D₅ = P-T₂-T₃-T₄ (≤ 6·s⁵). Maxheartbeats 4M for nlinarith.
- Step 19: I1 wrapper redesign — `norm_I1_septic_residual_RHS_le` now
  takes a single combined parameter `‖z·R+R·z+T22+T_extra‖ ≤ C·s⁷`
  instead of 3 (which were unsatisfiable as constants). Result bound:
  (7 + C/2)·s⁷. With C=28 from step 18: I1 RHS ≤ 21·s⁷.
  Proof uses `abel` re-association + `← smul_add` factoring.
- Step 20: `norm_T4_le` and `norm_T5_le` standalone helpers.
  - `norm_T4_le`: `‖T₄(a,b)‖ ≤ s⁴` (sum of |coefs| = 16/24 = 2/3).
  - `norm_T5_le`: `‖T₅(a,b)‖ ≤ s⁵` (sum of |coefs| = 32/120 = 4/15).
  Factor out the inline T₄/T₅ bound calculations needed for the future
  small-s septic assembly, saving ~120 lines. Note: T₂ and T₃ helpers
  cannot be standalone with `α ≤ s, β ≤ s` since their |coef| sums are
  `> 1`; they remain inline in the assembly using `s = α + β`.
- Step 21: `real_exp_sub_one_pow7_le_small`. Helper bounding
  `(Real.exp s - 1)^7 ≤ 2·s^7` for `s ≤ 1/10`. Analog of inline `hexp6`
  in the sextic discharge. Saves ~10 lines in the future pieceA bound.

**I2 wrapper inputs all in place:** K_PmT4=6, K_P2=15, K_PzP=13, K_P3=15.
Total septic I2 RHS bound: (3·6 + 2·15 + 13 + 15)·s⁷ = 76·s⁷ for s ≤ 1/10.

**I1 wrapper now satisfiable:** With C = 28 from `norm_combined_tricky_le`,
I1 RHS ≤ 21·s⁷.

**`pieceB_septic_decomp` piece bounds (used in step 22 discharge):**
- S₁' (I₁) ≤ 21·s⁷ (via I1 wrapper + combined tricky C=28: (7 + C/2)·s⁷)
- S₂' (I₂ inner) ≤ 76·s⁷; after ⅓ scaling ≤ 26·s⁷
- S₃' (y⁴ inner) ≤ 85·s⁷; after ¼ scaling ≤ 22·s⁷
- S₄' (y⁵ inner) ≤ 51·s⁷; after ⅕ scaling ≤ 11·s⁷
- S₅ (y⁶ inner) ≤ 63·s⁷; after ⅙ scaling ≤ 11·s⁷
- **Total pieceB''' ≤ 91·s⁷**; with pieceA ≤ 2·s⁷/(2-exp(s)),
  combined gives ≤ 93·s⁷/(2-exp(s)) ≤ 1000·s⁷/(2-exp(s)).

- **Step 22 (session 19): `norm_bch_septic_remainder_small_s_le`** — fully
  discharged (~700 lines, mirrors the session-16 sextic discharge structure).
  `set_option maxHeartbeats 32000000`. Key tactic insight: pieceB_septic_decomp
  unfolds let-bindings on rewrite, so hS_i_le hypotheses must be unfolded to
  match (`simp only [hy_def, hz_def, hT₂_def, ...] at hS1_le ... hS5_le`
  before triangle inequality). hS2_inner_eq's y3_6 ordering re-aligned to
  match pieceB's (T₂zT₃ + T₂T₃z + T₃zT₂ + T₃T₂z), proved via `noncomm_ring`.

**Axiom count: 2 scoped `private axiom`s + Lean's 3 standard** (was 3 before
session 19 step 22).
- `BCH.symmetric_bch_quintic_sub_poly_axiom` — B1.c Tier-2 PARENT, in
  `SymmetricQuintic.lean`. Discharge requires T2-F7e (cubic template
  extension to deg-5 cancellation), ~1000 lines remaining.
- `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` — axiom 3 (septic at Suzuki p)
  in `Suzuki5Quintic.lean`.

(`BCH.norm_bch_septic_remainder_small_s_axiom` was discharged in step 22
and is now the public theorem `norm_bch_septic_remainder_small_s_le`.)

**Session 18 highlights (`match_scalars <;> ring` methodology)**:
A simple 3-line tactic sequence replaces 150+ line scalar pattern enumerations:
```
unfold <all definitions>
simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
  smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
match_scalars <;> ring
```

Refactored proofs (all in `BCH/Basic.lean`):
- `symmetric_bch_quintic_poly_alt_form` (NEW; T2-B alt-form): 5 lines.
- `symmetric_bch_cubic_poly_alt_form`: 28 → 5 lines.
- `symmetric_bch_quartic_identity`: 56 → 5 lines.
- `quintic_pure_identity`: 50 → 4 lines.
- `sextic_pure_identity`: 80 lines (with maxHeartbeats 4 BILLION!) → ~20 lines
  (with explicit let-binding unfolds via `show <name> = <expansion> from rfl`).

Foundation work for T2-F7e:
- `bch_sextic_term` defined (NEW): 28-term explicit polynomial in {a,b}, LCM
  1440, numerators in {±1, ±4, ±6, ±24}. With c⁶ homogeneity and norm bound
  `‖Z₆(a,b)‖ ≤ s⁶`. Used as the deg-6 leading term in the sextic identity
  for the parent discharge.

This methodology generalizes to ANY pure polynomial identity in (a, b) with
rational scalar coefficients in 𝕂. Use this template first for new identities.

**Session 17–18 final state (16 working lemmas + alt-form theorem)**:
- T2-A done: CAS pipeline `Lean-Trotter/scripts/discover_quintic_alt_form.py`.
- T2-B done (session 18, FULLY PROVED — no longer axiom):
  `symmetric_bch_quintic_poly_alt_form` via `match_scalars <;> ring`.
- T2-F1 through T2-F6 done: full framework from `‖P-1‖` bounds through
  the bridge `bch∘bch = logOnePlus(P-1)` to combined framework bound.
- T2-F7-aux, T2-F7-prelim, T2-F7-prelim2, T2-F7g-coarse done: progressively
  tighter bounds (O(s²) → O(s⁵)).
- T2-F7g-tight, T2-F-equiv done: T2-F7g ⟺ parent axiom (Lean-proved both
  directions modulo small tail term).
- T2-G done: `‖correction polynomial‖ ≤ s⁵`.
- **T2-F7e is the SOLE remaining math piece**: identify deg-5 of polynomial_in_y
  as sym_E₅ algebraically. Combined with T2-F-equiv, this immediately
  discharges the parent Tier-2 axiom.

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

### `match_scalars <;> ring` for poly identities in 𝕂-modules (NEW session 18)
For polynomial identities (over `NormedAlgebra 𝕂 𝔸`) with rational scalar
coefficients in 𝕂, the cleanest proof is:
```lean
unfold <all definitions>
simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
  smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
match_scalars <;> ring
```

Why each part:
- `smul_*` lemmas distribute scalar multiplication through algebraic ops.
- `mul_smul_comm`, `smul_mul_assoc` pull smul out of products.
- `mul_*` and `*_mul` distribute multiplication.
- `← mul_assoc` left-associates products (so `match_scalars` sees `a*b*c`
  consistently as `(a*b)*c`, otherwise it produces non-trivial scalar goals).
- `match_scalars` splits the equation into one scalar identity per monomial.
- `ring` (commutative 𝕂-arithmetic) closes each scalar goal.

For identities with `let` bindings (e.g., `let z := a + b in ...`), unfold the
let bindings explicitly first via `simp only [show <name> = <expansion> from rfl]`,
since `match_scalars` doesn't auto-unfold them.

Refactored: cubic alt-form, quartic identity, quintic_pure_identity,
sextic_pure_identity (sessions 18). Original proofs used ×LCM + comprehensive
pattern enumeration (50-200 lines each); new proofs are 4-20 lines.

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

### Decomposition into sub-tasks T2-A through T2-G

**Session 17–18 progress** (13+ commits, 16 working lemmas):
- ✅ T2-A: CAS `Lean-Trotter/scripts/discover_quintic_alt_form.py` discovers
  the explicit alt-form decomposition (residual = 0). Outputs the combined
  correction polynomial (25 terms, denom 11520).
- ✅ T2-B (session 18): `BCH.symmetric_bch_quintic_poly_alt_form` is now a
  fully proved theorem (3-line proof via `match_scalars <;> ring` after
  unfolding + smul distribution). The 25-term `correction_poly` is defined
  in `SymmetricQuintic.lean`.
- ✅ T2-F7e infrastructure step 1 (session 18): `BCH.bch_sextic_term` defined
  + `bch_sextic_term_smul` (homogeneity) + `norm_bch_sextic_term_le`
  (`‖Z₆(a,b)‖ ≤ s⁶`). 28-term explicit polynomial in {a,b}, LCM 1440,
  numerators in {±1, ±4, ±6, ±24}. Used as the deg-6 leading term in the
  sextic identity for the parent discharge.
- ✅ T2-F7e infrastructure step 2 (session 18): `BCH.septic_pure_identity`
  — the deg-6 cancellation algebraic identity (analog of `sextic_pure_identity`
  at one higher degree). Asserts:
  `½·W6 + ⅓·y3_6 - ¼·y4_6 + ⅕·y5_6 - ⅙·z⁶ - bch_sextic_term = 0`
  where W6, y3_6, y4_6, y5_6 capture deg-6 contributions from y, y², y³, y⁴, y⁵.
  Pure {a, b} polynomial identity, proved via `match_scalars <;> ring`
  (only 16M heartbeats, vs 4 BILLION for the original sextic_pure_identity).
- ✅ T2-F7e infrastructure step 3 (session 18):
  `BCH.norm_bch_septic_remainder_large_s_le` — the easy half of the order-7
  BCH remainder bound, for s ≥ 1/10. Proved via triangle inequality from
  `norm_bch_sextic_remainder_le` + `norm_bch_sextic_term_le`. Bound:
  `‖LHS_septic‖ ≤ 1000010·s⁷/(2-exp(s))`.
- ✅ T2-F7e infrastructure step 4 (session 18):
  `BCH.norm_bch_septic_remainder_le` — public theorem combining the
  large-s case (proved) with a small-s axiom
  (`norm_bch_septic_remainder_small_s_axiom`). The small-s axiom is a
  stepping stone (analog of the discharged session-16 sextic small-s
  axiom; can be discharged similarly using septic_pure_identity).
- ✅ T2-F7e infrastructure step 5 (session 18, pow6 helper):
  `BCH.pow6_sub_zpow6_telescope` (6-fold non-commutative telescoping)
  + `BCH.norm_pow6_sub_zpow6_le` (`‖y⁶ - z⁶‖ ≤ 63·s⁷` for `‖y‖ ≤ 2s,
  ‖z‖ ≤ s, ‖P‖ ≤ s²`). Building block analog of `pow5_sub_zpow5_telescope`
  + `norm_pow5_sub_zpow5_le` for the future `norm_bch_septic_remainder_small_s_le`
  (S₅ piece bound: `⅙·63·s⁷ ≈ 10.5·s⁷`).
- ✅ T2-F7e infrastructure step 6 (session 18, pow4 + y5 helpers):
  `BCH.norm_pow4_sub_zpow4_le` (`‖y⁴ - z⁴‖ ≤ 15·s⁵`),
  `BCH.y5_sub_z5_sub_y5_6_decomp` (algebraic identity, 9 deg-7+ terms),
  `BCH.norm_y5_sub_z5_sub_y5_6_le` (`‖y⁵ - z⁵ - y5_6‖ ≤ 51·s⁷`).
  Analog of `norm_y4_sub_z4_sub_y4_5_le` at one degree higher; needed for
  the S₄' piece of `pieceB_septic_decomp`.
- ✅ T2-F7e infrastructure step 7 (session 18, **pieceB_septic_decomp**):
  `BCH.pieceB_septic_decomp` — the CENTRAL algebraic decomposition for
  the septic small-s case. Analog of `pieceB_sextic_decomp` at one degree
  higher. States:
  ```
  pieceB''' = (I₁ - corr₁ - corr₁_5 - corr₁_6) +
              (I₂ - corr₂ - corr₂_5 - corr₂_6) -
              ¼(y⁴-z⁴-y4_5-y4_6) + ⅕(y⁵-z⁵-y5_6) - ⅙(y⁶-z⁶)
  ```
  Where corr₁_6 = ½·W6, corr₂_6 = ⅓·y3_6, y4_6/y5_6/y3_6 are the explicit
  deg-6 contributions to y⁴/y⁵/y³.
  **Proof: 5 lines** — `linear_combination (norm := module) hQPI + hSPI + hSeptic`.
  Each piece on the RHS has deg-7+ structure.

  This is the foundation for the future small-s septic discharge.
  Remaining pieces: norm bounds for S₁', S₂', S₃' (S₄' and S₅ already done).
- ✅ T2-F1: `norm_three_factor_exp_product_sub_one_le` —
  `‖P-1‖ ≤ exp(s)-1` (Palindromic.lean).
- ✅ T2-F2: `norm_three_factor_exp_product_sub_one_lt_one` —
  `‖P-1‖ < 1` for `s < log 2` (Palindromic.lean).
- ✅ T2-F3: `norm_logOnePlus_sub_sub_sub_sub_sub_sub_le` — deg-7 log series
  tail bound `‖.‖ ≤ ‖x‖⁷/(1-‖x‖)` (LogSeries.lean).
- ✅ T2-F4: `bch_bch_half_eq_logOnePlus_strangBlock_sub_one` — bridge:
  `bch(bch(½a, b), ½a) = logOnePlus(P-1)` (Palindromic.lean).
- ✅ T2-F5: `norm_logOnePlus_strangBlock_sub_through_deg_6_le` — deg-7 tail
  bound on `logOnePlus(P-1)` in terms of `s` (Palindromic.lean).
- ✅ T2-F6: `symmetric_bch_cubic_sub_polynomial_in_y_le` — combined
  framework bound: `‖sym_bch_cubic - polynomial-in-y‖ ≤ tail`
  (Palindromic.lean).
- ✅ T2-F7-aux: `norm_three_factor_exp_product_sub_one_sub_add_le` —
  `‖P − 1 − (a+b)‖ ≤ exp(s) − 1 − s`. Plus inductive helper
  `norm_mul_exp_sub_one_sub_le` (deg-2 chain step).
- ✅ T2-F7-prelim: `norm_polynomial_in_y_sub_add_le` — coarse O(s²) bound
  on the deg-2+ residual of polynomial_in_y after subtracting (a+b). Sums
  per-term ‖y^k/k‖ bounds via triangle inequality.
- ✅ T2-F7-prelim2: `norm_polynomial_in_y_sub_add_sub_E3_le` — tighter
  O(s⁵) bound after subtracting (a+b) and sym_E₃. Uses cubic template +
  T2-F6 framework via triangle inequality.
- ✅ T2-F7g-coarse: `norm_polynomial_in_y_sub_add_sub_E3_sub_E5_le` —
  coarse O(s⁵) version of the final T2-F7g target after subtracting also
  sym_E₅. Strongest provable bound from existing infrastructure (modulo
  alt-form axiom T2-B); final O(s⁷) requires algebraic deg-5 cancellation
  (T2-F7e).
- ✅ T2-F7g-tight: `norm_polynomial_in_y_sub_add_sub_E3_sub_E5_via_parent` —
  O(s⁷) version derived FROM THE PARENT AXIOM. Forward direction.
- ✅ T2-F-equiv: `symmetric_bch_quintic_sub_poly_le_via_T2F7g` — reverse
  direction: any T2-F7g witness `K` discharges the parent with bound
  `K + tail`. Together with T2-F7g-tight establishes mathematical
  equivalence T2-F7g ⟺ parent axiom.
- ✅ T2-G: `norm_symmetric_bch_quintic_correction_poly_le` — norm bound
  on the 25-term correction polynomial: `‖correction(a,b)‖ ≤ s⁵`.
  Sum of |numerators|/11520 = 1360/11520 ≈ 0.118 < 1.

**Pending sub-tasks**:

**T2-C** (revised): `symmetric_bch_sextic_part_zero` — assert that the
deg-6 part of `sym_bch_cubic - sym_E₃ - sym_E₅` equals zero (palindromic
vanishing of even degrees in the 3-factor product).

**T2-D** (revised): Extended `hdecomp`. The natural per-piece
decomposition (R₁_sextic, R₂_sextic, 7 terms) gives only O(s⁶) per term.
**This decomposition cannot achieve O(s⁷) by itself.**

**T2-E** (revised): **Critical reassessment after session 17 analysis**:
For `s ≤ 1/4`, an O(s⁶) per-piece bound CANNOT imply O(s⁷): the
relationship is `s⁶ > s⁷` for `s < 1`. Achieving O(s⁷) requires exploiting
the palindromic deg-6 cancellation algebraically.

**Revised discharge strategy** (replaces the per-piece T2-C/D/E approach):

Treat `sym_bch_cubic - sym_E₃ - sym_E₅` directly as the deg-7+ tail of
`log(exp(½a)·exp(b)·exp(½a))`. Bound this tail via a series convergence
argument analogous to `norm_bch_quintic_remainder_le` (Basic.lean:2873,
~750 lines).

Specifically, write the 3-factor Strang product as:
```
P(a, b) := exp(½a) · exp(b) · exp(½a)
log(P) = (a+b) + sym_E₃(a, b) + sym_E₅(a, b) + sym_E₇(a, b) + ...
       (palindromic: deg 2, 4, 6 vanish identically)
```

The bound `‖log(P) - through-deg-5‖ ≤ K · s⁷ / (constant)` follows from:
1. P - 1 has tail bounded by `(exp(s/2)·exp(s)·exp(s/2)) - 1 - (deg≤6 sum)`.
2. log(1+y) tail bounded by `‖y‖^7 · series tail`.
3. Combine with explicit identification of deg-1, deg-3, deg-5 contributions
   (the latter via the just-discharged alt-form lemma).

**Estimated size**: ~1000-1500 lines (mirrors the structure of
`norm_bch_quintic_remainder_le`, but for the 3-factor symmetric product).

**Per-piece decomposition (T2-C/D/E original) is REJECTED** as a path —
fundamentally cannot reach O(s⁷) without the full Tier-1 sextic
infrastructure (additional ~1500 lines for `bch_sextic_term` +
`norm_bch_septic_remainder_le`).

**Recommendation for next session**: Discharge T2-F7e via Option B
(extending the cubic template `norm_symmetric_bch_cubic_sub_poly_le` at
`Basic.lean:5834`). The recommended structure:

1. **Inner BCH expansion to deg-5**: define
   `inner_R₆ := z - (a'+b) - ½[a',b] - C₃(a',b) - C₄(a',b) - bqt(a',b)`
   (the deg-6+ remainder after subtracting the explicit deg-5 contribution).
   Bound: `‖inner_R₆‖ ≤ K · s⁶` via `norm_bch_sextic_remainder_le`.
2. **Outer BCH expansion to deg-5**: similarly define `outer_R₆`.
3. **Sextic identity**: an algebraic identity (analog of
   `symmetric_bch_quartic_identity` at `Basic.lean:5760`) showing that
   the sum of all deg-6 contributions to `sym_bch_cubic - sym_E₃ - sym_E₅`
   equals zero. **Try `match_scalars <;> ring` first** — same technique as
   the alt-form discharge.
4. **Extended hdecomp**: rewrite `sym_bch_cubic - sym_E₃ - sym_E₅` as a
   sum of ~7 pieces, each O(s⁷) using the sextic identity for deg-6
   cancellation.
5. **Per-piece bounds**: each new term needs O(s⁷) constant.

**Estimated size**: ~1000-1500 lines total, but possibly less if
`match_scalars` works for the sextic identity.

The alt-form discharge (T2-B) is now in place to support step 4
(absorbing the deg-5 contribution from `bqt(a', b) + bqt(a'+b, a')`).

## Lean-Trotter interface (axioms 1–3)

`Lean-Trotter/LieTrotter/Suzuki4ViaBCH.lean` has three BCH-interface axioms:

1. `bch_w4Deriv_quintic_level2` — unit-coefficient pointwise τ⁵ bound.
   **Discharged session 12** via `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le`.
2. `bch_w4Deriv_level3_tight` — tight γᵢ at Suzuki p.
   **Discharged session 8** via `BCH.suzuki5_log_product_quintic_tight_at_suzukiP`.
3. `bch_uniform_integrated` — order-7 + R₇ + FTC-2 integrated bound.
   Currently `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` (Lean-BCH side).

**Key public theorems on this branch** (depend only on Lean's 3 standard +
B1.c Tier-2 axiom + `suzuki5_log_product_septic_at_suzukiP_axiom`):
- `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` (P1 headline).
- `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` (P1 bridge corollary).
- `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` (P2 bridge).
- `BCH.norm_bch_sextic_remainder_le` (Tier-1 of B1.c, fully proven
  session 16).
- `BCH.norm_bch_septic_remainder_le` (T2-F7e infra step 4, **fully proven**
  session 19; no longer depends on a small-s axiom — `Basic.lean` has 0
  remaining axioms).

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
