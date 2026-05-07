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

### Decomposition into sub-tasks T2-A through T2-G

**Session 17 progress** (substantial — 12 commits, 6 working lemmas):
- ✅ T2-A: CAS `Lean-Trotter/scripts/discover_quintic_alt_form.py` discovers
  the explicit alt-form decomposition (residual = 0). Outputs the combined
  correction polynomial (25 terms, denom 11520).
- ✅ T2-B: `BCH.symmetric_bch_quintic_correction_poly` defined. Alt-form
  lemma added as scoped axiom `symmetric_bch_quintic_poly_alt_form_axiom`.
  Tactical discharge needs ~150-200 lines of comprehensive scalar
  enumeration following `symmetric_bch_quartic_identity` pattern.
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

**Recommendation for next session**: Discharge T2-F7 — the algebraic
identity that the deg-1, 3, 5 parts of `(y - y²/2 + y³/3 - y⁴/4 + y⁵/5
- y⁶/6)` equal `(a+b) + sym_E₃ + sym_E₅`, with deg-2, 4, 6 vanishing
palindromically. This is the LAST piece of the T2-F discharge.

Form: prove `‖[y - y²/2 + ... - y⁶/6] - (a+b) - sym_E₃ - sym_E₅‖ ≤
K · s⁷`. Combined with T2-F6 via triangle inequality, gives the parent
bound `‖sym_bch_cubic - sym_E₃ - sym_E₅‖ ≤ (K + K') · s⁷`.

Estimated: 500-1000 lines (algebraic expansions of y, y², ..., y⁶ to
deg ≤ 6 + bounds on the deg-7+ residuals).

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
