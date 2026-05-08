# T2-F7e Session Prompt — Discharge Parent Tier-2 Axiom

## Current State (after session 19, all I2 wrapper inputs in place)

- **0 sorries**, **3 scoped private axioms** (unchanged):
  - `symmetric_bch_quintic_sub_poly_axiom` (parent Tier-2 — final target)
  - `norm_bch_septic_remainder_small_s_axiom` (session 18, stepping stone)
  - `suzuki5_log_product_septic_at_suzukiP_axiom` (axiom 3)
- **T2-F7g ⟺ parent axiom** Lean-proved (bidirectional equivalence).
- **23+ commits in session 18 + 8 commits in session 19**.

## Session 19 progress (Phase A foundation + algebraic identities + I2 inputs)

- Step 8 (Phase A.1): `y4_sub_z4_sub_y4_5_sub_y4_6_decomp` (16-term algebraic
  identity, `noncomm_ring`) + `norm_y4_sub_z4_sub_y4_5_sub_y4_6_le`
  (`≤ 85·s⁷`). The S₃' = ¼·(y⁴-z⁴-y4_5-y4_6) piece bound = `≤ 22·s⁷`.
- Step 9 (level-7 exp tail): `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le`
  (noncomm) + `real_exp_seventh_order_le_septic` (real `≤ s⁷` for `s < 3/4`).
  Foundation for the H_a → I_a refinement in Phase A.2.
- Step 10 (Phase A.2 — I1 algebraic): `I1_septic_residual_decomp_eq`.
  12-term algebraic identity extending `I1_residual_decomp_eq` by subtracting
  `corr₁_6 = ½·W6`. Proof via `match_scalars <;> ring`, `maxHeartbeats 8000000`.
  All 12 RHS pieces are deg-7+ — **after combining the three "tricky"
  smul'd terms with cancellation**.
- Step 11 (Phase A.2 — I2 algebraic): `I2_septic_residual_decomp_eq`.
  Pure ring identity in `(z, P, T₂, T₃, T₄)` extending `I2_residual_decomp_eq`
  by subtracting `y3_6` (the deg-6 leading of `(z+P)³ - z³`). Proof via
  `noncomm_ring`. All 7 RHS pieces are deg-7+.
- Step 12 (Phase A.4 — RHS bound wrappers): `norm_I1_septic_residual_RHS_le`
  and `norm_I2_septic_residual_RHS_le`. Both take precomputed bounds and
  combine via triangle inequality. The I1 wrapper bounds by
  `(7 + (C₁+C₂+C₃)/2)·s⁷` (parameterized over 3 "tricky" piece bounds);
  the I2 wrapper bounds by `(3·K_PmT4 + 2·K_P2 + K_PzP + K_P3)·s⁷`
  (parameterized over 4 input bounds).

  **Note on I1 wrapper**: Per individual-piece analysis, the I1 wrapper's
  C₁, C₂, C₃ parameters cannot be satisfied as constants — each tricky piece
  is naturally deg-6, not deg-7. Cancellation occurs only in the SUM
  `(z·R+R·z) + T22 + T_extra`. The I1 wrapper needs redesign (to take a
  single combined bound) before assembly.
- Step 13 (Phase A.4 — P³-T₂³ helper): `norm_P3_sub_T23_le`. Bound
  `‖P³ - T₂³‖ ≤ 15·s⁷` via 3-fold telescoping
  `(P-T₂)·P² + T₂·(P-T₂)·P + T₂²·(P-T₂)`. Concrete value of K_P3 = 15
  for the I2 wrapper.
- Step 14 (Phase A.4 — P-T₂-T₃-T₄ helper): `norm_P_sub_T2_sub_T3_sub_T4_le`.
  Bound `‖P-T₂-T₃-T₄‖ ≤ 6·s⁵` via 7-term decomposition
  `G₁+G₂+a·F₂+F₁·b+E₁·E₂+½·E₁·b²+½·a²·E₂`.
  **Algebraic identity proved via `linear_combination` from
  `R_eq_neg_deg5_residual`** (avoiding the failing standalone
  `match_scalars <;> ring`: scalar mismatch in canonical form for the
  E₁·E₂ deg-4 term in the opaque setting). Concrete K_PmT4 = 6 for I2.
- Step 15 (Phase A.4 — PzP-T₂zT₂-... helper): `norm_PzP_sub_T2zT2_etc_le`.
  Bound `‖PzP-T₂zT₂-T₂zT₃-T₃zT₂‖ ≤ 13·s⁷` for `s ≤ 1/10`. Decomposition
  via `P = T₂ + T₃ + (P-T₂-T₃)` into 6 terms. Concrete K_PzP = 13 for I2.
- Step 16 (Phase A.4 — R+T₅ algebraic): `R_plus_T5_eq_neg_deg6_residual`.
  Identity `T₃ - E₁ - E₂ - Q + T₄ + T₅ = -(H₁+H₂+a·G₂+G₁·b+E₁·E₂+½·F₁·b²+½·a²·F₂)`.
  Each RHS piece is deg-6+ — exposes `R₅ = -T₅` deg-5 cancellation
  algebraically. Proof via `linear_combination` from `R_eq_neg_deg5_residual`
  with `match_scalars + ring` for scalar normalization.
- Step 17 (Phase A.4 — R+T₅ norm bound): `norm_R_plus_T5_residual_sum_le`.
  Analog of `norm_R_residual_sum_le` at one degree higher: `≤ 6·s⁶`.
  All 7 inputs uniformly deg-6, no small-s constraint needed.
  Combined with step 16: `‖R + T₅‖ ≤ 6·s⁶`.
- Step 18 (Phase A.4 — combined tricky bound): `norm_combined_tricky_le`.
  `‖(z·R+R·z) + T22 + T_extra‖ ≤ 28·s⁷` for `s ≤ 1/10`. Algebraic identity
  reduces the LHS to `z·(R+T₅) + (R+T₅)·z - P²_deg≥7` via `noncomm_ring`
  after substituting `P = T₂+T₃+T₄+D₅`. Then 12 component bounds
  (2 from R+T₅ part, 10 from P²_deg≥7) + nlinarith with auxiliary
  `s⁸ ≤ s⁷/10`, `s⁹ ≤ s⁷/100`, `s¹⁰ ≤ s⁷/1000` (using s ≤ 1/10).
  Maxheartbeats 4M.
- Step 19 (Phase A.4 — I1 wrapper redesign): `norm_I1_septic_residual_RHS_le`
  rewritten to take a single combined parameter
  `‖z·R+R·z+T22+T_extra‖ ≤ C·s⁷` instead of 3 separate parameters
  (C₁, C₂, C₃ — which were individually unsatisfiable as constants).
  Result bound: (7 + C/2)·s⁷. Combined with step 18 (C=28):
  I1 RHS ≤ 21·s⁷ for s ≤ 1/10. Proof uses `abel` re-association
  + `← smul_add` factoring.

**I2 wrapper inputs now all available**: K_PmT4=6, K_P2=15, K_PzP=13, K_P3=15.
Combined I2 RHS bound: (3·6 + 2·15 + 13 + 15)·s⁷ = 76·s⁷ for `s ≤ 1/10`.

**I1 wrapper now satisfiable**: with C = 28 from `norm_combined_tricky_le`,
I1 RHS ≤ 21·s⁷.

**All pieceB_septic_decomp piece bounds available**:
- S₁' (I₁) ≤ 21·s⁷ ✅
- S₂' (I₂) ≤ 76·s⁷ ✅
- S₃' (¼·(y⁴-z⁴-y4_5-y4_6)) ≤ ¼·85·s⁷ ≈ 22·s⁷ ✅
- S₄' (⅕·(y⁵-z⁵-y5_6)) ≤ ⅕·51·s⁷ ≈ 11·s⁷ ✅
- S₅ (⅙·(y⁶-z⁶)) ≤ ⅙·63·s⁷ ≈ 11·s⁷ ✅
- Total pieceB''' ≤ ~141·s⁷.

## Session 18 accomplishments

**Methodology breakthrough**: `match_scalars <;> ring` for poly identities in
𝕂-modules. Standard template:
```lean
unfold <all definitions>
simp only [smul_sub, smul_add, smul_neg, smul_smul, mul_smul_comm,
  smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
match_scalars <;> ring
```
With `← mul_assoc` for left-association and `show name = expansion from rfl`
for let-bindings. Refactored 11 algebraic identities (700+ lines → ~50 lines).

**T2-B alt-form**: `symmetric_bch_quintic_poly_alt_form` proved (5 lines).

**Septic infrastructure** (steps 1-7):
- Step 1: `bch_sextic_term` defined (28 terms, LCM 1440) + homogeneity + norm bound.
- Step 2: `septic_pure_identity` (deg-6 cancellation) proved.
- Step 3: `norm_bch_septic_remainder_large_s_le` (s ≥ 1/10 case).
- Step 4: Public `norm_bch_septic_remainder_le` (with small-s axiom).
- Step 5: `pow6_sub_zpow6_telescope` + `norm_pow6_sub_zpow6_le` (≤ 63·s⁷).
- Step 6: `norm_pow4_sub_zpow4_le` (≤ 15·s⁵), `y5_sub_z5_sub_y5_6_decomp`,
  `norm_y5_sub_z5_sub_y5_6_le` (≤ 51·s⁷).
- Step 7: **`pieceB_septic_decomp`** — central decomposition, 5 lines via
  `linear_combination (norm := module) hQPI + hSPI + hSeptic`.

## Remaining work for T2-F7e

### Phase A: Complete `norm_bch_septic_remainder_small_s_le`

**Currently axiom-ized**: `norm_bch_septic_remainder_small_s_axiom` provides
the `s < 1/10` case bounded by `1000·s⁷/(2-exp(s))`. Discharging this is
the next major step.

The proof structure (mirroring `norm_bch_sextic_remainder_small_s_le`):
1. Decompose LHS as `pieceA + pieceB'''`.
2. pieceA = log series tail, bounded by `‖y‖⁷/(1-‖y‖)`.
3. pieceB''' = use `pieceB_septic_decomp` to split into 5 pieces:
   - **S₁'** = (I₁ - corr₁ - corr₁_5 - corr₁_6): TODO bound (~60 lines)
   - **S₂'** = (I₂ - corr₂ - corr₂_5 - corr₂_6): TODO bound (~60 lines)
   - **S₃'** = ¼·(y⁴-z⁴-y4_5-y4_6): TODO bound (~70 lines, needs new helper)
   - **S₄'** = ⅕·(y⁵-z⁵-y5_6): bound = `⅕·51·s⁷ ≈ 11·s⁷` ✅ via `norm_y5_sub_z5_sub_y5_6_le`
   - **S₅** = ⅙·(y⁶-z⁶): bound = `⅙·63·s⁷ ≈ 11·s⁷` ✅ via `norm_pow6_sub_zpow6_le`
4. Combine: `‖pieceA + pieceB'''‖ ≤ pieceA_bound + ΣS_i_bound`.
5. Total ~ 1000·s⁷ for s ≤ 1/10 (matching the small-s axiom statement).

### Phase A sub-tasks

1. **`norm_y4_sub_z4_sub_y4_5_sub_y4_6_le`** (S₃' bound): ✅ **DONE session 19**.
   - 16-term algebraic decomposition (`y4_sub_z4_sub_y4_5_sub_y4_6_decomp`):
     - 4 weight-1 (P-T₂-T₃)·z's terms (T₃ correction completes (P-T₂)→(P-T₂-T₃))
     - 7 deg-7 terms from `(y³-z³)P − 3 T₂²` (using compound `(y²-z²)·P²` and `z²·(P²-T₂²)`)
     - 4 deg-7 terms from `(y²-z²)·P·z − 2 T₂²` (using compound `z·(P²-T₂²)·z`)
     - 1 deg-7 term: `(P²-T₂²)·z²`.
   - Bound `≤ 85·s⁷` via 16 individual `norm_mul_le` chains + 15 `norm_add_le`
     applications + `nlinarith [pow_nonneg hs_nn 7]`. `maxHeartbeats 4000000`.

2. **Level-7 exp tail lemmas**: ✅ **DONE session 19**.
   - `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le` (noncomm): bounds
     `‖exp(x) − Σ_{k=0}^6 x^k/k!‖ ≤ Real.exp(‖x‖) − Σ_{k=0}^6 ‖x‖^k/k!`.
   - `real_exp_seventh_order_le_septic` (real): for `0 ≤ s < 3/4`,
     `Real.exp(s) − Σ_{k=0}^6 s^k/k! ≤ s⁷`.
   - Foundation: defines `I_a := H_a − (720)⁻¹·a⁶` with `‖I_a‖ ≤ α⁷`.

3. **I1/I2 algebraic decompositions with corr*_6**: ✅ **DONE session 19**
   (steps 10, 11). Both `I1_septic_residual_decomp_eq` and
   `I2_septic_residual_decomp_eq` proved as pure algebraic identities.

4. **Norm bounds for I1/I2 septic residual RHS** (S₁', S₂'): partially DONE.

   **I2 inputs all done** (steps 12-15 of session 19):
   - K_PmT4 = 6 from `norm_P_sub_T2_sub_T3_sub_T4_le` ✅
   - K_P2 = 15 from existing `norm_T22_sub_P2_etc_le` (sign flip) ✅
   - K_PzP = 13 from `norm_PzP_sub_T2zT2_etc_le` ✅
   - K_P3 = 15 from `norm_P3_sub_T23_le` ✅
   - I2 RHS bound: `(3·6 + 2·15 + 13 + 15)·s⁷ = 76·s⁷` for s ≤ 1/10. ✅

   **I1 simple bounds** (still TODO; mostly inline calculations):
   - `‖I_a‖ ≤ s⁷`, `‖I_b‖ ≤ s⁷`: compose level-7 exp tail with `pow_le_pow_left₀`.
   - `‖a·H₂‖ ≤ α·β⁶ ≤ s⁷`, `‖H₁·b‖ ≤ α⁶·β ≤ s⁷`.
   - `‖½·a²·G₂‖ ≤ s⁷/2`, `‖½·G₁·b²‖ ≤ s⁷/2`.
   - `‖(1/6)·a³·F₂‖ ≤ s⁷/6`, `‖(1/6)·F₁·b³‖ ≤ s⁷/6`, `‖F₁·F₂‖ ≤ s⁸`.

   **I1 tricky combined bound** (needs new infrastructure):
   - Individual pieces (z·R+R·z, T22, T_extra) are deg-6, NOT deg-7.
   - Cancellation only in the SUM `(z·R+R·z) + T22 + T_extra`.
   - Need: `R_plus_T5_decomp_eq` (alg identity), `norm_R_plus_T5_le ≤ 6·s⁶`,
     `norm_combined_tricky_le ≤ ~27·s⁷`.
   - Plus: redesign `norm_I1_septic_residual_RHS_le` to take a single combined
     bound parameter instead of three separate.

   Estimated ~150 lines for the tricky combined bound.

5. **Assembly into `norm_bch_septic_remainder_small_s_le`** (~150 lines):
   - Mirror `norm_bch_sextic_remainder_small_s_le` (line ~4957 in `Basic.lean`,
     ~580 lines).
   - Use `pieceB_septic_decomp` (already done).
   - Combine the 5 piece bounds via triangle inequality.
   - Plus pieceA bound (deg-7 log series tail).

**Total remaining for Phase A**: ~300 lines (split between I1 redesign + assembly).

### Phase B: Discharge the parent (extend cubic template)

After Phase A, `norm_bch_septic_remainder_le` is fully proved. Then extend
the cubic template at `Basic.lean:5834` (~700 lines) to discharge the parent
axiom. Estimated ~300-500 lines.

The structure:
1. Inner BCH expansion to deg-6: `inner_R₇ := bch(a',b) - through-deg-6`,
   bounded by `norm_bch_septic_remainder_le` ≤ K·s₁⁷.
2. Outer BCH expansion: similar.
3. Symmetric sextic identity for deg-6 cancellation in the symmetric case.
4. Per-piece O(s⁷) bounds.
5. Final triangle inequality.

## Useful framework lemmas (already in place)

**Algebraic identities**:
- `BCH.symmetric_bch_quintic_poly_alt_form` (T2-B, session 18, 5 lines)
- `BCH.bch_sextic_term` + homogeneity + norm bound (NEW session 18)
- `BCH.septic_pure_identity` (deg-6 cancellation, NEW session 18)
- `BCH.pieceB_septic_decomp` (central decomposition, NEW session 18)

**Norm bounds** (existing + new through session 19):
- `BCH.norm_bch_sextic_remainder_le` (≤ 100000·s⁶/(2-exp(s)))
- `BCH.norm_bch_septic_remainder_large_s_le` (s ≥ 1/10, ≤ 1000010·s⁷/...)
- `BCH.norm_bch_septic_remainder_le` (public, with small-s axiom)
- `BCH.norm_pow6_sub_zpow6_le` (≤ 63·s⁷, session 18)
- `BCH.norm_pow4_sub_zpow4_le` (≤ 15·s⁵, session 18)
- `BCH.norm_y5_sub_z5_sub_y5_6_le` (≤ 51·s⁷, session 18)
- `BCH.norm_y4_sub_z4_sub_y4_5_sub_y4_6_le` (≤ 85·s⁷, NEW session 19)
- `BCH.norm_y4_sub_z4_sub_y4_5_le` (existing, ≤ 31·s⁶)
- `BCH.norm_pow_n_sub_zpow_n_le` for n=2,3,5 (existing)
- `BCH.norm_P_sub_T2_sub_T3_le` (≤ 5·s⁴)
- `BCH.norm_P2_sub_T22_le` (≤ 10·s⁵)
- `BCH.norm_PzP_sub_T2zT2_le` (existing)

**Exp tail bounds** (existing + new session 19):
- `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le` (level-7 noncomm, NEW)
- `real_exp_seventh_order_le_septic` (real, ≤ s⁷ for s < 3/4, NEW)

## Recommended starting point for next session

**The I2 path is unblocked.** All four input bounds for `norm_I2_septic_residual_RHS_le`
are now available (K_PmT4=6, K_P2=15, K_PzP=13, K_P3=15). The I2 wrapper
gives a clean ≤ 76·s⁷ bound.

**The I1 path requires a structural redesign.** The current
`norm_I1_septic_residual_RHS_le` takes three separate parameters
(C₁ for `‖z·R+R·z‖`, C₂ for `‖T22‖`, C₃ for `‖T_extra‖`), each of which
is naturally a deg-6 quantity. The deg-7 cancellation only occurs in the
**combined** sum `(z·R+R·z) + T22 + T_extra`.

### I1 redesign plan — ALL DONE ✅

1. **`R_plus_T5_eq_neg_deg6_residual`** (algebraic identity): ✅ DONE step 16.
2. **`norm_R_plus_T5_residual_sum_le`** (≤ 6·s⁶): ✅ DONE step 17.
3. **`norm_combined_tricky_le`** (≤ 28·s⁷): ✅ DONE step 18.
4. **`norm_I1_septic_residual_RHS_le` redesign**: ✅ DONE step 19.

### Final assembly (~500 lines, mirror of session-16 sextic discharge)

After the I1 redesign (step 19):
1. Use `pieceB_septic_decomp` to split LHS into pieceA + 5 sub-pieces.
2. Bound pieceA via deg-7 log series tail (`norm_logOnePlus_sub_sub_sub_sub_sub_sub_le`).
3. Bound S₁' (I₁) ≤ 21·s⁷ via I1 wrapper (step 19) + combined tricky (step 18).
4. Bound S₂' (I₂) ≤ 76·s⁷ via I2 wrapper.
5. Bound S₃', S₄', S₅ via existing helpers.
6. Combine via triangle inequality. Total pieceB''' ≤ ~141·s⁷, plus pieceA.
   Net ~1000·s⁷/(2-exp(s)) for `s ≤ 1/10`, matching the small-s axiom.

The structure mirrors `norm_bch_sextic_remainder_small_s_le` (line ~6338,
~580 lines), extended one degree higher.

**Bypass strategy** (if Phase A is deferred): keep
`norm_bch_septic_remainder_small_s_le` axiom-ized and focus on Phase B
(parent discharge using `norm_bch_septic_remainder_le` as a black box).
Phase A.3 can be revisited later — the public
`norm_bch_septic_remainder_le` already exists with the small-s axiom
dependency, so downstream work can proceed.

## Methodology reminders

- Try `match_scalars <;> ring` first for any new poly identity in 𝕂-modules.
- For `let`-binding chains, use `intros` + `simp only [show name = expansion
  from rfl, ...]` to expand them.
- Add `← mul_assoc` to the simp set when products of more than 2 letters appear.
- Don't worry about heartbeat reductions for performance — they don't help
  wall-clock (per BCH session 18 A/B test). Reduce only for code quality.
- Use `linear_combination (norm := module) <list of identities>` for piece
  decompositions that combine multiple pure_identity lemmas.

## Success criteria

- Parent axiom `symmetric_bch_quintic_sub_poly_axiom` discharged.
- Repository: 0 sorries, **1 scoped axiom** (just axiom 3).
- All downstream theorems still build:
  `BCH.norm_symmetric_bch_quintic_sub_poly_le`,
  `BCH.norm_strangBlock_log_sub_quintic_target_le`.
