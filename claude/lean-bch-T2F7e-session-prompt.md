# T2-F7e Session Prompt — Discharge Parent Tier-2 Axiom

## Current State (after session 19, S₃' bound + level-7 exp tail in place)

- **0 sorries**, **3 scoped private axioms**:
  - `symmetric_bch_quintic_sub_poly_axiom` (parent Tier-2 — final target)
  - `norm_bch_septic_remainder_small_s_axiom` (session 18, stepping stone)
  - `suzuki5_log_product_septic_at_suzukiP_axiom` (axiom 3)
- **T2-F7g ⟺ parent axiom** Lean-proved (bidirectional equivalence).
- **23+ commits in session 18 + 2 commits in session 19**.

## Session 19 progress (Phase A foundation + algebraic identities)

- Step 8 (Phase A.1): `y4_sub_z4_sub_y4_5_sub_y4_6_decomp` (16-term algebraic
  identity, `noncomm_ring`) + `norm_y4_sub_z4_sub_y4_5_sub_y4_6_le`
  (`≤ 85·s⁷`). The S₃' = ¼·(y⁴-z⁴-y4_5-y4_6) piece bound = `≤ 22·s⁷`.
- Step 9 (level-7 exp tail): `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_le`
  (noncomm) + `real_exp_seventh_order_le_septic` (real `≤ s⁷` for `s < 3/4`).
  Foundation for the H_a → I_a refinement in Phase A.2.
- Step 10 (Phase A.2 — I1 algebraic): `I1_septic_residual_decomp_eq`.
  12-term algebraic identity extending `I1_residual_decomp_eq` by subtracting
  `corr₁_6 = ½·W6`. Proof via `match_scalars <;> ring`, `maxHeartbeats 8000000`.
  All 12 RHS pieces are deg-7+.
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
- Step 13 (Phase A.4 — P³-T₂³ helper): `norm_P3_sub_T23_le`. Bound
  `‖P³ - T₂³‖ ≤ 15·s⁷` via 3-fold telescoping
  `(P-T₂)·P² + T₂·(P-T₂)·P + T₂²·(P-T₂)`. Concrete value of K_P3 = 15
  for the I2 wrapper.

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

4. **Norm bounds for I1/I2 septic residual RHS** (S₁', S₂'): TODO.
   The RHS of `I1_septic_residual_decomp_eq` has 9 cluster expressions:
   - `I_a` (= H₁ - (720)⁻¹·a⁶) ← bound `≤ s⁷` via level-7 exp tail.
   - `I_b` ← `≤ s⁷`.
   - `a·H₂` ← `α·β⁶ ≤ s⁷`.
   - `H₁·b` ← `α⁶·β ≤ s⁷`.
   - `(1/6)·a³·F₂ + (1/6)·F₁·b³ + F₁·F₂` ← bounded individually (s⁷·O(1)).
   - `(2)⁻¹·a²·G₂` ← `≤ s⁷/2`.
   - `(2)⁻¹·G₁·b²` ← `≤ s⁷/2`.
   - `(2)⁻¹·(z·R + R·z)` ← still bounded by 6·s⁶ in the existing bound;
     to get s⁷, need either tighter `R+T₅` analysis or a different approach.
   - `(2)⁻¹·(T₂² - P² + T₂T₃ + T₃T₂)` ← currently 7.5·s⁶; need refinement.
   - `(2)⁻¹·(z·T₅ + T₂T₄ + T₃² + T₄T₂ + T₅z)` ← new: needs bounding.

   For I2, RHS has 7 clusters. Several can use existing bounds:
   - 3 weight-1 (P-T₂-T₃-T₄): need new helper for `‖P-T₂-T₃-T₄‖ ≤ K·s⁵`.
   - 3 weight-2 compound (e.g., `z(P²-T₂²-T₂T₃-T₃T₂)`): existing
     `norm_T22_sub_P2_etc_le` gives ‖T₂²-P²+T₂T₃+T₃T₂‖ ≤ 15·s⁶, so
     `z·(...)` ≤ 15·s⁷. ✓
   - `(P³ - T₂³)`: telescopes as `(P-T₂)·P² + T₂·(P-T₂)·P + T₂²·(P-T₂)`,
     each ≤ 5s³·s⁴ = 5s⁷ (sum 15·s⁷).

   Most challenging pieces:
   - The `½·(z·R + R·z) + ½·(z·T₅ + ... + T₅·z)` cluster — these need
     algebraic refactoring of `R + T₅` to expose deg-6+ structure for the
     z-multiplications to give deg-7. Possibly via expressing `R + T₅` in
     terms of higher exp tail variables (G_a, H_a) plus mixed terms.
   - `‖P - T₂ - T₃ - T₄‖ ≤ K·s⁵`: a new helper analogous to existing
     `norm_P_sub_T2_sub_T3_le` (extends one degree).

   Estimated ~200-300 lines.

5. **Assembly into `norm_bch_septic_remainder_small_s_le`** (~150 lines):
   - Mirror `norm_bch_sextic_remainder_small_s_le` (line ~4957 in `Basic.lean`,
     ~580 lines).
   - Use `pieceB_septic_decomp` (already done).
   - Combine the 5 piece bounds via triangle inequality.
   - Plus pieceA bound (deg-7 log series tail).

**Total remaining for Phase A**: ~350-450 lines (mostly task #4).

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

Steps 8–11 of session 19 establish:
- The S₃' bound (Phase A.1) — fully discharged.
- Level-7 exp tail (foundation for I_a/I_b) — ready.
- I1/I2 algebraic identities for the septic case — ready.

**Next step: norm bounds for the I1/I2 septic RHS pieces.**

Quick wins (simple `norm_mul_le` chains):
- `‖I_a‖ ≤ s⁷`, `‖I_b‖ ≤ s⁷`: compose level-7 exp tail with `pow_le_pow_left₀`.
- `‖a·H₂‖ ≤ α·β⁶ ≤ s⁷`, `‖H₁·b‖ ≤ α⁶·β ≤ s⁷`.
- `‖½·a²·G₂‖ ≤ s⁷/2`, `‖½·G₁·b²‖ ≤ s⁷/2`.
- `‖(1/6)·a³·F₂‖ ≤ s⁷/6`, `‖(1/6)·F₁·b³‖ ≤ s⁷/6`, `‖F₁·F₂‖ ≤ s⁸ ≤ s⁷·s`.
- `‖(P²-T₂²-T₂T₃-T₃T₂)·z‖ ≤ 15·s⁷` via `norm_T22_sub_P2_etc_le`.
- `‖P³ - T₂³‖`: write as `(P-T₂)·P² + T₂·(P-T₂)·P + T₂²·(P-T₂)`. Each ≤ 5s⁷.

Tricky pieces:
- `‖½·(z·R + R·z) + ½·(z·T₅ + ... + T₅·z)‖`. Needs refactoring of `R+T₅`.
  Specifically `R + T₅ = T₃ + T₄ + T₅ - E₁ - E₂ - Q`. Using
  `E_i = T_3_a + T_4_a + T_5_a + H_a` (where T_k_a = a^k/k! is the pure-a
  part of T_k, similar for b), get `R + T₅ = T_mixed_3+4+5 - H₁ - H₂ - Q`.
  Each piece is deg-5+ in s; multiplying by z gives deg-6 leading. Hmm,
  not directly deg-7. Need finer analysis (perhaps separate the `Q`
  contribution carefully).
- `‖P - T₂ - T₃ - T₄‖`: new helper analogous to `norm_P_sub_T2_sub_T3_le`.
  Bound `≤ K·s⁵` for some constant K. Required for the 3 weight-1 pieces
  in I2's RHS.

**Bypass strategy** (if the tricky pieces are too hard): keep
`norm_bch_septic_remainder_small_s_le` axiom-ized for now and focus on
Phase B (parent discharge using `norm_bch_septic_remainder_le` as a black
box). Phase A.3 can be revisited later — the public
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
