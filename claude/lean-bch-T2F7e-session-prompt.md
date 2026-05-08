# T2-F7e Session Prompt — Discharge Parent Tier-2 Axiom

## Current State (after session 18, substantial T2-F7e foundation in place)

- **0 sorries**, **3 scoped private axioms**:
  - `symmetric_bch_quintic_sub_poly_axiom` (parent Tier-2 — final target)
  - `norm_bch_septic_remainder_small_s_axiom` (NEW session 18, stepping stone)
  - `suzuki5_log_product_septic_at_suzukiP_axiom` (axiom 3)
- **T2-F7g ⟺ parent axiom** Lean-proved (bidirectional equivalence).
- **23+ commits in session 18**, foundation for parent discharge in place.

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

1. **`norm_y4_sub_z4_sub_y4_5_sub_y4_6_le`** (S₃' bound):
   - Algebraic: extend `y4_sub_z4_sub_y4_5_decomp` by subtracting y4_6.
     Each of the 7 terms decomposes as (deg-6 part) + (deg-7+ residual).
     Sum of deg-6 parts = y4_6 (verified by hand).
   - Specifically, the deg-7+ pieces are:
     - z³(P-T₂-T₃), z²(P-T₂-T₃)z, z(P-T₂-T₃)z², (P-T₂-T₃)z³ (4 terms)
     - (y³-z³)P − (z²T₂+zT₂z+T₂z²)·T₂ (deg-7+, expand via telescoping)
     - (y²-z²)Pz − (zT₂+T₂z)·T₂·z (deg-7+)
     - P²z² − T₂²z² = (P²-T₂²)z² (deg-7+, use norm_P2_sub_T22_le)
   - Bounds: 4·5s⁷ + (~5s⁷) + (~3s⁷) + 10s⁵·s² = ~38s⁷ + ε.
   - ~70 lines.

2. **I1/I2 residual decomp + bounds with corr*_6** (S₁', S₂'):
   - Extend `I1_residual_decomp_eq` by adding `- corr₁_6 = -½W6` to the LHS.
     The new RHS will have additional deg-6+ residual terms.
   - Similarly for I2.
   - Bounds use existing per-term norm bounds + new contributions from corr*_6.
   - ~120 lines combined.

3. **Assembly into `norm_bch_septic_remainder_small_s_le`** (~150 lines):
   - Mirror `norm_bch_sextic_remainder_small_s_le` (line ~4957, ~580 lines).
   - Use `pieceB_septic_decomp` (already done).
   - Combine the 5 piece bounds via triangle inequality.
   - Plus pieceA bound.

**Total remaining for Phase A**: ~340 lines.

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

**Norm bounds** (existing + new this session):
- `BCH.norm_bch_sextic_remainder_le` (≤ 100000·s⁶/(2-exp(s)))
- `BCH.norm_bch_septic_remainder_large_s_le` (s ≥ 1/10, ≤ 1000010·s⁷/...)
- `BCH.norm_bch_septic_remainder_le` (public, with small-s axiom)
- `BCH.norm_pow6_sub_zpow6_le` (≤ 63·s⁷, NEW)
- `BCH.norm_pow4_sub_zpow4_le` (≤ 15·s⁵, NEW)
- `BCH.norm_y5_sub_z5_sub_y5_6_le` (≤ 51·s⁷, NEW)
- `BCH.norm_y4_sub_z4_sub_y4_5_le` (existing, ≤ 31·s⁶)
- `BCH.norm_pow_n_sub_zpow_n_le` for n=2,3,5 (existing)
- `BCH.norm_P_sub_T2_sub_T3_le` (≤ 5·s⁴)
- `BCH.norm_P2_sub_T22_le` (≤ 10·s⁵)
- `BCH.norm_PzP_sub_T2zT2_le` (existing)

## Recommended starting point for next session

**Phase A.1** (S₃' bound): Add `y4_sub_z4_sub_y4_5_sub_y4_6_decomp`
(noncomm_ring identity) and `norm_y4_sub_z4_sub_y4_5_sub_y4_6_le`. Most
intricate of the remaining pieces. Should be doable in 100-150 lines.

After that, Phase A.2 (I1/I2 with corr*_6) and Phase A.3 (assembly) follow
the same template as the sextic version.

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
