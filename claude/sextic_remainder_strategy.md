# Sextic Remainder Lean Port Strategy (session 14, B1.c Tier 1)

## Goal

Prove `norm_bch_sextic_remainder_le` in `BCH/Basic.lean`:

```
‖bch a b - z - ½[a,b] - C₃ - C₄ - C₅‖ ≤ 30000 · s⁶ / (2 - exp(s))
```

where `s = ‖a‖+‖b‖`, under hypothesis `s < log 2`.

This extends `norm_bch_quintic_remainder_le` (line 2873, ~750 lines) one degree higher.

## Strategy

**Case split on s ≥ 1/10 (crude) vs s < 1/10 (analytic).**

### Case 1 (s ≥ 1/10): crude bound

```
‖LHS_sextic‖ ≤ ‖LHS_quintic‖ + ‖C₅‖ ≤ 3000s⁵/(2-exp(s)) + s⁵
            ≤ 3001 s⁵/(2-exp(s)) ≤ 30000 s⁶/(2-exp(s))   [since 3001 ≤ 30000s for s ≥ 1/10]
```

### Case 2 (s < 1/10): analytic decomposition

```
LHS_sextic = pieceA + pieceB''
```

- `pieceA = log(1+y) - y + ½y² - ⅓y³ + ¼y⁴ - ⅕y⁵`
  - Bound: ‖pieceA‖ ≤ ‖y‖⁶/(1-‖y‖) ≤ (exp(s)-1)⁶/(2-exp(s)) ≤ 64s⁶/(2-exp(s)) for s < 1.
  - Use lemma `norm_logOnePlus_sub_sub_sub_sub_sub_le` (LogSeries.lean:321).
  
- `pieceB'' = ½W + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅`
  - Equivalently: `pieceB' + ⅕y⁵ - C₅` where `pieceB'` is the quintic algebraic piece.
  - Strategy: deg-5 cancellation via `sextic_pure_identity` (already proved at Basic.lean:2784).

## pieceB'' decomposition

Using sextic_pure_identity: `½W5 + ⅓y3_5 - ¼y4_5 + ⅕z⁵ - C₅ = 0`

Where W5, y3_5, y4_5 are the deg-5 substituted polynomials in {a, b}.

Define:
- `corr₁` = deg-4 of I₁ (already in quintic proof)
- `corr₂` = deg-4 of I₂ (already in quintic proof)
- `corr₁_5 = ½·W5` (deg-5 of I₁)
- `corr₂_5 = ⅓·y3_5` (deg-5 of I₂)
- I₁ = ½W + ⅓z³ - C₃ (same as quintic)
- I₂ = ⅓(y³-z³) (same as quintic)

By QPI (line 2705): `corr₁ + corr₂ - ¼z⁴ - C₄ = 0`
By sextic_pure_identity: `corr₁_5 + corr₂_5 - ¼y4_5 + ⅕z⁵ - C₅ = 0`

Therefore:
```
pieceB'' = (I₁ - corr₁ - corr₁_5) + (I₂ - corr₂ - corr₂_5) - ¼(y⁴ - z⁴ - y4_5) + ⅕(y⁵ - z⁵)
```

(Both QPI and sextic_pure_identity sum to 0 and are subtracted.)

Each of the 4 sub-terms has deg-6+ structure, bounded by Cs⁶.

## Sub-bounds

### Term 1: ‖I₁ - corr₁ - corr₁_5‖

Algebraic decomposition (extending h_regroup from quintic):
```
I₁ - corr₁ - corr₁_5 = H₁ + H₂ + a·G₂ + G₁·b + (E₁E₂ + ½·a²·F₂ + ½·F₁·b²)
                     + ½·(z·R + R·z) + ½·(P₂² - P² + T₂T₃ + T₃T₂)
```
where R = T₃-E₁-E₂-Q+T₄, P₂ = T₂.

Bounds (each ≤ Cs⁶):
- H₁, H₂: ‖H_i‖ ≤ ξⁱ⁶ ≤ s⁶ via `norm_exp_sub_one_sub_sub_sub_sub_sub_le` + `real_exp_sixth_order_le_sextic`
- a·G₂, G₁·b: bounded by ξ·γ⁵ ≤ s⁶
- E₁E₂: ‖E_i‖ ≤ ξ³, so ‖E₁E₂‖ ≤ s⁶
- ½·a²·F₂, ½·F₁·b²: bounded by ½ξ²·γ⁴ ≤ ½s⁶
- ‖R‖ ≤ 6s⁵ (= -G₁ - G₂ - aF₂ - F₁b - E₁E₂ - ½E₁b² - ½a²E₂); ‖z·R+R·z‖ ≤ 12s⁶, half: 6s⁶
- ‖P²-T₂²-T₂T₃-T₃T₂‖ ≤ 15s⁶: split via (P-P₂-T₃)·P + T₂·(P-P₂-T₃) + T₃·(P-P₂); each ≤ 5s⁶

Total K_1 ≤ 20.

### Term 2: ‖I₂ - corr₂ - corr₂_5‖

Algebraic decomposition (extending hI₂_alg from quintic):
```
I₂ - corr₂ - corr₂_5 = ⅓·[z²(P-P₂-T₃) + z(P-P₂-T₃)z + (P-P₂-T₃)z² 
                       + z(P²-T₂²) + (PzP - T₂zT₂) + (P²-T₂²)z + P³]
```

Bounds:
- z²(P-P₂-T₃), etc.: ≤ s²·5s⁴ = 5s⁶ each → 15s⁶ for 3 terms
- z(P²-T₂²), (P²-T₂²)z: ‖P²-T₂²‖ ≤ 10s⁵, so each ≤ 10s⁶
- PzP - T₂zT₂ = T₂z(P-P₂) + (P-P₂)zT₂ + (P-P₂)z(P-P₂); ≤ 5s⁶+5s⁶+25s⁷ ≤ 12s⁶ for s ≤ 1
- P³: ≤ s⁶

Total ≤ 48s⁶, ÷3 ≤ 16s⁶. K_2 ≤ 17.

### Term 3: ‖¼·(y⁴-z⁴-y4_5)‖

```
y⁴-z⁴-y4_5 = (y³P-z³T₂) + (y²Pz-z²T₂z) + (yPz²-zT₂z²) + (Pz³-T₂z³)
```

Each pair telescopes via y³P - z³T₂ = (y³-z³)P + z³(P-T₂):
- (y³-z³)P: ‖y³-z³‖ ≤ 7s⁴, so ≤ 7s⁶
- z³(P-T₂): 5s⁶ (using ‖P-T₂‖ = ‖P-P₂‖ ≤ 5s³)

Total ≤ 31s⁶, ¼: ≤ 8s⁶. K_3 ≤ 8.

### Term 4: ‖⅕·(y⁵-z⁵)‖

```
y⁵-z⁵ = y⁴P + y³Pz + y²Pz² + yPz³ + Pz⁴
```

Bounds: 16s⁶ + 8s⁶ + 4s⁶ + 2s⁶ + s⁶ = 31s⁶. ⅕: 7s⁶. K_4 ≤ 7.

## Total bound

K_1 + K_2 + K_3 + K_4 ≤ 20 + 17 + 8 + 7 = 52.

With pieceA bound 64s⁶/(2-exp(s)):
LHS_case2 ≤ 64s⁶ + 52s⁶ ≤ 200·s⁶/(2-exp(s)) — easily within 30000.

## Proof size estimate

- Setup, hLHS_split, hLHS_3001': ~30 lines
- Case 1: ~10 lines
- Case 2 hdecomp + pieceA: ~30 lines
- Case 2 pieceB'' main:
  - Setup (D, E, F, G, H, P, z, etc.): ~50 lines
  - Norm bounds: ~80 lines
  - y⁵-z⁵ telescoping: ~80 lines
  - y⁴-z⁴-y4_5 telescoping: ~80 lines
  - I₁-corr₁-corr₁_5 bound: ~200 lines
  - I₂-corr₂-corr₂_5 bound: ~200 lines
  - Final assembly via sextic_pure_identity: ~50 lines

Total estimate: ~750-850 lines.

## Build/verify recipe

After writing:
```
cd /Users/jue/Documents/Claude/Projects/Lean-BCH
lake build BCH.Basic
```

Expected build time: 10-15 min (lots of `noncomm_ring` proofs).

## Implementation tactic

Given the size, write incrementally. Since repo invariant is 0 sorries, the WIP state must build. Approaches:
1. Write the entire proof in one local commit, test, iterate. Don't push until clean.
2. Define intermediate **helper lemmas** that each can compile independently, build up the main theorem from them.

Approach 2 is preferred for incremental progress visibility.

## Session 16 attempt (Task #17b) — findings

Attempted to discharge `norm_bch_sextic_remainder_small_s_le` by writing
the full proof inline. Got the SETUP, decomposition, and pieceA bound
working (~150 lines compiling cleanly). Hit obstacles in the pieceB''
bound:

### What works
- `pieceB_sextic_decomp` applies via direct `rw` (let-bindings propagate
  transparently to the goal).
- pieceA bound via `norm_logOnePlus_sub_sub_sub_sub_sub_le` + sharpening
  `(exp(s)-1)⁶ ≤ 2·s⁶` for `s ≤ 1/10` is straightforward.
- All exp remainder norm bounds (D, E, F, G, H of orders 1..5 in α, β)
  follow the quintic proof's pattern.
- `‖P‖ ≤ s²`, `‖P-T₂‖ ≤ 5·s³` (via inline algebraic identity), and
  `‖P-T₂-T₃‖ ≤ 5·s⁴` (via `norm_P_sub_T2_sub_T3_le`) all work.
- T₂, T₃ norm bounds via `norm_smul_le` chain.
- Combine pieceA + pieceB'' via `add_div` (NOT `div_add_div_same`!) +
  `div_le_div_of_nonneg_right`.

### What does NOT work cleanly
- `linear_combination (norm := module) hQPI + hSPI` in a goal where my
  T₃ uses T₃_SPI ordering but hQPI has T₃_QPI ordering. The underlying
  `module` calls `ring` which fails on the non-commutative residual.
  *Workaround*: use `pieceB_sextic_decomp` directly via `rw`, which
  separates T₃_QPI and T₃_SPI as let-bindings. Don't try to redo the
  decomposition with `set` variables.
- `linear_combination (norm := module) hqid` for the H1 + quartic_identity
  step. quartic_identity's LHS form is `½ • (2•(...) - z*P - P*z - P²)`
  while my goal has `y - z - ½(ab-ba) - ½y²` — these are equal by H1
  identity but `module` doesn't see this. *Workaround*: mirror the
  quintic proof's pattern (lines 3208-3219 of `Basic.lean`):
  - Set `Q`, `W_H1` explicitly.
  - Prove `hH1 : y - z - ½(ab-ba) - ½y² = ½ • W_H1` via ×2 scalar
    clearing + `noncomm_ring`.
  - Apply `quartic_identity 𝕂 (exp a) (exp b) a b` directly.

### Per-piece bound strategy (next session)

After `rw [pieceB_sextic_decomp 𝕂 a b]`, the goal becomes
`‖S₁ + S₂ - S₃ + S₄‖ ≤ 52·s⁶` with let-bindings T₂, T₃_QPI, T₃_SPI,
T₄, W5, y3_5, y4_5, corr₁ (= explicit form using T₃_QPI), corr₂, etc.

**S₃ (easiest)** — `‖¼ • (y⁴ - z⁴ - y4_5)‖ ≤ 8·s⁶`:
```lean
have h_zPeq : z = y - P := by rw [hP_def]; abel
have hS3_inner : ‖y^4 - z^4 - y4_5‖ ≤ 31 * s^6 := by
  rw [h_zPeq]  -- match norm_y4_sub_z4_sub_y4_5_le's (y-P) form
  exact norm_y4_sub_z4_sub_y4_5_le y P T₂ hs_nn hy_le2 hz_le hP_le_s2 hPmT₂
have h4eq : ‖(4:𝕂)⁻¹‖ = (4:ℝ)⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
-- ‖¼ • _‖ ≤ ¼ * 31 * s⁶ = 7.75 ≤ 8
```

**S₄ (next easiest)** — `‖⅕ • (y⁵ - z⁵)‖ ≤ 7·s⁶`:
Similar pattern using `norm_pow5_sub_zpow5_le`. ⅕ * 31 = 6.2 ≤ 7.

**S₂** — `‖⅓(y³-z³) - corr₂ - corr₂_5‖ ≤ 17·s⁶`:
The inner expression equals `⅓ • [(y³-z³) - (z²T₂+zT₂z+T₂z²) - y3_5]`
by smul distributivity. By `I2_residual_decomp_eq` with `y = z + P`,
the inner sum equals 7 deg-6+ terms bounded by `norm_I2_residual_inner_le`
(≤ 50·s⁶). With ⅓ scaling: ⅓·50 = 16.67 ≤ 17.

```lean
have hS2_eq : ⅓•(y³-z³) - ⅓•(z²T₂+zT₂z+T₂z²) - ⅓•y3_5 =
              ⅓ • (y³-z³ - (z²T₂+zT₂z+T₂z²) - y3_5) := by
  rw [smul_sub, smul_sub]; abel  -- uses smul distribution

have hyzP : y = z + P := by rw [hP_def]; abel
have hS2_inner_eq : y^3 - z^3 - (z²T₂+zT₂z+T₂z²) - y3_5 =
    z²(P-T₂-T₃) + ... + P³ := by
  rw [hyzP]; exact I2_residual_decomp_eq z P T₂ T₃
```

But wait: pieceB_sextic_decomp's y3_5 uses T₃_SPI, and I2_residual_decomp_eq
also uses T₃_SPI. They match.

**S₁ (hardest)** — `‖I₁_form - corr₁_QPI - corr₁_5‖ ≤ 20·s⁶`:
1. Convert I₁_form to quartic_id form via H1 + quartic_identity.
2. Convert corr₁_QPI to corr₁_SPI form via abel (T₃_QPI = T₃_SPI as values).
3. Apply I1_residual_decomp_eq.
4. Apply norm_I1_residual_RHS_le.

Step 1 mirrors quintic proof's hH1 + hI₁_quartic. ~50 lines.
Step 2 is a single abel rewrite on hQPI's T₃_QPI sum. ~5 lines.
Step 3 is a `rw` + helper application. ~10 lines.
Step 4 supplies all the per-component bounds. ~80 lines (mostly bound
each H_i, G_i, F_i, E_i, etc. by s⁶/s⁵/s⁴; ‖R‖ via R_eq_neg_deg5_residual
+ norm_R_residual_sum_le; ‖z*R+R*z‖ ≤ 12·s⁶; ‖T22_resid‖ via
norm_T22_sub_P2_etc_le ≤ 15·s⁶).

Total estimated S₁ proof: ~150 lines.

### Combine pieceA + pieceB''

```lean
calc _ ≤ ‖pieceA‖ + ‖pieceB''‖ := norm_add_le _ _
  _ ≤ (Real.exp s - 1)^6/(2-exp s) + 52*s^6 := by linarith [hpieceA, hpieceB]
  _ ≤ (Real.exp s - 1)^6/(2-exp s) + 52*s^6/(2-exp s) := by
      gcongr; rw [le_div_iff₀ hdenom]; nlinarith [pow_nonneg hs_nn 6]
  _ = ((exp s - 1)^6 + 52*s^6) / (2-exp s) := (add_div _ _ _).symm
  _ ≤ 100*s^6 / (2-exp s) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      linarith [hexp6, pow_nonneg hs_nn 6]
```

### Total proof size estimate
- SETUP: ~150 lines (DONE in session 16 attempt).
- pieceA bound: ~15 lines (DONE).
- S₁ bound: ~150 lines.
- S₂ bound: ~30 lines.
- S₃ bound: ~15 lines.
- S₄ bound: ~15 lines.
- Triangle inequality combine: ~20 lines.
- Final pieceA+pieceB'' combine: ~15 lines (DONE).

Total: ~410 lines (more than the original 250-300 estimate due to S₁
complexity). Use `set_option maxHeartbeats 4000000000` for the whole
theorem.
