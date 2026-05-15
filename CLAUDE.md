# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status (session 35, 2026-05-14)

Branch: `main`. Repository is **0 sorries**, **3 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`,
`norm_bch_octic_remainder_small_s_axiom` (octic stepping stone, awaiting discharge).

**Session 35 part 7 (2026-05-15, deg-8 P²-residual cluster bound, 1 commit)**:

Commit `c5537bd` (+114 lines): `BCH.norm_P2_etc_nonic_le` — deg-9 analog of
`norm_P2_etc_octic_le` (session 29) at one degree higher.

Bounds the deg-8 residual of P² after subtracting all deg-4..7 contributions:
`‖P² − T₂² − T₂T₃ − T₃T₂ − T₂T₄ − T₃² − T₄T₂ − T₂T₅ − T₃T₄ − T₄T₃ − T₅T₂‖
≤ 19·s⁸` for `s ≤ 1/10`. Decomposes via `P = T₂ + T₃ + T₄ + T₅ + D₆` into
15 deg-8+ terms (6 T·T deg-8+ + 8 T·D₆ cross + D₆²). Per-degree sums:
17 + 1.6 + 0.15 + 0.014 + ε ≈ 18.76·s⁸ ≤ 19·s⁸.

Needed `maxHeartbeats 4000000` for whnf on the 11-term LHS. Forward-looking
infrastructure for the future I2-nonic chain in the deg-9-parent T2-F7e-octic
discharge (analog of how the octic version provided the K_P2' = 16 input
for `norm_I2_octic_residual_RHS_le`).

**Session 35 part 6 (2026-05-15, y7 nonic decomp + norm bound, 1 commit)**:

Commit `fbec7a0` (+216 lines): `BCH.y7_sub_z7_sub_y7_8_decomp` (13-term
algebraic identity) + `BCH.norm_y7_sub_z7_sub_y7_8_le` (`‖y⁷ - z⁷ - y7_8‖
≤ 155·s⁹`). Deg-9 analog of `y6_sub_z6_sub_y6_7_decomp` /
`norm_y6_sub_z6_sub_y6_7_le` (session 28) at one degree higher.

`y7_8 = z⁶T₂ + z⁵T₂z + z⁴T₂z² + z³T₂z³ + z²T₂z⁴ + zT₂z⁵ + T₂z⁶` (7 perms
of (1,1,1,1,1,1,2) — single T₂ in 7 positions among 6 z's). The 13 RHS
terms split as 5 (yⁿ-zⁿ)·P·zᵏ telescoping pieces (n=2..6) + 7 zⁿ·(P-T₂)·zᵏ
absorption pieces (n=0..6) + P·P·z⁵ (level-1 telescoping). Per-term:
63+5+31+5+15+5+7+5+3+5+1+5+5 = 155 (units of s⁹).

Both lemmas need `set_option maxHeartbeats 4000000` (default 200K times out
on the 13-term `noncomm_ring` and on `whnf` of the giant statement).
Forward-looking infrastructure for the future S₆-nonic piece in the
deg-9-parent T2-F7e-octic discharge.

**Session 35 part 5 (2026-05-14, deg-9 pow8 telescoping bound, 1 commit)**:

Commit `eeb72c8` (+121 lines): `BCH.pow8_sub_zpow8_telescope` (8-fold
non-commutative ring identity) + `BCH.norm_pow8_sub_zpow8_le`
(`‖y⁸ - z⁸‖ ≤ 255·s⁹` for `‖y‖ ≤ 2s, ‖z‖ ≤ s, ‖P‖ ≤ s²`). Per-term bounds:
`(2s)^(7-k)·s²·s^k` for k=0..7 sums to 128+64+32+16+8+4+2+1 = 255 (units
of s⁹).

Deg-9 analog of `pow7_sub_zpow7_telescope` + `norm_pow7_sub_zpow7_le`
(session 28) at one degree higher. Forward-looking infrastructure for the
deg-9-parent T2-F7e-octic discharge — will feed the future S₆-nonic piece
(analog of the octic S₆ using `norm_pow7_sub_zpow7_le` ≤ 127·s⁸).

**Session 35 part 4 (2026-05-14, ‖T₈‖ ≤ s⁸ helper, 1 commit)**:

Commit `b86f4c1` (+155 lines): `BCH.norm_T8_le` — standalone helper bounding
the deg-8 contribution of `exp(a)·exp(b)-1`:

  T₈ = (1/40320)·a⁸ + (1/5040)·a⁷b + (1/1440)·a⁶b² + (1/720)·a⁵b³ +
       (1/576)·a⁴b⁴ + (1/720)·a³b⁵ + (1/1440)·a²b⁶ + (1/5040)·ab⁷ +
       (1/40320)·b⁸.

Sum of |coefficients|·LCM = 256/40320 = 2/315 ≈ 0.00635, so `‖T₈‖ ≤ s⁸`.
Mirrors `norm_T7_le` (session 31) at one degree higher with 9 instead of 8
monomials. Forward-looking infrastructure for the deg-9-parent T2-F7e-octic
discharge, where ‖T₈‖ ≤ s⁸ is needed alongside the ‖T_k‖ ≤ s^k chain
(k=2..7) already in place.

**Session 35 part 3 (2026-05-14, deg-8 R+T5+T6+T7 norm sum bound, 1 commit)**:

Commit `34873dc` (+61 lines): `BCH.norm_R_plus_T5_plus_T6_plus_T7_residual_sum_le`
— deg-8 analog of `norm_R_plus_T5_plus_T6_residual_sum_le` (session 29) at one
degree higher. Bounds the 9-term residual sum from session 35 part 1's
`R_plus_T5_plus_T6_plus_T7_eq_neg_deg8_residual` identity by `7·s⁸` given
precomputed per-term bounds (each ≤ s⁸):

  J_a + J_b + a·I_b + I_a·b + F₁·F₂ + ⅙·G₁·b³ + ⅙·a³·G₂ + ½·H₁·b² + ½·a²·H₂.

Per-term: 4·s⁸ (outer) + s⁸ (F₁·F₂, deg-8 leading inherently — no `s ≤ 1`
folding needed) + 2·(s⁸/6) (smul'd by 1/6) + 2·(s⁸/2) (smul'd by 1/2) =
19/3·s⁸ ≈ 6.34·s⁸ ≤ 7·s⁸. Proof: 9-step triangle inequality + linarith.

Forward-looking infrastructure for the future I1-nonic chain (deg-9-parent
T2-F7e-octic discharge), alongside session 35 part 2's
`norm_combined_tricky_nonic_le`.

**Session 35 part 2 (2026-05-14, nonic combined tricky bound, 1 commit)**:

Commit `b3bdb2b` (+266 lines): `BCH.norm_combined_tricky_nonic_le` — deg-9
analog of `norm_combined_tricky_octic_le` (session 31) at one degree higher.
Uses session 35's new deg-8 cancellation identity bound and session 34's
deg-7 P-tail bound as inputs.

Bounds the combined cluster
`z·R + R·z + (T₂²-P²+T₂T₃+T₃T₂) + (z·T₅+T₂T₄+T₃²+T₄T₂+T₅z) +
 (z·T₆+T₂T₅+T₃T₄+T₄T₃+T₅T₂+T₆z) + (z·T₇+T₂T₆+T₃T₅+T₄²+T₅T₃+T₆T₂+T₇z)`
by `35·s⁹` for `s ≤ 1/10`.

Algebraic identity (`noncomm_ring`): combined = `z·(R+T₅+T₆+T₇) +
(R+T₅+T₆+T₇)·z − P²_deg≥9` where `P²_deg≥9` unfolds via
`D₇ := P-T₂-T₃-T₄-T₅-T₆` into 21 deg-9+ terms (10 T·T products with
i+j ≥ 9, 10 T·D₇ products, D₇²). Proof: 20-step norm_add_le telescoping +
`nlinarith` with `maxHeartbeats 16000000` (4M times out due to large
context: 21 cluster bounds + 20 norm_add_le + 5 s^k folding facts).

Per-degree contributions: deg 9 (18·s⁹) + dominated higher degrees
(≤ 1.88·s⁹) + z·R cluster (14·s⁹) ≈ 33.88·s⁹ ≤ 35·s⁹.

**Session 35 part 1 (2026-05-14, deg-8 P-tail chain, 1 commit)**:

Forward-looking infrastructure for the eventual deg-9-parent T2-F7e-octic
discharge (which will eliminate `symmetric_bch_septic_sub_poly_axiom`).
Commit `1d5056e` added 3 lemmas extending the session-34 chain one degree
higher:

- `BCH.R_plus_T5_plus_T6_plus_T7_eq_neg_deg8_residual`: deg-8 cancellation
  identity. Promotes each term in the deg-7 residual by one tail level
  (F→G, G→H, H→I, I→J); subtracted monomials sum to exactly T₇. RHS =
  `−(J_a + J_b + a·I_b + I_a·b + F₁·F₂ + ⅙·G₁·b³ + ⅙·a³·G₂ + ½·H₁·b² +
  ½·a²·H₂)`. Proof: 1-line `linear_combination` from session-29 deg-7
  identity + match_scalars/ring normalization.
- `BCH.P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_sub_T7_decomp_eq`: deg-8 P-tail
  decomp (`P − T₂ − ... − T₇ = 9 deg-8+ terms`). Proof:
  `linear_combination -hR` + noncomm_ring normalization.
- `BCH.norm_P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_sub_T7_le`: norm bound
  `≤ 7·s⁸` for `s < 3/4`. Per-term: 5·s⁸ (J_a+J_b+a·I_b+I_a·b+F₁·F₂) +
  2·(s⁸/6) (⅙·G₁·b³+⅙·a³·G₂) + 2·(s⁸/2) (½·H₁·b²+½·a²·H₂) = 19/3·s⁸ ≈
  6.34·s⁸ ≤ 7·s⁸. Uses session-29 deg-8 noncomm exp tail +
  `real_exp_eighth_order_le_octic`. No `s ≤ 1` folding needed (all
  terms inherently deg-8+).

Deg-8 analog of session 34's deg-7 P-tail bound. Same per-term arithmetic
at one degree higher; same outer triangle inequality + linarith pattern.

**Session 34 (2026-05-13, deg-7 P-tail bound, 1 commit)**:

Infrastructure for the future deg-9 parent (T2-F7e-octic) discharge:

- `BCH.P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_decomp_eq` + `BCH.norm_P_sub_T2_sub_T3_sub_T4_sub_T5_sub_T6_le`:
  the deg-7 P-tail bound `‖P − T₂ − T₃ − T₄ − T₅ − T₆‖ ≤ 7·s⁷` for
  `P = exp(a)·exp(b) − 1 − (a+b)`, `s < 3/4`, `s ≤ 1`. Algebraic identity:
  `P − T₂ − ... − T₆ = I_a + I_b + a·H₂ + H₁·b + F₁·F₂ + ⅙·F₁·b³ +
   ⅙·a³·F₂ + ½·G₁·b² + ½·a²·G₂` (9 deg-7+ terms). Decomp proof: 4-line
  `linear_combination ... -hR` from `R_plus_T5_plus_T6_eq_neg_deg7_residual`
  + the auxiliary fact `P − T₂ = E₁ + E₂ + Q`. Norm bound: per-term
  bounds (each ≤ s⁷, F₁·F₂ ≤ s⁸ folded via `s ≤ 1`) summed via 8-step
  triangle inequality; total ≤ (4 + 1 + 4/3)·s⁷ ≈ 6.34·s⁷ ≤ 7·s⁷.
  Deg-10 analog of the existing `norm_P_sub_T2_sub_T3_sub_T4_sub_T5_le`
  (≤ 6·s⁶) at one degree higher.

**Session 33 (2026-05-13, octic pieceA bound, 1 commit)**:

First ingredient for the eventual small-s octic discharge:

- `BCH.norm_bch_octic_pieceA_le` (commit `63a82dc`): the deg-8 log-tail
  bound `‖logOnePlus y − y + y²/2 − … − y⁷/7‖ ≤ 3·s⁸/(2 − exp s)` for
  `y := exp(a)·exp(b) − 1`, `s := ‖a‖+‖b‖`, `s < 1/10`. Combines
  `norm_logOnePlus_sub_sub_sub_sub_sub_sub_sub_le` (LogSeries.lean, deg-7
  truncation tail) with `real_exp_sub_one_pow8_le_small` (`(exp s − 1)⁸ ≤
  3·s⁸`). Structure mirrors the septic pieceA inline computation in
  `norm_bch_septic_remainder_small_s_le` at one degree higher. The
  constant 3 (not 2 as for septic) reflects `(1+1/10)⁸ ≈ 2.14 > 2`.

Per the discharge arithmetic in the axiom's docstring: pieceA contributes
3·s⁸/(2−exp s); pieceB''' will contribute 217·s⁸ from the 6 sub-pieces
(S₁' ≤ 25·s⁸ + S₂' ≤ 57·s⁸ + S₃' ≤ 72·s⁸ + S₄' ≤ 29·s⁸ + S₅' ≤ 15·s⁸ +
S₆ ≤ 19·s⁸). Total ≤ 220·s⁸/(2−exp s), comfortably within the axiom's
1000·s⁸/(2−exp s) headroom.

**Remaining for the small-s discharge**: the pieceB''' assembly (~700
lines) using `pieceB_octic_decomp` + the 6 sub-piece bounds already in
place from sessions 28–31. Estimated 2–3 sessions for the final assembly,
then 2–3 more for the parent T2-F7e-octic discharge.

## Status (session 32, 2026-05-13)

Branch: `main`. Repository is **0 sorries**, **3 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`,
and the newly-added stepping stone `norm_bch_octic_remainder_small_s_axiom`.

**Session 32 (2026-05-13, octic remainder public theorem via stepping stone, 1 commit)**:

With all per-piece octic infrastructure in place from sessions 28-31, the
public `norm_bch_octic_remainder_le` theorem is now in place, gated on a
stepping-stone axiom for the small-s case (analog of session 18's pattern
for the septic where the small-s axiom was introduced then discharged
session 19).

- `norm_bch_octic_remainder_small_s_axiom`: stepping-stone bounding
  `‖LHS_octic‖ ≤ 1000·s⁸/(2-exp(s))` for s < 1/10. To be discharged
  following the session-19 template (~770 lines): pieceA (deg-8 log tail)
  + pieceB'''' (via `pieceB_octic_decomp` + 6 sub-piece bounds).
- `BCH.norm_bch_octic_remainder_le`: PUBLIC theorem
  `‖bch - ... - bch_septic_term‖ ≤ 10000110·s⁸/(2-exp(s))` for s < log 2.
  Case split: large-s (proved via `norm_bch_octic_remainder_large_s_le`)
  vs. small-s (uses the new stepping-stone axiom). Deg-8 analog of
  `norm_bch_septic_remainder_le`.

Axiom count: 2 → 3. Will return to 2 once the small-s axiom is discharged
over the next 2-3 sessions, and to the original 2 once the deg-9-parent
T2-F7e-octic discharge eliminates `symmetric_bch_septic_sub_poly_axiom`.

## Status (session 31, 2026-05-13)

Branch: `main`. Repository was **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`,
`norm_septic_match_residual_le_axiom`.

**Session 31 (2026-05-13, octic small-s S₃' + S₄' inner bounds, 3 commits)**:

Both remaining "inner piece" bounds for the octic small-s discharge are
now in place. The roadmap noted in session 30 — y4 octic via structural
extension, y5 octic via CAS or analogy — is COMPLETE for both:

1. **y4 octic** (commit `ab38b23`, 407 lines):
   * `y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_decomp`: 24-term deg-8+
     decomposition. Each of the 20 `y4_7` items is exactly the deg-7
     leading of one of the 16 terms in the existing septic decomposition.
     Absorption pattern verified by hand (no CAS needed).
   * `norm_y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_le`: bound `≤ 285·s⁸`
     for `s ≤ 1`. Uses `nlinarith` with `s ≤ 1` to coalesce a single
     `s⁹` term (B7-3 = `(P²-T₂²)·z·(P-T₂)`).

2. **y5 octic decomp** (commit `d4089c0`, 65 lines):
   * `y5_sub_z5_sub_y5_6_sub_y5_7_decomp`: 18-term decomposition. Each of
     the 15 `y5_7` items is the deg-7 leading of one of the 9 terms in
     the y5 septic decomposition. The "(y^k-z^k)·...·P·..." terms split
     into `(y^k-z^k-yk_l)·...·P·...` (deg-8+ compound) + perms of
     `y(k-1)_l·(P-T₂)·...`. Identity proved by `noncomm_ring`.

3. **y5 octic norm bound + 2 helpers** (commit `7a18dde`, 385 lines):
   * `norm_y2_sub_z2_sub_y2_3_le`: `≤ 11·s⁴` via identity
     `y² - z² - y2_3 = z(P-T₂) + (P-T₂)z + P²`.
   * `norm_y3_sub_z3_sub_y3_4_le`: `≤ 19·s⁵` (for `s ≤ 1`) via
     `y³ - z³ - y3_4 = (P-T₂)·z² + z²·(P-T₂) + z·(P-T₂)·z + P·z·P +
      P²·z + P³ + z·P²`.
   * `norm_y5_sub_z5_sub_y5_6_sub_y5_7_le`: bound `≤ 141·s⁸` for `s ≤ 1`.
     The 18 terms split as: 25·s⁸ (5 P-T₂-T₃ middle) + 51·s⁸ (Group B:
     compound + 4 perms) + 34·s⁸ (Group C) + 21·s⁸ (Group D) + 10·s⁸
     (Group E = `(P²-T₂²)·z³`).

**pieceA infrastructure (this session, 3 commits)**:
- `BCH.norm_logOnePlus_sub_sub_sub_sub_sub_sub_sub_le` (LogSeries.lean,
  commit `f4ec6ed`): the deg-8 log tail bound
  `‖log(1+x) - x + x²/2 - ... - x⁷/7‖ ≤ ‖x‖⁸/(1-‖x‖)` for `‖x‖ < 1`.
  Analog of the deg-7 tail used by the septic pieceA, at one degree
  higher. Plus 3 helpers (`summable_logSeriesTerm_shift7`,
  `logSeriesTerm_six`, `logOnePlus_sub_sub_sub_sub_sub_sub_sub_eq_tsum`).
- `BCH.real_exp_sub_one_pow8_le_small` (Basic.lean, commit `ff04696`):
  `(Real.exp s - 1)⁸ ≤ 3·s⁸` for `s ≤ 1/10`. Constant is 3 (not 2)
  because `(1+1/10)⁸ ≈ 2.14 > 2`.
- `BCH.norm_T7_le` (commit `f895af1`): `‖T₇‖ ≤ s⁷` standalone helper
  (T₇ = deg-7 contribution of `exp(a)·exp(b)-1`, 8 monomial terms,
  sum of |coefs|/5040 = 128/5040 ≈ 0.0254). Mirrors `norm_T6_le`.

**Remaining for octic small-s discharge** (pending):
- Final `norm_bch_octic_remainder_small_s_le` (analog of session-19
  step 22 septic discharge / `norm_bch_septic_remainder_small_s_le` at
  ~770 lines). The 6 RHS pieces of `pieceB_octic_decomp` now have all
  their inner bounds available: I₁ octic (via `norm_I1_octic_residual_RHS_le`
  + `norm_combined_tricky_octic_le`), I₂ octic (via
  `norm_I2_octic_residual_RHS_le` + 4 parametric inputs), S₃' (y4 octic
  ≤ 285·s⁸, this session), S₄' (y5 octic ≤ 141·s⁸, this session),
  S₅ (`norm_y6_sub_z6_sub_y6_7_le` ≤ 87·s⁸), S₆ (`norm_pow7_sub_zpow7_le`
  ≤ 127·s⁸). Plus pieceA bound via the deg-8 log tail (just added).

Estimated: 2-3 sessions for the final small-s assembly, then 2-3 more
for the parent T2-F7e-octic discharge.

## Status (session 29, 2026-05-13)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
* `symmetric_bch_septic_sub_poly_axiom` (Stage 2 stepping-stone,
  introduced session 25; mirrors `symmetric_bch_quintic_sub_poly_axiom`).
* `norm_septic_match_residual_le_axiom` (Stage 3 stepping-stone,
  introduced session 26; bounds the σ⁹ residual of the deg-7 matching
  identity).

**Session 29 (2026-05-13, octic small-s infrastructure, 13 commits)**:

Substantial progress on the octic small-s discharge (foundation for the
deg-9 analog of T2-F7e, eventually replacing
`symmetric_bch_septic_sub_poly_axiom`):

1. **`pieceB_octic_decomp`** (commit `d1204b7`, the MAJOR commit): the
   central algebraic decomposition for the small-s octic case. Combines
   QPI + SPI + Septic + Octic pure identities via
   `linear_combination (norm := module)` with 4 BILLION heartbeats. ~190
   lines, 35 min build wall.

2. **Full I2 octic chain** (4 commits):
   * `I2_octic_residual_decomp_eq` (pure ring identity, `noncomm_ring`).
   * `norm_I2_octic_residual_RHS_le` (parameterized wrapper).
   * 4 input bounds (K_PmT5=6, K_P2'=16, K_PzP'=16, K_P3'=105) via
     `norm_P_sub_T2_sub_T3_sub_T4_sub_T5_le`, `norm_P2_etc_octic_le`,
     `norm_PzP_etc_octic_le`, `norm_P3_etc_octic_le`.
   * Combined: ‖I2 octic RHS‖ ≤ (3·6 + 2·16 + 16 + 105)·s⁸ = 171·s⁸.

3. **Telescoping & cancellation** (2 commits):
   * `y6_sub_z6_sub_y6_7_decomp` + bound (≤ 87·s⁸).
   * `pow7_sub_zpow7_telescope` + bound (session 28; ≤ 127·s⁸).

4. **Deg-8 exp tail helpers** (commit `7864cdf`):
   * `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_sub_le` (noncomm deg-8 tail).
   * `real_exp_eighth_order_le_octic` (real ≤ x⁸ bound).
   Foundation for J_a := I_a - a⁷/5040 (next exp-tail level), needed for
   the future I1 octic chain.

5. **R+T₅+T₆ deg-7 cancellation infrastructure** (2 commits):
   * `R_plus_T5_plus_T6_eq_neg_deg7_residual` (commit `da82482`): the deg-7
     cancellation algebraic identity extending `R_plus_T5_eq_neg_deg6_residual`.
     RHS = -(I_a + I_b + a·H₂ + H₁·b + F₁·F₂ + ⅙·F₁·b³ + ⅙·a³·F₂ +
     ½·G₁·b² + ½·a²·G₂), 9 deg-7+ terms. Proof: 1-line `linear_combination`
     from septic version + simp + `match_scalars <;> ring`. ~75 lines.
   * `norm_R_plus_T5_plus_T6_residual_sum_le` (commit `0f968b8`): the norm
     bound `≤ 7·s⁷` on the 9-term residual sum, given precomputed
     component bounds. ~65 lines.

**Remaining for octic small-s discharge** (pending):
- `norm_y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_le` (S₃' inner bound,
  deg-8 analog of `norm_y4_sub_z4_sub_y4_5_sub_y4_6_le`, ~400 lines).
- `norm_y5_sub_z5_sub_y5_6_sub_y5_7_le` (S₄' inner bound,
  deg-8 analog of `norm_y5_sub_z5_sub_y5_6_le`, ~250 lines).
- Final `norm_bch_octic_remainder_small_s_le` (the public theorem,
  analog of session-19 step 22 septic discharge at ~770 lines).

**Note (session 30 attempted):** sympy expansion of
`y^5 - z^5 - y5_6 - y5_7` after `z=y-P` yields ~370 distinct
non-commutative monomials. The y4 octic decomp (16 terms) was derived
via careful structural analysis — for y5 the structural pattern is
non-trivial. Next session should either:
(a) write a CAS pipeline (similar to existing `scripts/gen_*.py`) that
    factors the expansion into compact building blocks
    `(P-T₂-T₃), (P²-T₂²), (y^k-z^k), z^a·X·z^b`, OR
(b) extend the y4 octic structure by analogy and iterate via
    `noncomm_ring` verification.

**Session 30 (in progress, octic I1 infrastructure + T₆ helper)** added
4 lemmas (all proved, ~500 lines total added):
- `I1_octic_residual_decomp_eq`: extends `I1_septic_residual_decomp_eq` by
  subtracting `corr₁_7 = ½·W7`, expressing
  `(I₁ in quartic_id form) - corr₁ - corr₁_5 - corr₁_6 - corr₁_7` as
  13 deg-8+ terms. Promotions: I_a→J_a, I_b→J_b, a·H₂→a·I_b, H₁·b→I_a·b,
  ½·a²·G₂→½·a²·H₂, ½·G₁·b²→½·H₁·b², ⅙·a³·F₂→⅙·a³·G₂, ⅙·F₁·b³→⅙·G₁·b³,
  F₁·F₂ unchanged, plus new cluster `½·(z·T₆+T₂·T₅+T₃·T₄+T₄·T₃+T₅·T₂+T₆·z)`.
  Proof: `match_scalars <;> ring`, 16M heartbeats.
- `norm_I1_octic_residual_RHS_le`: parameterized wrapper, `(7 + C/2)·s⁸`
  bound from 9 "easy" inputs (each ≤ s⁸) + combined cluster bound C·s⁸.
- `norm_combined_tricky_octic_le`: combined cluster bound `≤ 35·s⁸`
  for `(z·R+R·z) + T22 + T_extra + T_extra2` via the R+T₅+T₆ identity
  (`R_plus_T5_plus_T6_eq_neg_deg7_residual`) + 15-term P²_deg≥8
  decomposition (with D₆ := P-T₂-T₃-T₄-T₅).
- `norm_T6_le`: `‖T₆‖ ≤ s⁶` standalone helper (sum of |coef| = 64/720 = 4/45).

Estimated remaining: 3-4 sessions for the final small-s assembly
(`norm_bch_octic_remainder_small_s_le`), then 2-3 more for the parent
T2-F7e-octic discharge (analog of session 22).

**Session 28 (2026-05-12, stepping stone 1 foundation, 4 commits)**:

Substantial progress on the `bch_octic_term` infrastructure for stepping
stone 1 discharge:

1. `BCH.norm_bch_septic_term_diff_le` (~1700 lines via Finset.sum approach,
   CAS-generated). The deg-9 analog of `norm_bch_sextic_term_diff_le`:
   `‖Z₇(z, y) − Z₇(x, y)‖ ≤ 7·M⁶·‖z − x‖` for `M = ‖z‖+‖x‖+‖y‖`.
   Foundation for stepping stone 1 (`symmetric_bch_septic_sub_poly_axiom`):
   the deg-7 BCH coefficient is Lipschitz in its first arg, enabling
   O(s⁸·‖W‖) bounds for `‖C₇(z, y) − C₇(a'+b, y)‖` when z = (a'+b)+W.

2. `BCH.bch_octic_term`: deg-8 BCH coefficient as an explicit 124-term
   polynomial (out of 256 = 2⁸ possible 8-letter words). LCM 120960,
   max |coef| = 432, Σ|coef|/LCM = 199/4032 ≈ 0.0494. CAS-derived in
   `scripts/compute_bch_octic_term.py`. Plus homogeneity theorem
   `bch_octic_term_smul`: `Z₈(c•a, c•b) = c⁸ • Z₈(a, b)`.

3. `BCH.norm_bch_octic_term_le`: `‖Z₈(a, b)‖ ≤ (‖a‖+‖b‖)⁸`. ~820 lines
   via Finset.sum approach mirroring `norm_bch_septic_term_le` (session 27).
   Uniform per-i bound `432/120960`; sum `124·432/120960 = 31/70 ≤ 1`.
   CAS-generated in `scripts/gen_bch_octic_norm_bound.py`.

4. `BCH.bch_octic_term_apply_smul_smul`: vanishing on (αV, βV) inputs.
   ~50 lines, mirrors `bch_septic_term_apply_smul_smul`. Foundation for
   the future `nonic_pure_identity` (deg-8 cancellation in deg-9-precision
   small-s discharge).

Net axiom count unchanged (still 2 scoped private axioms). Build time:
~11 min wall for Basic.lean per major commit (124-case matches at 32M+
heartbeats, plus 4M for the ring proof in the vanishing theorem).

**Stepping stone 1 (`symmetric_bch_septic_sub_poly_axiom`) infrastructure
quartet now COMPLETE for both `bch_septic_term` and `bch_octic_term`**:
* `bch_septic_term`: def + homogeneity + norm bound + vanishing + Lipschitz ✓ (s27-28).
* `bch_octic_term`: def + homogeneity + norm bound + vanishing + Lipschitz ✓ (s28).

9 code commits this session:
* `bch_septic_term` Lipschitz bound (commit 14d75bc, ~1700 lines)
* `bch_octic_term` def + homogeneity (commit 325b632, ~150 lines)
* `bch_octic_term` norm bound ‖Z₈‖ ≤ s⁸ (commit 3c96d30, ~820 lines)
* `bch_octic_term` vanishing on (αV, βV) (commit 2696fcf, ~50 lines)
* `bch_octic_term` Lipschitz bound (commit ad299db, ~1700 lines)
* `norm_bch_octic_remainder_large_s_le` private helper (commit 6b86a3a, ~60 lines)
* `octic_pure_identity` deg-7 cancellation identity (commit 2af11b6, ~200 lines)
* `nonic_pure_identity` deg-8 cancellation identity (commit db47a44, ~344 lines)
* `pow7_sub_zpow7_telescope` + `norm_pow7_sub_zpow7_le` (commit c6d129c, ~105 lines)

Total session 28: ~5100 lines added, 12 commits (9 code + 3 doc + extras), 0 axioms changed.

Remaining for stepping stone 1: small-s case of octic remainder bound
(uses `octic_pure_identity` + `pieceB_octic_decomp` analog) → full
`norm_bch_octic_remainder_le`, inner/outer nonic remainder bounds
(deg-8 analog of Phase A), per-piece bounds + extended hdecomp + parent
theorem. Estimated: ~2000-3500 lines, multi-session.

**Major session-26 milestone: `suzuki5_log_product_septic_at_suzukiP_axiom`
(the Lean-Trotter interface axiom 3 / headline axiom) is now DISCHARGED!**
It is now a proved theorem `BCH.suzuki5_log_product_septic_at_suzukiP`
that depends only on the two stepping-stones above plus Lean's foundational
axioms. The 6-stage septic-axiom discharge roadmap is complete.

**All 6 stages of the septic-axiom roadmap are now complete**:
* Stage 1: `suzuki5_R7` + norm bound (session 24).
* Stage 2.0: deg-7 algebraic identity infrastructure (session 24).
* Stage 2.1: B1.d-septic + B2.1-septic per-block bounds (session 25).
* Stage 2 main: combined σ⁹ bound (session 25).
* Stage 3.0–3.3: `symmetric_bch_septic_poly` infrastructure (session 24).
* Stage 3 main: algebraic backbone (session 26, stepping-stone axiom).
* Stage 5: σ⁹ → |τ|⁹·polynomial conversion (session 26, this commit).
* Stage 6 step 1: |τ|⁹ → |τ|⁸ assembly via small-τ regime (session 26).
* Stage 6 step 2: triangle inequality with R₅, R₇ bounds → headline
  axiom replaced with theorem (session 26).


---

**Earlier sessions (16–27):** archived in `claude/session_history.md`.

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
