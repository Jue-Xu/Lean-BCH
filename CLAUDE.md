# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status: **All BCH files sorry-free (2026-04-25, updated session 12).** Basic, Palindromic, LogSeries: see prior status. Branch `trotter-5factor-palindromic`: ChildsBasis (axiom-1 infrastructure + BCHPrefactors struct), Suzuki5Quintic (βᵢ(p) polynomials + R₅ Childs-basis def + unit-coefficient norm bound + **headline τ⁵-identification theorem fully proved (no axiom)** + bridge corollary + **tight bridge at Suzuki p, fully proved**), **SymmetricQuintic (τ⁵ coefficient infrastructure + B1.c quintic Taylor bridge via Tier-2 axiom)**, **Palindromic B1.d (per-block quintic bound derived from B1.c) + B2.2.a/b/c/d/e algebraic decomposition + B2.2.e Childs-basis projection identity + B2.5 T₂ bound (zero new axioms)**. Infrastructure is ready for Lean-Trotter's axioms 1 AND 2:

- Axiom 1 (`bch_w4Deriv_quintic_level2`): wired up via `suzuki5_log_product_quintic_of_IsSuzukiCubic`; **P1 axiom discharged session 12** (was `suzuki5_R5_identification_axiom`). The headline theorem `norm_suzuki5_bch_sub_smul_sub_R5_le` is now a fully proved theorem, not an axiom.
- Axiom 2 (`bch_w4Deriv_level3_tight`): **P2 axiom discharged session 8.** Bridge theorem `suzuki5_log_product_quintic_tight_at_suzukiP` derived solely from the headline theorem + `norm_suzuki5_R5_at_suzukiP_le_bchTightPrefactors_boundSum` (now a fully-proved theorem, not an axiom).

Session 9 closed **B1.c** (quintic Taylor bridge for 3-factor symmetric BCH, `norm_symmetric_bch_quintic_sub_poly_le`) and **B1.d** (per-block `strangBlock_log` quintic wrapper, `norm_strangBlock_log_sub_quintic_target_le`) via a scoped Tier-2 axiom `symmetric_bch_quintic_sub_poly_axiom` (see "Remaining axioms"). Sessions 10-12 used the resulting infrastructure to discharge **P1**.

Repository remains 0-sorry. **Axiom count: 1 scoped `private axiom` + Lean's 3 standard** (P1 discharged session 12, only P3 = B1.c remains). See "Remaining axioms" section below.

Earlier state: Basic: H1, H2, M1, quintic BCH, symmetric quartic identity, alt-form, decomposition equality, all six triangle-inequality bounds (R₁, R₂, T3, T4, and the T5/T6 ring-identity bounds with the `(96)⁻¹·[b,DC_a]` cancellation), and the downstream `norm_symmetric_bch_cubic_sub_smul_le` all complete. Palindromic: M1–M4b closed, telescoping bound, exp-Lipschitz `norm_exp_add_sub_exp_le`, **M6 Trotter h4 theorem** `norm_s4Func_sub_exp_le_of_IsSuzukiCubic` — `‖s4Func(t/n, n) - exp(t•(A+B))‖ = O(|t|⁵·s⁵/n⁴)` under IsSuzukiCubic — and **M4b RHS quintic corollary** `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (∃ δ, K, ∀ τ < δ, RHS ≤ K·‖τ‖⁵), which is the payoff lemma for downstream Lean-Trotter.

## Goal

Formalize the BCH formula and its truncated bounds in a general complete normed algebra,
with applications to product formula error analysis (Trotter, Strang, Suzuki).

## Constraints

- **Lean:** 4.29.0-rc8 (via `lean-toolchain`)
- **Mathlib:** pinned in `lake-manifest.json`
- **Typeclass setup:** `[NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]`
- `include 𝕂 in` needed before theorems where `𝕂` appears in proofs but not in the type signature

## Relation to Lean-Trotter

The [Lean-Trotter](https://github.com/Jue-Xu/Lean-Trotter) project proves the first-order
Lie–Trotter formula `(exp(A/n)exp(B/n))^n → exp(A+B)` and second-order Strang splitting
using direct exp bounds. This BCH project provides:

- **H1** (`norm_bch_sub_add_sub_bracket_le`): Commutator extraction — identifies `[A,B]/2`
  as the leading BCH correction, with cubic remainder. Needed for Suzuki S₄.
- **H2** (`norm_symmetric_bch_sub_add_le`): Symmetric BCH — shows the `[A/2,B]` commutator
  cancels in `bch(bch(A/2,B),A/2)`, giving cubic error. This is the BCH-based proof that
  Strang splitting is second-order.

The Lean-Trotter `StrangSplitting.lean` proves second-order convergence via direct algebraic
splitting. The BCH approach here gives a cleaner route to higher-order (S₄) analysis.

## Key Techniques

### Non-commutative scalar issue
`(2:𝕂)⁻¹ • x` (scalar smul) doesn't interact with `noncomm_ring` or `abel`.
**Solution:** Multiply both sides by `(2:𝕂)`, clear via `smul_smul` + `inv_mul_cancel₀` +
`one_smul`, then use `noncomm_ring` on the scalar-free identity.

### Commutator cancellation in H2
Ring identity: `(z*a' - a'*z) + (a'*b - b*a') = (z-a'-b)*a' - a'*(z-a'-b)`.
Proved by `noncomm_ring`. Since `‖z-a'-b‖ = O(s²)`, the RHS is `O(s³)`.

### Taylor bounds for `nlinarith`
Feed `nlinarith` pre-computed bounds: `exp(s) ≤ 1+s+s²` (from `Real.norm_exp_sub_one_sub_id_le`),
`s⁴ ≤ s³` (for `s < 1`), `α³+β³ ≤ s³` (convexity), `αβ ≤ s²/4` (AM-GM).

### Algebraic identities: quartic_identity pattern
The `quartic_identity` (line ~1614) is a ring identity in abstract `ea, eb, a, b` that expresses
`½W + ⅓z³ - C₃` as a sum of terms each bounded by O(s⁴). Proved by:
1. Prove `hpure` sub-identity (pure a,b) by multiplying by 12 + `noncomm_ring`
2. Prove full identity by multiplying by 24 + `simp [smul_smul, ...]` + `noncomm_ring`

### Critical lesson: non-commutative degree-4 cancellation
**The degree-4 cancellation in the quintic BCH is NOT an exact ring identity** (neither in
`a,b` nor in `ea,eb,a,b`). The non-commutative discrepancy `zPz ≠ z²P` means individual
degree-4 terms are `O(s⁴)`, not zero. However, their SUM is `O(s⁵)` due to the BCH structure.

**Consequence:** The quintic proof CANNOT follow the quartic pattern (ring identity → term-by-term
bounds). Instead, it must use a **norm-based grouping** where groups of degree-4 terms are
bounded collectively by `O(s⁵)` using commutator estimates and the specific structure of the
exp/log expansion.

**Key estimates for the degree-4 grouping:**
- `‖[P,z]‖ = ‖[exp(a)exp(b), a+b]‖ ≤ exp(s)·αβs ≈ s³` (commutator of product with sum)
- `‖z[P,z]‖ ≤ s⁴` (one order below the quartic bound)
- The FULL combination of degree-4 corrections is `O(s⁵)` because the BCH Z₅ term provides
  the exact cancellation pattern.

## Remaining Sorry's

None across all five BCH files (verified 2026-04-24). The repository is fully
sorry-free.

## Remaining axioms

Beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`),
the following `private axiom`s are introduced on branch
`trotter-5factor-palindromic`:

### Axiom 1: `BCH.suzuki5_R5_identification_axiom` — **DISCHARGED session 12**

Previously `private` axiom in `BCH/Suzuki5Quintic.lean` asserting the
symbolic 5-factor BCH τ⁵-identification:
`∃ δ > 0, ∃ K ≥ 0, ∀ τ ∈ [−δ, δ],
 ‖suzuki5_bch ℝ A B p τ − τ•(A+B) − τ⁵ • suzuki5_R5 A B p‖ ≤ K·‖τ‖⁶`.

The headline theorem `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` is now a
fully proved theorem (verified `#print axioms` returns only Lean's 3
standard + B1.c). The discharge chain (session 12):

1. Six **regime helpers** (~570 lines): from `‖τ‖ < 1/(10¹¹·pn·qn·s)`,
   derive `hp`, `h1m4p` (per-block `< 1/4`), `hreg` (`‖4X‖+‖Y‖ < 1/4`),
   `hR` (`R < log 2`), `hZ1` (`‖suzuki5_bch‖ < log 2`), `hZ2`
   (`‖outer_bch‖ < log 2`). Use `Real.abs_exp_sub_one_sub_id_le`,
   `norm_bch_sub_add_le`, `norm_logOnePlus_le`. (`Z2_lt_log_two_of_tau_small`
   needs `set_option maxHeartbeats 8000000`.)

2. `norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime` (~150 lines): given
   the 6 regime hypotheses + `IsSuzukiCubic p`, applies
   `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic` (the B2.5 algebraic
   backbone), the per-summand bounds T₁/T₂/T₃, and triangle inequality
   to get `‖...‖ ≤ suzuki5_bch_sub_R5_RHS A B p τ` (an explicit
   polynomial-shape RHS in 7 summands).

3. `D_bound_aux` (~200 lines, `maxHeartbeats 2000000`): per-block residual
   `D ≤ 5·10⁸·pn⁵·qn⁵·s⁵·‖τ‖³`. Uses `norm_strangBlock_log_sub_linear_le`.

4. **Per-term bounds** (~7 helpers, ~600 lines total):
   `RHS_T1_le_aux`, `RHS_T2a_le_aux`, `RHS_T2b_le_aux`, `RHS_T2c_le_aux`,
   `RHS_T3_le_aux`. Each bounds one summand of `suzuki5_bch_sub_R5_RHS`
   by `K_i · ‖τ‖⁶`. Each uses `set_option maxHeartbeats 1000000`-`4000000`.

5. `suzuki5_bch_sub_R5_RHS_le_aux` (~10 lines): combines the per-term
   bounds via `linarith`.

6. **Public theorem** `norm_suzuki5_bch_sub_smul_sub_R5_le` (~30 lines,
   `maxHeartbeats 4000000`): chooses `δ = 1/(10¹¹·pn·qn·s)` and `K =
   4·10⁹·pn⁷·s⁷ + 10⁹·qn⁷·s⁷ + 10⁹·40002⁷·(4pn+qn)⁷·s⁷ +
   2·10¹⁸·pn¹¹·qn¹¹·s¹¹ + 10²⁶·pn¹⁵·qn¹⁵·s¹⁵ + 10⁸·pn⁶·qn⁶·s⁷ +
   2·10³⁰·pn⁹·qn⁹·s⁹`; derives 6 regime hypotheses; applies under_regime
   + the RHS bound + `le_trans`.

Total ~1100 lines added (Suzuki5Quintic.lean). Zero new axioms; only
Lean's 3 standard + B1.c remain.

**Lesson**: For polynomial bookkeeping with deeply nested expressions,
splitting into per-term `private lemma`s avoids kernel whnf blowup. Final
combination via `le_trans` (not `linarith`) sidesteps def-unfolding
arithmetic for huge expressions.

### Axiom 2 (NEW session 9): `BCH.symmetric_bch_quintic_sub_poly_axiom`

(in `BCH/SymmetricQuintic.lean`, scope-`private`) — the quintic Taylor
bridge for the 3-factor symmetric BCH. Asserts that for `‖a‖+‖b‖ < 1/4`,

```
‖symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b
    − symmetric_bch_quintic_poly 𝕂 a b‖ ≤ 10⁹ · (‖a‖+‖b‖)⁷
```

extending `Basic.lean`'s cubic-version `norm_symmetric_bch_cubic_sub_poly_le`
by one degree. CAS at `Lean-Trotter/scripts/verify_strangblock_degree7.py`
confirms degrees 2, 4, 6 vanish identically (palindromic symmetry) and
the degree-7 residual has 126 non-zero `{a,b}`-words, so the statement is
structurally sound — only the explicit `hdecomp` proof is deferred.

The public theorems
`BCH.norm_symmetric_bch_quintic_sub_poly_le` (the B1.c bridge) and
`BCH.norm_strangBlock_log_sub_quintic_target_le` (the B1.d per-block wrapper
in `Palindromic.lean`) depend on this axiom. Downstream: B2 (symbolic
5-factor BCH composition on the Childs basis) and Lean-Trotter's discharge
of the P1 axiom chain pin against B1.d.

Removing the axiom requires three tiers of Lean work (per the session
prompt at `claude/lean-bch-B1c-session-prompt.md`):

- **Tier 1** (~1–2 days): add `bch_quintic_term a b` and
  `norm_bch_sextic_remainder_le` in `Basic.lean` (analogs of the existing
  `bch_quartic_term` and `norm_bch_quintic_remainder_le`), identifying the
  degree-5 coefficient of `bch(a,b)` and giving an `O(s⁶/(2−exp(s)))`
  tail bound. The sextic-remainder proof alone is ~500 lines, paralleling
  the existing ~800-line quintic-remainder proof at line 2326 of
  `Basic.lean`.

- **Tier 2** (~1 week, the hardest): extend the 6-term algebraic
  decomposition in the cubic template `norm_symmetric_bch_cubic_sub_poly_le`
  (line ~3798 of `Basic.lean`) to the 8–10-term decomposition of the
  quintic version. Each additional term captures a degree-5 correction
  bounded by commutator algebra + the new sextic remainder. The CAS
  pipeline at `Lean-Trotter/scripts/compute_bch_prefactors.py` (extended
  to degree 7) discovers the decomposition mechanically. Expect ~400
  lines of `noncomm_ring` after scalar clearing for `hdecomp`.

- **Tier 3** (~1 day): triangle-inequality assembly of the 8–10 per-term
  `O(s⁷)` bounds — analogous to the cubic template's `5×10⁶ + 5000 +
  1000 + 1 + 500 + 2 = 5,006,503` constant chain.

Introduced `private` so only the public theorems appear in the API.

**Session 13 (2026-04-26 / 2026-04-27) progress on Tier 1**:

- ~488 lines committed (`973b5d6`, `4cc5a5a`): log/exp tail bounds at
  order 6, `bch_quintic_term` (= Z₅) definition + smul + norm bound,
  `real_exp_sixth_order_le_sextic`, `norm_logOnePlus_sub_sub_sub_sub_sub_le`.
- **`quintic_identity` discovery hit a structural wall.** CAS script
  `Lean-Trotter/scripts/discover_quintic_identity.py` (rev `f50ed7f`)
  iterated through 17 → 61 → 86 → 115 → 131-133 candidate basis
  elements. With 131+ elements, all 50 LHS_full monomials are covered
  by the basis support, but ONE inconsistency row remains:
  `720·LHS[bbbba] + 720·LHS[bbbbA] = 1`.

  **Root cause**: the basis can produce bbbba (5-letter pure {a,b}) and
  bbbbA (5-letter ending in ea) only in COUPLED form — e.g.,
  `bbbbD₁ = bbbbA - bbbb - bbbba` always couples them with sum 0.
  But the LHS has bbbba with coef +1/720 (from -C₅) and bbbbA with
  coef 0. So the discovery approach (each summand structurally O(s⁶))
  fundamentally cannot close the constraint.

- **Implication**: a "natural extension of `quartic_identity`" at the
  unsubstituted ring level doesn't exist. The proof of
  `norm_bch_sextic_remainder_le` must work post-substitution.

**Strategy (a) VERIFIED — `sextic_pure_identity` holds at deg 5**
(Lean-Trotter `6d029b6`, session 13):

```
½·W_subst[5] + ⅓·y³_subst[5] - ¼·y⁴_subst[5] + ⅕·y⁵_subst[5] - C₅ = 0
```

CAS-verified to give EXACTLY 0 non-zero monomials in pure {a, b}.
Components: W_subst[5] has 26 monomials, y³/y⁴/y⁵_subst[5] each 32,
C₅ has 30. The natural extension of `quartic_identity` DOES exist —
it just operates on SUBSTITUTED polynomials in {a, b}, NOT the
unsubstituted {a, b, ea, eb} level. This sidesteps the bbbba/bbbbA
coupling obstruction.

**Next session — Lean port** (Tier 1 next concrete step):

Define `private theorem sextic_pure_identity` in `BCH/Basic.lean`,
analogous to `quintic_pure_identity` at line 2705. Form:

```
(2:𝕂)⁻¹•W5 + (3:𝕂)⁻¹•y3_5 - (4:𝕂)⁻¹•y4_5 + (5:𝕂)⁻¹•z⁵
  - bch_quintic_term 𝕂 a b = 0
```

where W5, y3_5, y4_5 are explicit polynomials in {a, b}:
- W5 = explicit 26-monomial sum (from W's 2(E+aD+Db+DD)-zP-Pz-P²
  structure substituted at deg 5).
- y3_5 = z²·T₃ + z·T₃·z + T₃·z² + z·T₂² + T₂·z·T₂ + T₂²·z
  (where T₂ = ½a²+ab+½b², T₃ = ⅙a³+½a²b+½ab²+⅙b³).
- y4_5 = z³·T₂ + z²·T₂·z + z·T₂·z² + T₂·z³.

Proof: ×720 scalar clearing + `noncomm_ring`. Estimated 300-500 lines.
Heartbeats likely 100M-500M.

Then build `norm_bch_sextic_remainder_le` using sextic_pure_identity
(deg-5 cancellation) + existing quintic_pure_identity (deg-4) + per-term
norm bounds. Estimated ~800 lines (paralleling
`norm_bch_quintic_remainder_le` at Basic.lean:2326).

- See `claude/lean-bch-B1c-session-prompt.md` for full details.

### Rigorously proved (no axioms) — Axiom 2 infrastructure (sessions 7–8)

All of the following depend only on Lean's 3 standard axioms:

- `BCH.suzukiP` — the canonical real Suzuki root `1/(4 − 4^(1/3))`.
- `BCH.IsSuzukiCubic_suzukiP` — `IsSuzukiCubic suzukiP`, from the
  algebraic identity `4p³ + (1 − 4p)³ = (4 − r³)/(4 − r)³` at
  `r = 4^(1/3)` where `r³ = 4`.
- `BCH.rpow_one_third_cube`, `BCH.one_lt_rpow_one_third`,
  `BCH.rpow_one_third_lt_four`, `BCH.four_sub_rpow_pos` — basic
  inequalities for `4^(1/3)`.
- `BCH.suzukiP_mem_rational_interval` — **tight bound**
  `41449/100000 < suzukiP < 41450/100000` (slack ~8·10⁻⁶ lower and
  ~0.9·10⁻⁶ upper), proved via `nlinarith` on the expanded Suzuki cubic
  `−60p³ + 48p² − 12p + 1 = 0` with polynomial hints at the interval
  endpoints. Tighter than the earlier `414/1000 < … < 415/1000`;
  necessary for the γᵢ bounds below to close.
- `BCH.abs_suzuki5_βᵢ_at_suzukiP_le_γᵢ` (i = 1, 2, 4, 5, 6, 8) —
  six per-i numerical bounds `|βᵢ(suzukiP)| ≤ γᵢ`, each via `nlinarith`
  on the interval + `sq_nonneg` hints. `i = 3, 7` are trivially 0.
- `BCH.norm_suzuki5_R5_at_suzukiP_le_bchTightPrefactors_boundSum` —
  **P2 bound is now a theorem** (was axiom in session 7). Follows from
  the six per-i lemmas + triangle inequality via a 7-step `norm_add_le`
  chain + eight per-term `norm_smul_le` applications.
- `BCH.BCHPrefactors` struct + `bchTightPrefactors` instance (with γ₂
  = 663/10⁶ and γ₆ = 1128/10⁶ as proper ceilings) + `BCHPrefactors.boundSum`
  + positivity + `bchTightPrefactors_boundSum_le_bchFourFoldSum`.
- `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` — bridge theorem
  matching Lean-Trotter's `bch_w4Deriv_level3_tight`. `#print axioms`
  shows only `{propext, Classical.choice, Quot.sound,
  BCH.symmetric_bch_quintic_sub_poly_axiom}` (only B1.c remains —
  P1 and P2 are both discharged as of session 12).

### Coordinated γ fix (landed Lean-Trotter rev `63af0e9`)

Lean-Trotter's `bchTightPrefactors` used truncations of
`|βᵢ(suzukiP)|` to 6 decimals, making γ₂, γ₆ slightly *below* the true
values (~0.3×10⁻⁶). Fixed in Lean-Trotter at rev `63af0e9` to use
ceilings (`γ₂ := 663/10⁶`, `γ₆ := 1128/10⁶`). Lean-BCH matches exactly.

### Prior closures

The M4b RHS quintic corollary `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`
(commit `9ffaab4`) proves that `∃ δ > 0, ∃ K ≥ 0, ∀ τ < δ,
suzuki5_bch_M4b_RHS A B p τ ≤ K·‖τ‖⁵`. Strategy: choose
`δ = 1/(5·pn·qn·s)` with `pn = ‖p‖+1`, `qn = ‖1-4p‖+1`, `s = ‖A‖+‖B‖+1`;
bound each of the four unfolded terms separately via `pow_le_pow_left₀`,
the helper `norm_strangBlock_log_linear` (η + η³ + 10⁷·η⁵ ≤ 40002·η for
η ≤ 1/4), and `gcongr`. Body extracted to private
`suzuki5_bch_M4b_RHS_le_t5_aux` to keep kernel `whnf` within heartbeat
budget (16M).

### Earlier closures (2026-04-23):

The final two Basic.lean triangle-inequality terms were closed on 2026-04-23:

- **Term 6** (`C₄(z,a') - C₄(a'+b,a')` ≤ 2·s⁵): proved via the ring identity
  `DC_z - DC_p = S6` (noncomm_ring after z = (a'+b)+W) where S6 is an explicit
  three-commutator sum, each containing at least one `W`. Norm bounds use
  `‖W‖ ≤ 48·s²/11` and `‖a'+b‖ ≤ 3s/2`.
- **Term 5** (`C₃(z,a') - C₃(a'+b,a') + (96)⁻¹·[b,DC_a]` ≤ 500·s⁵): proved by
  splitting into three sub-identities:
  1. `Id1`: `C₃(p+W,a') - C₃(p,a') = (12)⁻¹·(L(W) + Q(W))` (noncomm_ring after
     12-injective scalar clearing);
  2. `Id2` (key cancellation): `(12)⁻¹·L(W₂) + (96)⁻¹·(b·DC_a - DC_a·b) = 0`
     where `W₂ = (2)⁻¹·(a'b - ba')` — pure ring identity in `a, b` proved by
     192-injective scalar clearing + ~20 `show (192 * products of inverses) = K`
     simp lemmas + `noncomm_ring`;
  3. `Id3`: linearity `L(W) = L(W_rest) + L(W₂)` where `W_rest = W - W₂` (noncomm_ring).
  Combining gives `Term5 = (12)⁻¹·L(W_rest) + (12)⁻¹·Q(W)`, where `W_rest =
  R₁ + C₃(a',b) + C₄(a',b)` has norm `O(s³)` and `W` has norm `O(s²)`.
  Final: `(7/12)·s²·‖W_rest‖ + (4/12)·‖W‖²·‖a'‖ ≤ 183·s⁵ + 2·s⁵ ≤ 250·s⁵`.
- **Triangle inequality:** `R₁ + R₂ + T3 + T4 + T5 + T6 ≤ 5000 + 5·10⁶ + 1000 + 1
  + 500 + 2 = 5,006,503 < 10⁷`, matching the statement's `10⁷·s⁵` constant.
- Downstream `norm_symmetric_bch_cubic_sub_smul_le` (`2·10⁷·|c|³·s⁵`) also closed.

## File Structure

```
BCH/
├── LogSeries.lean         ← log(1+x) series definition, summability, exp∘log = id
├── Basic.lean             ← exp bounds, BCH definition, H1, H2, Lie bracket bridge
├── Palindromic.lean       ← Suzuki-5 palindromic product, M1–M4b, M6 Trotter h4
├── ChildsBasis.lean       ← 8 Childs 4-fold commutators + bchFourFoldSum
                             + BCHPrefactors struct + bchTightPrefactors
                             (axiom 1/2 infrastructure)
├── SymmetricQuintic.lean  ← τ⁵ coefficient of 3-factor symmetric BCH:
                             30-term symmetric_bch_quintic_poly + c⁵ homogeneity +
                             norm bound + **B1.c quintic Taylor bridge theorem**
                             (derives from Tier-2 axiom
                             `symmetric_bch_quintic_sub_poly_axiom`)
└── Suzuki5Quintic.lean    ← βᵢ(p) polynomials + R₅ Childs-basis def + norm bound
                             + headline τ⁵-identification theorem + tight bridge
                             at Suzuki p (axiom 1/2 infrastructure)
```

Note: `Palindromic.lean` now imports `SymmetricQuintic.lean` (as of session 9)
so the B1.d per-block quintic wrapper
`norm_strangBlock_log_sub_quintic_target_le` can reference
`symmetric_bch_quintic_poly` and consume `norm_symmetric_bch_quintic_sub_poly_le`.
New import chain: `Basic → SymmetricQuintic → Palindromic → Suzuki5Quintic`.

## Lean-Trotter interface (branch `trotter-5factor-palindromic`)

Targeting Lean-Trotter's three BCH-interface axioms in
`LieTrotter/Suzuki4ViaBCH.lean`:
1. `bch_w4Deriv_quintic_level2` — unit-coefficient pointwise bound.
2. `bch_w4Deriv_level3_tight` — tight γᵢ at Suzuki p.
3. `bch_uniform_integrated` — order-7 + R₇ + FTC-2 integrated bound.

This branch closes axiom 1 prerequisites (but not axiom 1 itself yet).

### Done on this branch

- `BCH.commBr`, `BCH.childsComm₁..₈`, `BCH.bchFourFoldSum` —
  rfl-compatible mirror of Lean-Trotter defs.
- `BCH.IsSuzukiCubic_real_strict_bound` — for p : ℝ with IsSuzukiCubic p,
  we have 0 < p < 1.
- `BCH.suzuki5_β₁..β₈` — the 8 signed polynomial prefactors (from
  `Lean-Trotter/scripts/compute_bch_prefactors.py` CAS output).
- `BCH.abs_suzuki5_βᵢ_le_one` (i = 1..8) — each |βᵢ(p)| ≤ 1.
- `BCH.suzuki5_R5 A B p` — the τ⁵ Childs-basis combination, opaque.
- `BCH.norm_suzuki5_R5_le_bchFourFoldSum` — unit-coefficient norm bound.
- `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` — **headline theorem**:
  `∃ δ > 0, ∃ K ≥ 0, ∀ τ, ‖τ‖ < δ →
   ‖suzuki5_bch ℝ A B p τ − τ•(A+B) − τ⁵ • suzuki5_R5 A B p‖ ≤ K·‖τ‖⁶`
  under IsSuzukiCubic p. **Fully proved (no axiom)** as of session 12.
  Signature ready for Lean-Trotter consumption.
- `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` — **bridge corollary**:
  `∃ δ > 0, ∃ K ≥ 0, ∀ τ, 0 ≤ τ → τ < δ →
   ‖suzuki5_bch ℝ A B p τ − τ•(A+B)‖ ≤ τ⁵·bchFourFoldSum A B + K·τ⁶`.
  Triangle-inequality combination of the headline theorem with
  `norm_suzuki5_R5_le_bchFourFoldSum`. Lives in `Suzuki5Quintic.lean`
  (not `Palindromic.lean` — the import direction
  `Palindromic → Suzuki5Quintic → ChildsBasis` forces it here since the
  proof references both R₅ identification and the R₅ norm bound).

### Done (axiom 1 closure)

- **Discharged** `suzuki5_R5_identification_axiom` (session 12). See
  "Axiom 1: `BCH.suzuki5_R5_identification_axiom` — DISCHARGED session 12"
  above for the discharge chain (~1100 lines: 6 regime helpers,
  `D_bound_aux`, 5 per-term polynomial bounds, final assembly via
  `le_trans`). `#print axioms norm_suzuki5_bch_sub_smul_sub_R5_le`
  confirms only Lean's 3 standard + B1.c remain.

### B1.c / B1.d closure (session 9, this branch)

**B1.c** — `BCH.norm_symmetric_bch_quintic_sub_poly_le` in
`BCH/SymmetricQuintic.lean`: the quintic Taylor bridge

```
‖symmetric_bch_cubic(a,b) − symmetric_bch_cubic_poly(a,b)
    − symmetric_bch_quintic_poly(a,b)‖ ≤ 10⁹ · (‖a‖+‖b‖)⁷
```

Currently derived from the scoped Tier-2 axiom
`BCH.symmetric_bch_quintic_sub_poly_axiom` (see "Remaining axioms"). CAS
at `Lean-Trotter/scripts/verify_strangblock_degree7.py` confirms the
statement structurally (degrees 2, 4, 6 vanish; degree 7 has 126 non-zero
words).

**B1.d** — `BCH.norm_strangBlock_log_sub_quintic_target_le` in
`BCH/Palindromic.lean`: per-block quintic bound

```
‖strangBlock_log A B c τ − (cτ)•(A+B) − (cτ)³•symmetric_bch_cubic_poly A B
    − (cτ)⁵•symmetric_bch_quintic_poly A B‖ ≤ 10⁹·(‖cτ•A‖+‖cτ•B‖)⁷
```

Trivial reduction via `norm_symmetric_bch_quintic_sub_poly_le` +
`symmetric_bch_cubic_poly_smul` + `symmetric_bch_quintic_poly_smul`.
Directly analogous to the existing cubic wrapper
`norm_strangBlock_log_sub_target_le`, one degree higher.

Both B1.c and B1.d depend only on the new Tier-2 axiom plus Lean's 3
standard (verified via `#print axioms`).

**B2.1 done (session 9)**: per-block quintic decomposition closed in
`BCH/Palindromic.lean`:

- `BCH.suzuki5_bch_quintic_coeff p := 4*p^5 + (1-4p)^5` — τ⁵ scalar
  coefficient (analog of the existing `suzuki5_bch_cubic_coeff`).
- `BCH.strangBlock_log_target_quintic` — per-block linear+cubic+quintic
  polynomial target (analog of `strangBlock_log_target` extended one
  degree).
- `BCH.suzuki5_targets_sum_quintic` and `BCH.target_quintic_sum_4_form`
  — pure algebraic identities (zero axioms, only standard).
- `BCH.norm_4X_plus_Y_sub_quintic_target_le` — bound on
  `‖4X+Y − τ•V − τ³·C₃·E_sym − τ⁵·C₅·E_quintic‖ ≤ K·τ⁷` (depends only
  on B1.c P3 axiom via B1.d, NOT on P1).
- `BCH.norm_suzuki5_bch_sub_smul_sub_quintic_le` — **B2 stepping stone**:
  combines `suzuki5_bch_eq_symmetric_bch` (M4a key step) with B1.c and
  B2.1 to give
  ```
  ‖suzuki5_bch − τ•V − C₃·τ³•E_sym − C₅·τ⁵•E_quintic
       − sym_cubic_poly(4X, Y) − sym_quintic_poly(4X, Y)‖ ≤ K·τ⁷
  ```
  Depends on P3 only (via B1.c). The remaining symbolic work for P1
  closure is to identify `sym_cubic_poly(4X, Y) + sym_quintic_poly(4X, Y)`
  (under `IsSuzukiCubic p`) with `τ⁵·suzuki5_R5 A B p`.

**B2.2.a + B2.2.b done (session 9)**: vanishing identities for the symmetric
poly's on scalar•V inputs (in `BCH/SymmetricQuintic.lean`):

- `BCH.symmetric_bch_quintic_poly_apply_smul_smul (V α β) :`
  `symmetric_bch_quintic_poly 𝕂 (α•V) (β•V) = 0`. Proof: each 5-letter
  word collapses to `(α^k·β^(5−k))•V⁵`; the sum of word coefficients per
  k-group is identically zero (k=4: 7−28+42−28+7=0; k=3:
  −28+72+12−48−48+12+32−48+72−28=0; k=2:
  32−48−48+32−48+192−48−48−48+32=0; k=1: −8+32−48+32−8=0; k∈{0,5}: no
  terms). Closed via `simp + ← add_smul + ring` after a 5-fold smul-mul
  absorption helper. Zero new axioms.
- `BCH.symmetric_bch_cubic_poly_apply_smul_smul (V α β) :`
  `symmetric_bch_cubic_poly 𝕂 (α•V) (β•V) = 0`. Trivial: the inner
  commutator `(α•V)(β•V) − (β•V)(α•V) = αβ·V² − αβ·V² = 0`. Zero new
  axioms.

**Significance**: These are the structural foundations for B2.2. They show
that the "leading τ⁵" contribution from `sym_cubic_poly(4X, Y)` and
`sym_quintic_poly(4X, Y)` (substituting only the linear `(cτ)•V` parts of
X, Y) vanishes identically. The non-zero τ⁵ contribution comes from the
"linear-in-residual" terms of `sym_cubic_poly(4X, Y)` (where one slot has
the `(cτ)³·E_sym` cubic residue), giving 4-fold commutators in V's
letters — exactly the Childs basis structure. The `sym_quintic_poly(4X, Y)`
contribution at τ⁵ is `0` (since linear-in-residual would be τ⁷, beyond
the τ⁵ window).

**B2.2.c (session 9, FULL)**:
`norm_symmetric_bch_quintic_poly_apply_smul_add_smul_add_le` in
`BCH/SymmetricQuintic.lean` — fully proved:

```
‖sym_quintic_poly(α•V+δa, β•V+δb)‖ ≤ 2·N⁴·(‖δa‖+‖δb‖)
```

when `‖α•V‖, ‖β•V‖, ‖α•V+δa‖, ‖β•V+δb‖ ≤ N`. Built on:
- 5-letter telescoping Lipschitz `word_5_diff_le` (private):
  `‖x₁·x₂·x₃·x₄·x₅ − y₁·y₂·y₃·y₄·y₅‖ ≤ N⁴ · (‖x₁−y₁‖+...+‖x₅−y₅‖)`.
- B2.2.a vanishing: `sym_quintic_poly(α•V, β•V) = 0`.
- Regrouping `Σ cᵢ•full_i − Σ cᵢ•lin_i = Σ cᵢ•(full_i − lin_i)` via
  `unfold + simp [smul_sub] + abel` after `rw [h0, sub_zero]`.
- 30 b_i per-word diff bounds + 30 t_i smul-diff bounds + 29 norm_add_le
  + linarith with `N⁴·D ≥ 0` hint. The constant: `Σ |c_w|/5760 · 5 =
  1216·5/5760 ≈ 1.056 ≤ 2` (factor 2 buffer). Zero new axioms.

**B2.2.d (session 9)**:
`norm_symmetric_bch_cubic_poly_apply_smul_add_smul_add_le` in
`BCH/Palindromic.lean` — fully proved:

```
‖sym_cubic_poly(α•V+δa, β•V+δb)‖ ≤ (2/3)·(N²·D + N·D²)
```

Composes existing `norm_commutator_near_V_le` (slice 8) — bound
`‖[fA, fB]‖ ≤ 2·N·D + 2·D²` from `[α•V, β•V] = 0` cancellation —
with `norm_symmetric_bch_cubic_poly_le_commutator`. Lives in
Palindromic.lean (not SymmetricQuintic.lean) due to import direction.
Zero new axioms.

**For B2 closure**: when `α, β = O(τ)` (linear) and `δa, δb = O(τ³)`
(per-block residual), B2.2.c gives `‖sym_quintic_poly(4X, Y)‖ = O(τ⁷)`
(gaining 2 powers over trivial `(‖a‖+‖b‖)⁵ = O(τ⁵)`); B2.2.d gives
`‖sym_cubic_poly(4X, Y)‖ = O(τ⁵)` matching the τ⁵ leading order
(gaining nothing in asymptotic order, but identifying the structure for
the Childs-basis projection in B2.2.e).

**B2.2.e foundation (session 10)**: linear-in-residual extraction
for `sym_cubic_poly(α•V + δa, β•V + δb)` in `BCH/Palindromic.lean`.
All zero new axioms. Closed:

- **Definitions**: `sym_cubic_poly_linear_part_smul_V`,
  `sym_cubic_poly_quadratic_part_smul_V`, `sym_cubic_poly_cubic_part_smul_V`.
  Linear part closed form (verified by CAS):
  `L = ((α + 2β)/24) • (β • [V,[V,δa]] - α • [V,[V,δb]])`.
- **Algebraic decomposition** `symmetric_bch_cubic_poly_smul_V_decomp`:
  `sym_cubic_poly(α•V+δa, β•V+δb) = L + Q + C`. Proved via 24-injectivity
  scalar clearing (`mul_inv_cancel_left₀` + helper for `24·12⁻¹=2`)
  + `module` tactic for the final 𝕂-bilinear/𝔸-noncomm verification.
- **Cubic part bound** `norm_sym_cubic_poly_cubic_part_smul_V_le`:
  `‖C‖ ≤ (1/2)·D³` where `D = ‖δa‖+‖δb‖`.
- **Quadratic part bound** `norm_sym_cubic_poly_quadratic_part_smul_V_le`:
  `‖Q‖ ≤ (3/2)·N·D²` when `‖α•V‖, ‖β•V‖ ≤ N`. Built on commBr-bilinearity
  helpers (`commBr_smul_left_eq`, `commBr_smul_right_eq`) and a 3-fold
  commutator bound `‖[X, [Y, Z]]‖ ≤ 4·‖X‖·‖Y‖·‖Z‖`.
- **Combined residual bound** `norm_sym_cubic_poly_sub_linear_part_le`:
  `‖sym_cubic_poly - linear_part‖ ≤ (3/2)·N·D² + (1/2)·D³`.

**Significance**: identifies the linear part L as the *exact* τ⁵ content
of `sym_cubic_poly(4X, Y)` modulo τ⁶+ residual. With N = O(τ), D = O(τ³):
combined residual = O(τ·τ⁶ + τ⁹) = O(τ⁷), well below the τ⁶ threshold.

**B2.2.e key identity (session 10, NEW — Childs-basis projection closed)**:
the central symbolic content of B2.2.e is now fully proved in
`BCH/Palindromic.lean`:

```
BCH.comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis :
  (24 : 𝕂) • commBr (A + B) (commBr (A + B) (symmetric_bch_cubic_poly 𝕂 A B)) =
    (childsComm₁ A B + childsComm₃ A B + childsComm₅ A B + childsComm₇ A B) +
    (2 : 𝕂) • (childsComm₂ A B + childsComm₄ A B + childsComm₆ A B + childsComm₈ A B)
```

Equivalently `[V, [V, sym_E₃]] = (1/24)·(C₁+C₃+C₅+C₇) + (1/12)·(C₂+C₄+C₆+C₈)`.
Zero new axioms (verified `#print axioms` returns only Lean's 3 standard).

**Strategy** (split into three small `noncomm_ring` lemmas):

1. `comm_AB_AB_ABA_eq_childs_basis_odd`:
   `[A+B, [A+B, [A, [B, A]]]] = C₁ + C₃ + C₅ + C₇` (~64 monomials, ~13s).
2. `comm_AB_AB_BBA_eq_childs_basis_even`:
   `[A+B, [A+B, [B, [B, A]]]] = C₂ + C₄ + C₆ + C₈` (similar).
3. `smul_24_symmetric_bch_cubic_poly`:
   `24 • sym_E₃(A, B) = -[A,[A,B]] + 2 • [B,[B,A]]` (clears 1/24, 1/12 inverses).

Plus helpers `comm_A_A_B_eq_neg_comm_A_B_A` ([A,[A,B]] = -[A,[B,A]]),
`commBr_add_right_eq`, `commBr_neg_right_eq`. Combined via explicit
`rw` chain (avoiding `simp only` which mis-rewrites due to bilinearity-vs-neg
interactions).

**Lesson**: the original "monolithic" `noncomm_ring` proof timed out at
1.6M heartbeats on the ~128-monomial expansion. Splitting into the two
half-identities (each ~64 monomials, ~10s) plus an explicit ring-identity
for `24 • sym_E₃` made the proof tractable. Similar splitting may help
with B2.5 and beyond.

**B2.2.e substitution lemmas (session 10, NEW)**: Two corollaries of the
Childs-basis projection identity, in `BCH/Palindromic.lean`. Zero new axioms.

- `BCH.sym_cubic_poly_linear_part_at_smul_E3`: when `δa = γ•E_3` and
  `δb = δ•E_3` for `E_3 = symmetric_bch_cubic_poly A B`, the linear part
  collapses to a single scalar multiple of `[V,[V,E_3]]`:
  ```
  L = ((24)⁻¹ * (α + 2β) * (β·γ - α·δ)) • [V,[V,E_3]]
  ```
- `BCH.smul_24_sym_cubic_poly_linear_part_at_smul_E3_eq_childs_basis`:
  combining the substitution with the Childs-basis projection,
  ```
  24 • L = ((24)⁻¹ * (α + 2β) * (β·γ - α·δ)) •
           [(C₁+C₃+C₇+C₅) + 2 • (C₂+C₄+C₆+C₈)]
  ```

**B2.2.e scalar instantiation (session 10, NEW)**: Closed-form τ⁵ content
of the linear-in-residual part for the strangBlock-residue case
(α = 4pτ, β = (1-4p)τ, γ = 4(pτ)³, δ = ((1-4p)τ)³). Zero new axioms.

- `BCH.sym_cubic_poly_linear_part_at_strangBlock_E3`:
  ```
  L = ((1/3) · p(1-4p)(1-2p)(p²-(1-4p)²) · τ⁵) • [V,[V,E_3]]
  ```
  Closed form: the polynomial `poly_p := p(1-4p)(1-2p)(p²-(1-4p)²)` is
  the prefactor, scaled by `(1/3)·τ⁵`.
- `BCH.smul_24_sym_cubic_poly_linear_part_at_strangBlock_E3_eq_childs_basis`:
  combined with the Childs projection,
  ```
  24 • L = ((1/3) · poly_p · τ⁵) • [(C₁+C₃+C₅+C₇) + 2 • (C₂+C₄+C₆+C₈)]
  ```

**B2.2.e prep (session 10, NEW)**: τ³-vanishing in `4X+Y` under
`IsSuzukiCubic`. Zero new axioms.

- `BCH.norm_4X_plus_Y_sub_quintic_target_of_IsSuzukiCubic_le`:
  ```
  ‖4•X + Y - τ•V - (τ⁵ * (4p⁵+(1-4p)⁵)) • E_5‖
    ≤ 4·10⁹·σ_p⁷ + 10⁹·σ_(1-4p)⁷
  ```
  Identifies the second τ⁵ contributor: `(4p⁵+(1-4p)⁵)·τ⁵ • E_5`
  (alongside `L_leading` from sym_cubic_poly's linear part).

**Open** (the remaining B2.2.e work to finish P1 axiom discharge): The
**three τ⁵ contributors** are now all explicit:

1. **`L_leading`** (from sym_cubic_poly(4X, Y)): closed form
   `(1/3)·poly_p·τ⁵ • [V,[V,E_3]]`, projects to Childs basis via the
   `comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis` identity (DONE).
2. **`(4p⁵+(1-4p)⁵)·τ⁵ • E_5`** (from `4X+Y - τ•V` under IsSuzukiCubic):
   E_5's Childs-basis decomposition is now PROVEN
   (`smul_5760_symmetric_bch_quintic_poly_eq_childs_basis`):
   ```
   5760 • E_5 = -7·C₁ - 12·C₂ + 16·C₄ - 16·C₅ - 48·C₆ - 8·C₈
   ```
   Coefficients verified by Gauss-Jordan symbolic solving (with Jacobi
   free parameters set to 0). Provable in Lean via `Algebra.smul_def +
   map_intCast/map_ofNat + noncomm_ring` on ~126 monomials (~10s).
3. **`sym_quintic_poly(4X, Y)`** (from sym_bch's degree-5 BCH part):
   B2.2.c bound shows this is `O(τ⁷)`, so contributes nothing at τ⁵.

**B2.2.e Jacobi relations (session 10, NEW)**: `childsComm₂_eq_childsComm₃`
and `childsComm₆_eq_childsComm₇` — exact ring identities (not just
modulo Jacobi in the abstract Lie algebra) verified by `noncomm_ring`.
These reduce the over-completeness of the 8-Childs basis to dim-6
weight-5 free Lie algebra, and bridge between the Lean-side and CAS-side
choice of Jacobi free parameters.

**B2.2.e τ⁵ matching identity (session 10, NEW — CORNERSTONE PROVEN)**:

```
BCH.L_leading_plus_E5_eq_R5 : ∀ (A B : 𝔸) (p : ℝ), IsSuzukiCubic p →
  ((1/3) * poly_p) • [V,[V,E_3]] + (4p⁵+(1-4p)⁵) • E_5 = suzuki5_R5 A B p
```

(`poly_p := p(1-4p)(1-2p)(p²-(1-4p)²)`). Zero new axioms.

**Strategy**:
1. Apply Childs projections: rewrite `[V,[V,E_3]]` and `E_5` on the basis.
2. Apply Jacobi C₂=C₃, C₆=C₇ to merge over-complete basis elements.
3. Unfold `suzuki5_R5` and `βᵢ(p)`.
4. Establish 6 per-Cᵢ polynomial identities via `linear_combination * hcubic`
   with CAS-derived multipliers (e.g., for C₁: `41p²/5760 - 29p/7200 - 169/144000`).
5. Substitute `βᵢ(p) → L_poly` form (`rw [eq1, ..., eq8]`).
6. Close via `module` (pure ring identity in p, no hcubic dependence).

**B2.2.e τ⁵-scaled matching (session 10, NEW)**:
`sym_cubic_linear_part_τ5_plus_E5_τ5_eq_R5_τ5` — the τ⁵-scaled form
suitable for direct substitution into the `suzuki5_bch` triangle inequality:

```
sym_cubic_poly_linear_part_smul_V (A+B) (4pτ) ((1-4p)τ)
    (4(pτ)³ • E_3) (((1-4p)τ)³ • E_3) +
  (τ⁵ * (4p⁵+(1-4p)⁵)) • E_5 = τ⁵ • R₅(A,B,p)
```

**B2.5 algebraic decomposition (session 10, NEW — STRUCTURAL BACKBONE PROVEN)**:
`suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic`:

```
suzuki5_bch - τ•V - τ⁵•R₅ =
  R_b1c + (sym_cubic_poly(4X,Y) - L_leading_τ⁵) + sym_quintic_poly(4X,Y)
```

(under `IsSuzukiCubic p`). Zero new axioms. Proof: substitute the τ³
vanishing + the τ⁵-scaled matching identity, then `abel`.

This is the algebraic identity that reduces P1 discharge to bounding each
of the three summands.

**Remaining for P1 closure**: **Triangle-inequality bound assembly**.

The three summands' bounds:
1. **R_b1c**: `‖suzuki5_bch - τ•V - τ³·c·E_3 - τ⁵·γ5·E_5 - sym_cubic_poly(4X,Y)
   - sym_quintic_poly(4X,Y)‖ ≤ K·σ⁷` from `norm_suzuki5_bch_sub_smul_sub_quintic_le`.
2. **sym_cubic_poly(4X,Y) − L_leading_τ⁵ = (Q + C) + L_extra**:
   - `‖Q + C‖ ≤ (3/2)·N·D² + (1/2)·D³` from `norm_sym_cubic_poly_sub_linear_part_le`.
   - `‖L_extra‖`: bounded via 3-fold commutator + B1.d's `norm_strangBlock_log_sub_target_le`.
3. **sym_quintic_poly(4X,Y)**: bounded by `norm_symmetric_bch_quintic_poly_le`
   (`‖E_5(a,b)‖ ≤ (‖a‖+‖b‖)⁵`).

Final assembly (~100 lines): `norm_add_le` chain + per-term `norm_smul_le`
+ existential δ choice (similar to `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`
template).

### Session 11 (B2.5 T₂ bound + assembly under regimes, this branch — partial P1 progress)

Session 11 closed the **T₂ bound** for the τ⁶ triangle-inequality assembly,
along with the supporting infrastructure AND the **assembly under regime
hypotheses** (the public-API portion of the P1 axiom). Stopped short of
fully replacing the P1 axiom (regime-hypothesis derivation is the
remaining work). New helpers in `BCH/Palindromic.lean` and
`BCH/Suzuki5Quintic.lean`, all zero new axioms:

#### Foundation helpers (all `private` or local)

- `BCH.commBr_sub_right_eq` (private): `[X, Y₁ - Y₂] = [X, Y₁] - [X, Y₂]`.
  Single-line `noncomm_ring` proof.
- `BCH.sym_cubic_poly_linear_part_smul_V_sub_eq`: bilinearity of `L`
  packaged in subtraction form,
  ```
  L(V, α, β, δa1, δb1) - L(V, α, β, δa2, δb2) = L(V, α, β, δa1-δa2, δb1-δb2).
  ```
  Closed via `commBr_sub_right_eq` × 2 + `module`. Used to express
  `L(δa_actual, δb_actual) - L(δa_lead, δb_lead) = L(4·R_p, R_q)`
  where R_p, R_q are per-block cubic residues.
- `BCH.norm_sym_cubic_poly_linear_part_smul_V_le`: scalar bound on `L`,
  ```
  ‖L(V, α, β, δa, δb)‖ ≤ (1/6)·‖α + 2β‖·‖V‖²·(‖β‖·‖δa‖ + ‖α‖·‖δb‖).
  ```
  Direct chain `norm_smul_le` + `norm_three_commBr_le`. The `4` from the
  3-fold commutator bound combines with `1/24` to give the leading `1/6`.
- `BCH.strangBlock_residue_eq_smul_X_sub_target`: per-block residue identity,
  ```
  (4 : 𝕂) • X - (4*p*τ) • (A+B) - (4*(p*τ)^3) • E_3 =
    (4 : 𝕂) • (X - strangBlock_log_target 𝕂 A B p τ).
  ```
  Pure algebraic identity (proved via `← smul_smul` on each summand +
  `module`), used to translate `δa - δa_lead` to `4·R_p`.

#### B2.5 T₂ main bound ⭐⭐ (now provable)

- `BCH.norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le`: the τ⁶
  assembly's T₂ bound, fully proved:
  ```
  ‖sym_cubic_poly(4X, Y) - L_leading_τ⁵‖ ≤
    (3/2)·N·D² + (1/2)·D³ +
    (1/6)·‖4pτ + 2(1-4p)τ‖·‖A+B‖² ·
      (‖(1-4p)τ‖·4·10⁷·σ_p⁵ + ‖4pτ‖·10⁷·σ_q⁵)
  ```
  where `N = ‖(4pτ)•(A+B)‖ + ‖((1-4p)τ)•(A+B)‖`, `D = ‖4X − (4pτ)•(A+B)‖
  + ‖Y − ((1-4p)τ)•(A+B)‖`. Strategy: algebraic decomposition (via
  `sym_cubic_poly_linear_part_smul_V_sub_eq`) to express
  `T₂ = QC + L_extra`, then bound QC via `norm_sym_cubic_poly_sub_linear_part_le`
  and L_extra via `norm_sym_cubic_poly_linear_part_smul_V_le` +
  `norm_strangBlock_log_sub_target_le` + `strangBlock_residue_eq_smul_X_sub_target`.

  For the τ⁶ assembly, this bound is `O(τ⁷)`: with α, β = O(τ),
  N = O(τ), D = O(τ³), σ_p, σ_q = O(τ), the QC term is `O(τ·τ⁶) = O(τ⁷)`
  and the L_extra term is `O(τ·τ²·τ⁵) = O(τ⁸)` (dominated by QC).

#### B2.5 assembly under regime hypotheses ⭐⭐ (now provable)

In `BCH/Suzuki5Quintic.lean`:

- `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime` (private):
  given the 6 regime hypotheses `hR, hp, h1m4p, hreg, hZ1, hZ2` and
  `IsSuzukiCubic p`, bounds the τ⁶ residual by an explicit polynomial:
  ```
  ‖suzuki5_bch ℝ A B p τ - τ•(A+B) - τ⁵•R₅(A,B,p)‖ ≤ poly_T1 + poly_T2 + 2·N⁴·D
  ```
  where
  - `poly_T1` is the B1.c residual bound from
    `norm_suzuki5_bch_sub_smul_sub_quintic_le`
  - `poly_T2` is the new T₂ bound from
    `norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le`
  - `2·N⁴·D` is the T₃ bound from B2.2.c
    (`norm_symmetric_bch_quintic_poly_apply_smul_add_smul_add_le`)

  Strategy: apply `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic`, triangle
  inequality, bound each summand, combine via `add_le_add`. Zero new axioms.

**DONE (session 12)**: P1 axiom fully discharged. The public theorem
`norm_suzuki5_bch_sub_smul_sub_R5_le` is now a real theorem (no axiom).

1. ~~**Regime-hypothesis derivation**~~: **DONE session 12.** Six helpers
   in `BCH/Suzuki5Quintic.lean` derive `hR, hp, h1m4p, hreg, hZ1, hZ2`
   from `‖τ‖ < 1/(10¹¹·pn·qn·s)`. `Z2_lt_log_two_of_tau_small` needs
   `set_option maxHeartbeats 8000000`.
2. ~~Triangle-inequality assembly~~: **DONE session 11** as
   `norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime`.
3. ~~**Polynomial bookkeeping**~~: **DONE session 12.** Split into
   per-term `private lemma`s (`RHS_T1_le_aux`, `RHS_T2a/b/c_le_aux`,
   `RHS_T3_le_aux`, `D_bound_aux`) to avoid kernel whnf blowup. Final
   composition via `le_trans` (not `linarith`) sidesteps def-unfolding
   arithmetic on the huge `suzuki5_bch_sub_R5_RHS` expression.

Total ~1100 lines added. Zero new axioms.

### Axiom 2 infrastructure (sessions 7–8, this branch)

Lean-BCH-side infrastructure for Lean-Trotter's `bch_w4Deriv_level3_tight`
is now FULLY PROVED (no P2 axiom). See "Rigorously proved" section
above for the full list. The bridge theorem
`BCH.suzuki5_log_product_quintic_tight_at_suzukiP` is ready for
Lean-Trotter-side axiom → theorem conversion.

### Axiom 3

Out of scope on this branch. Requires order-7 BCH + R₇ bound + FTC-2
integration.
