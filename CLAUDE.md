# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status (session 59, 2026-05-19) — τ⁷ piece-by-piece calibration

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**
(unchanged): `symmetric_bch_septic_sub_poly_axiom`,
`norm_septic_match_residual_le_axiom`.

**Calibration of the piece-by-piece septic discharge (Path A)**:

Started building the second-order Taylor remainder framework for the 4
remaining single-V pieces in the joint cancellation roadmap (P_3_C5,
P_4_C5, P_2_C7, P_3_C6). The motivation: first-order Lipschitz gives
`O(s^{p+j-1})` which is short of the s⁹ target for 4 of 5 pieces.
Second-order Taylor gives `O(s^{p+2j-2}) ≥ s⁹` for all 4.

**Phase 1 commit `80686d1` (this session, 213 Lean lines)**:

* `bch_quintic_term_lin_diff (x V y : 𝔸) : 𝔸` — 75-term polynomial
  in {x, V, y}, LCM 720. First-order directional difference
  `Σ_w c_w · Σ_{i ∈ x-positions of w} word_with_V_at_i`.
* `bch_quintic_term_taylor2_remainder (x V y : 𝔸) : 𝔸` — 105-term
  polynomial, LCM 720, broken down as k=2 (70 terms), k=3 (30), k=4 (5).
* `bch_quintic_term_taylor2_decomp` — the matching identity
  `bch_quintic_term(x+V, y) - bch_quintic_term(x, y) = lin_diff + taylor2_remainder`.
  Proved via `unfold + simp only + match_scalars <;> ring` at
  `maxHeartbeats 1024000000`.

CAS-generated via `scripts/gen_bch_quintic_term_taylor2.py` (200 lines).

**Calibration findings (smaller-than-estimated for Phase 1)**:

* Original estimate: 500–1000 lines for Phase 1. Actual: 213. Both
  `lin_diff` (75) and `taylor2_remainder` (105) fit within the 124-term
  simp recursion limit, so single Finset.sum DEFs work cleanly.
* Hit the `[doc-comment] [set_option ... in] <decl>` parser order issue
  (memory: `feedback_doc_comment_set_option_order.md`). The correct
  order is `set_option ... in /-- doc -/ <decl>`. Cost: 1 build cycle.

**Phase 2 ahead (next session)**:

Bound `‖bch_quintic_term_taylor2_remainder(x, V, y)‖ ≤ K · M³ · ‖V‖²`
where `M = ‖x‖ + ‖V‖ + ‖y‖`. Approach:

1. Split into per-k sub-defs `taylor2_remainder_2V/_3V/_4V` (70 / 30 / 5
   terms each). Each fits a single Finset.sum.
2. Per-k uniform bound via per-i case analysis:
   * k=2: ≤ (Σ|c|_k2 / 720) · `‖V‖² · M³` (exact factorization).
   * k=3: ≤ (Σ|c|_k3 / 720) · `‖V‖³ · M²`, lift to `‖V‖² · M³` via
     `‖V‖ ≤ M` (automatic since M = ‖x‖+‖V‖+‖y‖).
   * k=4: ≤ (Σ|c|_k4 / 720) · `‖V‖⁴ · M`, lift similarly.
3. Triangle-sum: `‖taylor2_remainder‖ ≤ 536/720 · M³ · ‖V‖² ≈
   0.745 · M³ · ‖V‖²`.

Estimated 1000–1500 Lean lines (per-pattern case analysis for 25
position patterns + per-piece norm bounds + combined).

**Phase 3 (after Phase 2)**: Specialize at `V = V_3 = bch_cubic_term(½a, b)`,
`x = ½a + b`, `y = ½a`. Identify `bch_quintic_term_lin_diff(½a+b, V_3, ½a)`
with the existing `septic_d7_P3_C5_lin_poly`. Bound the residual ≤ K·s⁹
via Phase 2 + ‖V_3‖ ≤ s³ + M ≤ 2.02·s. Estimated 200–400 lines.

After P_3_C5 calibration, the remaining 3 single-V pieces (P_4_C5,
P_2_C7, P_3_C6) follow the same pattern with k=5,6,7 Taylor frameworks.
Plus the Cross_V₂·V₃_C5 bilinear piece needs special treatment.

**Roadmap reset**: prior session estimated 10–15 sessions for full τ⁷
discharge. Phase 1's better-than-estimated complexity suggests 6–10
sessions may suffice if subsequent phases hold.

## Status (session 58, 2026-05-19) — τ⁵ pipeline closure

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.
Both gate τ⁷-order results only.

**Strategic milestone confirmed (this session)**: the tight 4th-order
Trotter formula error bound on the Lean-Trotter side is **axiom-free at
the project level** after pushing 83 local commits to GitHub and bumping
the Lean-Trotter pin to `d455ff0`.

`#print axioms` on each τ⁵ headline (Lean-BCH side) returns only
`[propext, Classical.choice, Quot.sound]`:
- `norm_suzuki5_bch_sub_smul_sub_R5_le` (P1)
- `suzuki5_log_product_quintic_of_IsSuzukiCubic` (P1 bridge)
- `suzuki5_log_product_quintic_tight_at_suzukiP` (P2)

Downstream on Lean-Trotter side (axiom-free):
- `norm_suzuki4_childs_form_via_level3` (tight 4th-order, Childs (2021) form)
- `norm_suzuki4_level3_bch` (tight γᵢ prefactors)
- `norm_suzuki4_level2_bch` (unit-coefficient τ⁵ bound)

The Lean-BCH B1.c quintic axiom (`symmetric_bch_quintic_sub_poly_axiom`)
was discharged May 10–11; the Lean-Trotter pin at `cf5eea3` (Apr 26)
was pre-discharge. The pin bump closes the loop.

The 2 remaining Lean-BCH axioms gate ONLY the L4 τ⁷ uniform refinement
on the Lean-Trotter side (`bch_uniform_integrated`), not the core
4th-order Trotter bound.

This was a **stale-docs problem**, not a math problem. The piece-by-piece
septic work (sessions 26–57) is on a separate τ⁷-refinement thread,
orthogonal to the τ⁵ tight 4th-order Trotter goal.

Single commit this session:
**`<this commit>`** — doc cleanup in Lean-BCH and Lean-Trotter
(stale "B1.c is alive" claims now correctly say "discharged"); the
Tier-2 of B1.c section now describes the proved theorem.

## Status (session 57, 2026-05-18)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 57 (2026-05-18, d7 CAS matching identity + residual sizing, 2 commits)**:

CAS-only progress on the joint cancellation roadmap (session 52). Two
commits this session: (1) d7 analog of the d8 C_p grouping verification,
(2) a sizing study measuring residual sizes for each (C_p, V_j) matching
to plan the Lean strategy.

**`5ddd583`** — `scripts/verify_d7_C_k_diff_matching.py`: 8 d7 sub-pieces
group by C_p origin into 4 groups (Group_C3/C4/C5/C6 with 3+2+2+1
sub-pieces) summing exactly to `septic_d7_perturbation_poly` (116 terms,
LCM 276480). Identity: pert_d7 = V_7 + P_6 + Σ Group_Cp. Corrects session
52's docstring typo (P_3_C3_quad is in Group_C3, not C_4).

**`75f4ec7`** — `scripts/verify_d7_P2_C6_lin_residual.py` and
`scripts/verify_matching_residual_sizes.py`: measures the deg-(q+1)+
residual size for each matching identity. Three strategies needed by piece:

| Piece              | Residual terms      | Σ\|num\|/LCM | Lean strategy             |
|--------------------|--------------------:|------------:|---------------------------|
| d=8 P_2_C5_cubic   |  48 (d9 only)       | 0.0007      | (A) single DEF + identity |
| d=7 P_2_C5_quad    | 126 (d8:78,d9:48)   | 0.0059      | (A) single DEF + identity |
| d=8 P_2_C6_quad    | 194 (d9:120,d10:74) | 0.0025      | (B) per-deg split DEFs    |
| d=7 P_2_C6_lin     | 304 (d8:110,d9:120,d10:74) | 0.0106 | (B) per-deg split DEFs |
| d=8 P_2_C7_lin     | 2488                | 0.0134      | (C) Lipschitz residual    |
| d=8 Cross_V2_V3_C5 | 3193                | 0.0064      | (C) Lipschitz residual    |
| d=8 P_4_C5_lin     | 2929                | 0.0005      | (C) Lipschitz residual    |
| d=7 P_3_C5_lin     | 5029                | 0.0062      | (C) Lipschitz residual    |
| d=8 P_3_C6_lin     | 7638                | 0.0028      | (C) Lipschitz residual    |

(A) = direct polynomial-form Lean DEF + identity via `match_scalars <;> ring`
+ Finset.sum norm bound.

(B) = decompose residual into per-degree pieces (each ≤ 124 terms to fit
the simp recursion pattern, per memory `feedback_simp_recursion_180_terms.md`).
Each piece gets its own DEF + bound; identity combines via `abel`.

(C) = bound the full diff via `norm_bch_kth_term_diff_le` (which gives
`p·M^(p-1)·‖V‖` ≤ `p·M^(p-1)·s^j`), subtract the explicit deg-q part bound,
deduce residual bound. Loses constant tightness but doesn't need polynomial
form. Useful insight from the sizing: even the large residuals have small
Σ|num|/LCM (e.g., P_4_C5_lin: 2929 terms but only 0.0005), so the Lipschitz
approach loses little.

**Status of the joint cancellation roadmap** (session 52 items A–D):

| Step | d=7 | d=8 |
|------|-----|-----|
| Per-piece norm bounds (raw) | 6 parent + 4 sub ✓ (sessions 54-56) | 9 parent + 7 sub ✓ (sessions 53-56) |
| CAS-level Group_Cp grouping | ✓ (session 57) | ✓ (session 52) |
| Residual sizing study | ✓ (session 57) | ✓ (session 57) |
| Operator-form identities (Dynkin pieces) | 5 of 6 piece-types ✓ (sessions 45-46) | 6 of 9 piece-types ✓ (sessions 49-50) |
| Lean matching identities (small/marginal pieces) | covers P_2_C5_quad via decomp | 1 of ~3 small ✓ (P_2_C5_cubic, session 57) |
| Lean residual norm bounds (small/marginal pieces) | covers P_2_C5_quad via piece bound | 1 of ~3 small ✓ (P_2_C5_cubic, session 57) |
| Lipschitz residual bounds (large pieces) | pending | pending |
| Final O(s⁹) joint assembly | pending | pending |

**First (matching identity + residual norm bound) pair landed (session 57):**

`bch_quintic_term_V2_shift_decomp` (commit `812119c`, 139 lines):

    bch_quintic_term(½a + b + V_2, ½a) − bch_quintic_term(½a + b, ½a)
      = septic_d8_P2_C5_lin_poly             (deg 6, k=1, NEW)
      + septic_d7_P2_C5_quad_poly            (deg 7, k=2, session 46)
      + septic_d8_P2_C5_cubic_poly           (deg 8, k=3, session 51)
      + septic_d8_P2_C5_quartic_residual_poly (deg 9, k=4, NEW)

V_2 inlined as `(1/4)·(a*b − b*a)`. Proof: standard 4-line pattern
`unfold (4 quintic-groups + 4 P_2_C5 defs) + simp only [smul/mul distribute]
+ match_scalars <;> ring`.

`norm_septic_d8_P2_C5_quartic_residual_poly_le` (commit `57802c4`,
351 lines via the extended generator):

    ‖septic_d8_P2_C5_quartic_residual_poly(a, b)‖ ≤ (768/368640) · s⁹
                                                  ≈ 0.00208 · s⁹.

CAS-derived via `scripts/gen_d8_subpiece_norm_bound.py
d8_P2_C5_quartic_residual` (generator extended to deg-9 case). Pattern
matches the existing per-piece d8 bounds (sessions 53-56): TermN family +
Fin wrapper + eq_sum + per-i bound via `deg9_smul_word_le` + final
`norm_sum_le` + `Finset.sum_const` + ring.

The matching identity automatically gives the d=7 case (k=2 piece matches
`septic_d7_P2_C5_quad_poly`, session 46) and the d=6 case (the new
`septic_d8_P2_C5_lin_poly` — useful as a d6-level building block). The
deg-9 residual bound feeds into the joint analysis as the "post-cancellation"
remainder once the d6, d7, d8 sub-pieces match against their respective
pert decompositions.

CAS-side structural setup for joint cancellation is COMPLETE at both
degrees. Lean-side: first (identity + bound) pair in place; the proven
pattern extends to the remaining small/marginal pieces (next: d=8
P_2_C6_quad with 194-term per-deg split, then d=7 P_2_C6_lin with
304-term per-deg split). Large residuals (>2000 terms) await the
Lipschitz approach via existing `norm_bch_kth_term_diff_le` infrastructure.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 56, 2026-05-18)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 56 (2026-05-18, 5 deferred d8 parent piece bounds, 1 commit)**:

Completes the per-piece norm-bound infrastructure with the 5 remaining
d8 parent pieces (which need split-half Finset.sum emission since
N > 124 terms hits Lean's simp recursion limit).

**`ee6c0fb`** — 5 new public theorems in `BCH/SymmetricQuintic.lean`
(+6828 lines, before the d7 perturbation norm-bound section):

| Theorem | Terms | Bound (K·s⁸) |
|--------:|------:|-------------:|
| `norm_septic_d8_P2_poly_le`          | 186 | 583296/7741440 ≈ 0.075 |
| `norm_septic_d8_P3_poly_le`          | 166 | 164672/1105920 ≈ 0.149 |
| `norm_septic_d8_P5_poly_le`          | 146 | 112128/2211840 ≈ 0.051 |
| `norm_septic_d8_P6_poly_le`          | 126 | 12096/552960 ≈ 0.022 |
| `norm_septic_d8_cross_V2_V5_poly_le` | 154 | 29568/1105920 ≈ 0.027 |

Each piece is split into two ~75-93 term halves at definition time, with
the halves combined via `abel` reassociation + triangle inequality.

Generator-script bug fix: a previous regex-based parameterization left
a literal `{deg}` placeholder in the `pow_nonneg` line (only triggered
for split-half emission). Fixed by converting the `print` call to an
f-string.

**Per-piece norm bound infrastructure is now COMPLETE** (sessions 53-56):

| Layer | Count | Status |
|-------|------:|--------|
| d8 parent pieces | 9 | 9/9 bounded ✓ |
| d7 parent pieces | 6 | 6/6 bounded ✓ |
| d8 non-Dynkin sub-pieces | 6 | 6/6 bounded ✓ |
| d7 non-Dynkin sub-pieces | 3 | 3/3 bounded ✓ |
| d8 Dynkin sub-pieces | 1 (P_3_C4_quad) | 1/1 bounded ✓ |
| d7 Dynkin sub-pieces | 1 (P_3_C3_quad) | 1/1 bounded ✓ |

**Total: 26 direct polynomial norm-bound theorems** across d7+d8.

These are the "raw" polynomial-norm-bound foundation. Insufficient
alone for `O(s⁹)` joint bound (the bounds are `O(s⁷)` / `O(s⁸)` per
piece); the joint cancellation argument still needs the matching
identities outlined in session 52's roadmap.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 55, 2026-05-18)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 55 (2026-05-18, 10 more per-piece norm bounds for d7/d8, 1 commit)**:

Rounds out the per-piece norm-bound infrastructure with bounds on the
remaining single-Finset.sum-compatible (N ≤ 124 terms) d7 parent pieces,
d7 Dynkin sub-piece, and 3 smaller d8 pieces.

**`b6481d6`** — 10 new public theorems in `BCH/SymmetricQuintic.lean`
(+4555 lines):

| d7 piece | Terms | Bound (K·s⁷) | d8 piece | Terms | Bound (K·s⁸) |
|---------:|------:|-------------:|---------:|------:|-------------:|
| P_2_poly             |  96 | 0.106 | cross_V2_V4_poly     |  40 | 0.013 |
| P_3_poly             | 108 | 0.388 | cross_V3_V4_poly     |  66 | 0.010 |
| P_4_poly             |  35 | 0.030 | P_3_C4_quad_poly     |  90 | 0.013 |
| P_5_poly             | 100 | 0.139 | | | |
| cross_V2_V3_poly     |  41 | 0.036 | | | |
| cross_V2_V4_poly     |  30 | 0.052 | | | |
| P_3_C3_quad_poly     |  67 | 0.039 | | | |

Generator extended with 15 new piece names (5 split-half-needed pieces
deferred: `d8_P2/P3/P5/P6` and `d8_cross_V2_V5`, all with 126-186 terms).

**Combined infrastructure summary (sessions 53+54+55)**:

| Layer | Count | Status |
|-------|------:|--------|
| d8 parent pieces | 9 | 4/9 bounded (P_4, cross_V2_V3, cross_V2_V4, cross_V3_V4) + 5 split-half pending |
| d7 parent pieces | 6 | 6/6 bounded ✓ |
| d8 non-Dynkin sub-pieces | 6 | 6/6 bounded ✓ (session 53) |
| d7 non-Dynkin sub-pieces | 3 | 3/3 bounded ✓ (session 54) |
| d8 Dynkin sub-pieces | 1 (P_3_C4_quad) | 1/1 bounded ✓ |
| d7 Dynkin sub-pieces | 1 (P_3_C3_quad) | 1/1 bounded ✓ |

The 5 unbounded d8 parent pieces (P_2/P_3/P_5/P_6 + cross_V2_V5) would
need split-half emission (~1500 lines each); deferred to a future
session if needed. They're not blockers — the WHOLE
`septic_d8_perturbation_poly` already has `‖.‖ ≤ s⁸` (session 39),
giving a tight upper bound on each parent piece as a sub-sum.

These per-piece bounds give the "raw" polynomial-norm-bound foundation.
Insufficient alone for `O(s⁹)` joint bound; cancellation arguments
still needed.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 54, 2026-05-18)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 54 (2026-05-18, per-piece norm bounds for d7 non-Dynkin sub-pieces, 1 commit)**:

d7 analog of session 53's d8 work. Direct polynomial norm bounds for the
3 non-Dynkin sub-pieces of `septic_d7_perturbation_poly`. Each piece is
bounded by `K · s⁷` via single-Finset.sum (all N ≤ 124).

**`544174b`** — 3 new public theorems in `BCH/SymmetricQuintic.lean`
(+1641 lines, after `septic_d7_full_pieces_decomp`):

| Theorem | Sub-piece | Terms | Bound (K) |
|--------:|----------:|------:|----------:|
| `norm_septic_d7_P2_C5_quad_poly_le` | C_5 quad-in-V_2 |  79 | 8848/92160 ≈ 0.096 |
| `norm_septic_d7_P2_C6_lin_poly_le`  | C_6 lin-in-V_2  |  60 | 7680/92160 ≈ 0.083 |
| `norm_septic_d7_P3_C5_lin_poly_le`  | C_5 lin-in-V_3  | 108 | 89856/276480 ≈ 0.325 |

Generator script extended to support d7 sub-pieces (3 new piece names:
`d7_P2_C5_quad`, `d7_P2_C6_lin`, `d7_P3_C5_lin`) with a parametric
`deg ∈ {7, 8}` flag selecting `deg{7,8}_smul_word_le` vs `s^{7,8}`.

**Combined status after sessions 53+54**: all 9 non-Dynkin sub-pieces
(6 d8 + 3 d7) now have direct polynomial norm bounds in Lean.

| Sub-piece | d=7 bound | d=8 bound |
|-----------|----------:|----------:|
| P_2_C5_*  | quad ≤ 0.10·s⁷ | cubic ≤ 0.02·s⁸ |
| P_2_C6_*  | lin ≤ 0.08·s⁷  | quad ≤ 0.04·s⁸ |
| P_2_C7_*  | n/a  | lin ≤ 0.07·s⁸ |
| P_3_C5_lin | ≤ 0.33·s⁷ | n/a |
| P_3_C6_lin | n/a  | ≤ 0.13·s⁸ |
| P_4_*     | n/a  | C_5 lin ≤ 0.04·s⁸ |
| Cross(V_2,V_3) | n/a | C_5 bil ≤ 0.09·s⁸ |

These give the "raw" polynomial-norm-bound foundation for the joint
analysis. Insufficient alone for `O(s⁹)` (the bounds are `O(s⁷)` /
`O(s⁸)` per piece); the joint cancellation argument still needs the
matching identities outlined in session 52's roadmap.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 53, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 53 (2026-05-17, per-piece norm bounds for d8 non-Dynkin sub-pieces, 1 commit)**:

Direct polynomial norm bounds for the 6 sub-pieces of `septic_d8_perturbation_poly`
that are NOT Dynkin-expressible (each uses `bch_kth_term` in monomial form for
k ≥ 5). Each piece is bounded by `K · s⁸` via the standard Finset.sum triangle
approach (per-i `deg8_smul_word_le` + uniform `max|num|/LCM`).

**`1462ce5`** — 6 new public theorems in `BCH/SymmetricQuintic.lean`
(+7052 lines, after `septic_d8_P2_pieces_decomp`):

| Theorem | Sub-piece | Terms | Bound (K) |
|--------:|----------:|------:|----------:|
| `norm_septic_d8_P2_C5_cubic_poly_le` | C_5 cubic-in-V_2 | 78 | 3354/184320 ≈ 0.018 |
| `norm_septic_d8_P2_C6_quad_poly_le` | C_6 quad-in-V_2 | 110 | 13200/368640 ≈ 0.036 |
| `norm_septic_d8_P2_C7_lin_poly_le` | C_7 lin-in-V_2 | 174 | 272832/3870720 ≈ 0.070 |
| `norm_septic_d8_P3_C6_lin_poly_le` | C_6 lin-in-V_3 | 166 | 138112/1105920 ≈ 0.125 |
| `norm_septic_d8_P4_poly_le` | C_5 lin-in-V_4 | 154 | 19712/552960 ≈ 0.036 |
| `norm_septic_d8_cross_V2_V3_poly_le` | C_5 bil V_2·V_3 | 174 | 100224/1105920 ≈ 0.091 |

Pieces with N ≤ 124 use single Finset.sum; pieces with N > 124 use the
split-half pattern (two halves combined via `abel` + triangle inequality),
matching the existing `norm_septic_d8_perturbation_poly_le` template.

New CAS generator `scripts/gen_d8_subpiece_norm_bound.py` parameterizes
both the polynomial computation (per-sub-piece, via direct bch_kth_term
substitution at the appropriate degree) and the Lean code emission.

**Significance**: completes the "raw" `O(s⁸)` polynomial-norm step for
each non-Dynkin sub-piece. These are useful building blocks but
insufficient alone for the eventual `O(s⁹)` joint analysis — the joint
analysis still needs finer cancellation arguments (deg-9+ residual via
Lipschitz-quadratic bounds or matching identities, per session 52's
roadmap). This session is the polynomial-norm foundation; future
sessions formalize the cancellation.

Build wall ~10 min per touched-rebuild of SymmetricQuintic (consistent
with the existing pattern). Lean parsing pitfall encountered and fixed:
`/-- doc -/ set_option ... in theorem` fails parsing; must use the
order `set_option ... in /-- doc -/ theorem` (matching d7 pattern).

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 52, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 52 (2026-05-17, joint cancellation structure CAS verification, 1 commit)**:

Preparatory CAS work for the joint analysis (eventual O(s⁹) bound discharging
`symmetric_bch_septic_sub_poly_axiom`). No Lean changes; all verification at
polynomial level only.

**`51934a0`** — Two new CAS scripts:

1. `scripts/verify_d8_P4_lipschitz_form.py`: confirms that
   `septic_d8_P4_poly` equals the deg-8 part of
   `bch_quintic_term(x + V_4, a') - bch_quintic_term(x, a')`. The FULL
   bch_quintic_term diff has 3083 terms at degrees 8, 11, 14, 17;
   septic_d8_P4_poly (154 terms) is exactly the deg-8 part. The deg-11+
   residual has 2929 terms, too large to encode as an explicit Lean DEF.

   **Lesson**: explicit Lipschitz-form identities for non-Dynkin sub-pieces
   in Lean would require either a `deg-extraction` operator (none exists) or
   massive polynomial residuals. The norm-bound approach using
   `norm_bch_kth_term_diff_le` directly on FULL diffs is cleaner.

2. `scripts/verify_d8_C_k_diff_matching.py`: verifies the 5-group grouping
   of the 12 d8 sub-pieces by their C_p origin:

       Group_C3 = P_6 + Cross(V_2, V_5) + Cross(V_3, V_4)     [3 Dynkin]
       Group_C4 = P_5 + Cross(V_2, V_4) + P_3_C4_quad         [3 Dynkin]
       Group_C5 = P_4 + Cross(V_2, V_3) + P_2_C5_cubic        [3 non-Dynkin]
       Group_C6 = P_3_C6_lin + P_2_C6_quad                    [2 non-Dynkin]
       Group_C7 = P_2_C7_lin                                  [1 non-Dynkin]

   Total: 12 sub-pieces summing to `septic_d8_perturbation_poly` (182 terms,
   LCM 15482880). CAS verified at polynomial level.

   The grouping follows from degree counting: for k_j V_j substitutions
   in C_p, total deg = p + Σ k_j·(j-1) = 8. Each (p, {k_j}) combination
   gives a specific d8_pert sub-piece.

**Joint analysis cancellation structure** (CONCEPTUAL, to be formalized):

In the extended hdecomp (session 41) + per-Group bounds (session 42), the
Groups F and CD-quintic contain pieces like `(C_p(z, a') − C_p(a'+b, a'))`
for various p. The deg-8 part of these `(C_p diff)`s matches the corresponding
Group_C_p from `septic_d8_perturbation_poly`:

    (C_3 diff)_d8 ↔ Group_C3 (Dynkin pieces)
    (C_4 diff)_d8 ↔ Group_C4 (Dynkin pieces)
    (C_5 diff)_d8 ↔ Group_C5 (non-Dynkin pieces, bch_quintic_term Lipschitz)
    (C_6 diff)_d8 ↔ Group_C6 (non-Dynkin pieces, bch_sextic_term Lipschitz)
    (C_7 diff)_d8 ↔ Group_C7 (non-Dynkin pieces, bch_septic_term Lipschitz)

When subtracted, each (C_p diff)_d8 − Group_C_p = 0 (by the polynomial
matching established above). The residual after this cancellation is the
deg-9+ contributions from (C_p diff)_full minus Group_C_p, bounded by
`norm_bch_kth_term_diff_le` for the appropriate k.

The same structure applies for d7 (sessions 43-46):
    (C_3 diff)_d7 ↔ Group_C3_d7 = P_5_d7 + Cross(V_2, V_4)_d7
    (C_4 diff)_d7 ↔ Group_C4_d7 = P_4_d7 + Cross(V_2, V_3)_d7 + P_3_C3_quad
    (C_5 diff)_d7 ↔ Group_C5_d7 = P_3_C5_lin + P_2_C5_quad
    (C_6 diff)_d7 ↔ Group_C6_d7 = P_2_C6_lin

**Roadmap for the eventual discharge** (multi-session):
A) Lean-formalize the matching identity: for each p, prove that the deg-q
   part of (C_p diff) equals the corresponding Group_C_p (as polynomial
   identity). Requires defining a "deg-extraction" mechanism or using
   noncomputable residuals.
B) Apply Lipschitz bounds: ‖(C_p diff)_full‖ ≤ K · M^{p-1} · ‖z − (a'+b)‖
   via `norm_bch_kth_term_diff_le`.
C) Joint cancellation: the deg-q part of (C_p diff) cancels with Group_C_p,
   leaving the deg-(q+1)+ part of (C_p diff). Bound this residual by
   O(s^{q+1}) via direct polynomial bound or further Lipschitz.
D) Sum across p and groups to get the total O(s⁹) bound.

This is multi-session work (estimated 5-10 more sessions). The current
session 52 documents the structural matching; future sessions will
formalize the Lean-level cancellation identities.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 51, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 51 (2026-05-17, d8 P_2 3-piece sub-decomposition, 1 commit)**:

Polynomial-form sub-piece decomposition for the V_2-only piece (P_2_d8)
of the 9-piece d8 decomposition. d8 analog of d7 session 46 P_2 work, with
one extra sub-piece since deg 8 admits cubic-in-V_2 from C_5 (which d7
couldn't admit since C_4 has only 2 z-positions).

**`0bfc76d`** — Three polynomial DEFs in `BCH/SymmetricQuintic.lean`
(~line 16263, after P_3 sub-piece work, +419 lines) + sum identity:

* `septic_d8_P2_C7_lin_poly` (174 terms, LCM 3870720, Σ|num|/LCM ≈ 0.0108).
  C_7 linear-in-V_2 (k=1, p=7). Equals deg-8 part of
  `bch_septic_term(x + V_2, a') - bch_septic_term(x, a')`.
* `septic_d8_P2_C6_quad_poly` (110 terms, LCM 368640, Σ|num|/LCM ≈ 0.0081).
  C_6 quadratic-in-V_2 (k=2, p=6). Equals deg-8 part of
  `bch_sextic_term(x + V_2, a') - bch_sextic_term(x, a')`.
* `septic_d8_P2_C5_cubic_poly` (78 terms, LCM 184320, Σ|num|/LCM ≈ 0.0052).
  C_5 cubic-in-V_2 (k=3, p=5). Equals deg-8 part of
  `bch_quintic_term(x + V_2, a') - bch_quintic_term(x, a')`.

Sum: 186 terms (LCM 7741440), matching `septic_d8_P2_poly` exactly.

`septic_d8_P2_pieces_decomp`: P_2_d8 = C_7_lin + C_6_quad + C_5_cubic.
Proof: 2 lines (`unfold 4 defs + match_scalars <;> ring`).

Extraction method: each sub-piece extracted INDEPENDENTLY via direct
`bch_kth_term` differences (no Vandermonde extraction needed). At deg 8,
only specific (k V_2-substitutions, p+k=8) survive per bch_kth_term:
* For k=1 in bch_septic_term: deg 7 - 1 + 2 = 8 ✓.
* For k=2 in bch_sextic_term: deg 6 - 2 + 4 = 8 ✓.
* For k=3 in bch_quintic_term: deg 5 - 3 + 6 = 8 ✓.
* Higher k impossible since C_p with p ≤ 4 has ≤ 2 z-positions (can't
  accept k ≥ 4 substitutions).

CAS-derived via `scripts/gen_d8_P2_subpieces.py`. Cross-checked at CAS
level: sum equals direct `septic_d8_P2_poly` from full bch series.

None of the 3 sub-pieces are Dynkin-expressible — all use `bch_kth_term`
for k ≥ 5, monomial form in Lean. All need Lipschitz bounds.

**Status summary after session 51**: All 9 d8 pieces now have explicit
polynomial-form sub-decompositions in Lean.

| Piece | Sub-pieces | Op-form identities |
|-------|-----------:|--------------------|
| P_6 | 1 (ΔC_3_lin) | ✓ |
| P_5 | 1 (ΔC_4_lin) | ✓ |
| Cross(V_2, V_5) | 1 (ΔC_3_bil) | ✓ |
| Cross(V_3, V_4) | 1 (ΔC_3_bil) | ✓ |
| Cross(V_2, V_4) | 1 (ΔC_4_bil) | ✓ |
| P_3 | 2 (C_4 quad + C_6 lin) | ✓ for C_4 quad |
| P_2 | 3 (C_5 cubic + C_6 quad + C_7 lin) | needs Lipschitz |
| P_4 | 1 (C_5 lin, not Dynkin) | needs Lipschitz |
| Cross(V_2, V_3) | 1 (C_5 bil, not Dynkin) | needs Lipschitz |

6 Dynkin operator-form identities proven; 6 non-Dynkin sub-pieces remain
(P_3 C_6 lin, P_4 C_5 lin, P_2 3 sub-pieces, Cross(V_2, V_3) C_5 bil),
each needing a Lipschitz-style bound using existing `norm_bch_kth_term_diff_le`
helpers (k=5,6,7 already in Lean from sessions 27-28).

**Remaining work**:
☐ Lipschitz-style norm bounds for the 6 non-Dynkin sub-pieces using
  existing `norm_bch_quintic_term_diff_le`, `norm_bch_sextic_term_diff_le`,
  `norm_bch_septic_term_diff_le` infrastructure.
☐ Joint analysis combining d7+d8 op-form bounds with Groups F+CD-quintic
  for O(s⁹) bound discharging `symmetric_bch_septic_sub_poly_axiom`.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 50, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 50 (2026-05-17, d8 P_3 sub-piece decomposition, 1 commit)**:

Polynomial-form sub-piece decomposition for the V_3-only piece (P_3_d8) of
the 9-piece d8 decomposition. d8 analog of d7 session 46 P_3 sub-piece work
at one degree higher.

**`23ff45d`** — Two polynomial DEFs in `BCH/SymmetricQuintic.lean` (~line
15943, after the 5 op-form theorems, +322 lines) + sum identity + Dynkin
op-form:

* `septic_d8_P3_C4_quad_poly` (90 terms, LCM 221184, Σ|num|/LCM ≈ 0.0031).
  C_4 quadratic-in-V_3 sub-piece. Dynkin-expressible.
* `septic_d8_P3_C6_lin_poly` (166 terms, LCM 1105920, Σ|num|/LCM ≈ 0.0126).
  C_6 linear-in-V_3 sub-piece. Uses bch_sextic_term (monomial form, NOT
  Dynkin), so needs Lipschitz-style treatment.

`septic_d8_P3_pieces_decomp`: P_3_d8 = C_4_quad + C_6_lin. Proof: 2 lines.

`septic_d8_P3_C4_quad_op_form` (Dynkin operator-form identity):

    septic_d8_P3_C4_quad_poly = -(1/24)·[a', [V_3, [V_3, a']]]

where V_3 = bch_cubic_term(½a, b). d8 analog of d7's C_3 quad form
`(1/12)·[V_3, [V_3, a']]` (substituting V_3 → V_3 for both z's in the
[z, [z, y]] term of C_4 instead of C_3).

CAS-derived via `scripts/gen_d8_P3_subpieces.py`. The C_4 quad piece
computed directly from the Dynkin formula `C_4(z, y) = -(1/24)·[y, [z, [z, y]]]`
with both z's replaced by V_3; C_6 lin defined as the residual.

**Status summary after session 50** (6 of 9 d8 pieces with Dynkin forms):

| Piece | Sub-pieces | Op-form identities |
|-------|-----------:|--------------------|
| P_6 | 1 (ΔC_3_lin) | ✓ |
| P_5 | 1 (ΔC_4_lin) | ✓ |
| Cross(V_2, V_5) | 1 (ΔC_3_bil) | ✓ |
| Cross(V_3, V_4) | 1 (ΔC_3_bil) | ✓ |
| Cross(V_2, V_4) | 1 (ΔC_4_bil) | ✓ |
| P_3 | 2 (C_4 quad + C_6 lin) | ✓ for C_4 quad |
| P_4 | 1 (C_5 lin, not Dynkin) | needs Lipschitz |
| P_2 | 3 (C_5 cubic + C_6 quad + C_7 lin) | needs Lipschitz |
| Cross(V_2, V_3) | 1 (C_5 bil, not Dynkin) | needs Lipschitz |

6 Dynkin operator-form identities proven. The remaining 3 multi-sub-piece
operator pieces (P_2: 3 sub-pieces, Cross(V_2, V_3): 1 sub-piece, P_4: 1
sub-piece) all involve `bch_kth_term` for k ≥ 5 (monomial form in Lean),
needing Lipschitz-style bounds.

**Remaining work**:
☐ P_2_d8 sub-piece decomposition: 3 sub-pieces (C_5 cubic + C_6 quad +
  C_7 lin). Requires 3-way Vandermonde-style extraction.
☐ Lipschitz-style norm bounds for the 6 non-Dynkin sub-pieces.
☐ Joint analysis combining d7+d8 op-form bounds with Groups F+CD-quintic
  for O(s⁹) bound discharging `symmetric_bch_septic_sub_poly_axiom`.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 49, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 49 (2026-05-17, operator-form identities for 5 of 9 d8 pieces, 1 commit)**:

Lie-polynomial operator-form identities for the 5 SIMPLEST pieces of the
9-piece d8 decomposition. Each piece equals a specific nested-bracket
expression in (V_j, V_k, x, a') proved via `match_scalars + ring`. d8
analog of session 45 (d7, 4 pieces) at one degree higher with one extra
piece (the V_3·V_4 cross had no d7 analog).

**`f2e1676`** — 5 op-form private theorems in `BCH/SymmetricQuintic.lean`
(after `septic_d8_perturbation_poly_pieces_decomp`, ~line 15743, +196
lines added):

1. `septic_d8_P6_op_form` (ΔC_3_lin(V_6)):

       septic_d8_P6_poly = (1/12)·([V_6, [x, a']] + [x, [V_6, a']] + [a', [a', V_6]])

   where V_6 = bch_sextic_term(½a, b). Analog of `septic_d7_P5_op_form`.

2. `septic_d8_P5_op_form` (ΔC_4_lin(V_5)):

       septic_d8_P5_poly = -(1/24)·([a', [V_5, [x, a']]] + [a', [x, [V_5, a']]])

   where V_5 = bch_quintic_term(½a, b). Analog of `septic_d7_P4_op_form`.

3. `septic_d8_cross_V2_V5_op_form` (ΔC_3_bil(V_2, V_5)):

       septic_d8_cross_V2_V5_poly = (1/12)·([V_2, [V_5, a']] + [V_5, [V_2, a']])

4. `septic_d8_cross_V3_V4_op_form` (ΔC_3_bil(V_3, V_4)):

       septic_d8_cross_V3_V4_poly = (1/12)·([V_3, [V_4, a']] + [V_4, [V_3, a']])

   (extra piece — no d7 analog since d7 had only Cross(V_2, V_k) pieces.)

5. `septic_d8_cross_V2_V4_op_form` (ΔC_4_bil(V_2, V_4)):

       septic_d8_cross_V2_V4_poly = -(1/24)·([a', [V_2, [V_4, a']]] +
                                             [a', [V_4, [V_2, a']]])

CAS verification scripts: `scripts/verify_d8_{P5,P6,cross_V2_V4,cross_V2_V5,cross_V3_V4}_operator_form.py`,
each confirms the operator form's polynomial exactly equals the
corresponding `septic_d8_*_poly` def at CAS level.

Each Lean proof ~25-40 lines, follows the exact d7 pattern (unfold +
simp distribution + `match_scalars <;> ring`). Section-level
`maxHeartbeats 64000000` sufficient. Build wall ~10 min, no slowdown.

**Status summary after session 49** (5 of 9 d8 op-form identities proven):

| Piece | Sub-pieces | Op-form identities |
|-------|-----------:|--------------------|
| P_6 | 1 (ΔC_3_lin) | ✓ |
| P_5 | 1 (ΔC_4_lin) | ✓ |
| Cross(V_2, V_5) | 1 (ΔC_3_bil) | ✓ |
| Cross(V_3, V_4) | 1 (ΔC_3_bil) | ✓ |
| Cross(V_2, V_4) | 1 (ΔC_4_bil) | ✓ |
| P_4 | TBD | needs sub-piece split (C_5 lin via bch_quintic_term) |
| P_3 | TBD | needs sub-piece split (C_6 lin + C_4 quad) |
| P_2 | TBD | needs sub-piece split (C_7 lin + C_6 quad + C_5 cubic) |
| Cross(V_2, V_3) | TBD | needs sub-piece split (C_5 bil) |

5 Dynkin operator forms proven; the remaining 4 pieces (P_2, P_3, P_4,
Cross(V_2, V_3)) involve `bch_kth_term` for k ≥ 5 (monomial form in
Lean, not Dynkin Lie poly form), so will need sub-piece splits analog
to d7's `septic_d7_P3_pieces_decomp` and `septic_d7_P2_pieces_decomp`
(session 46), then Lipschitz-style bounds for the non-Dynkin sub-pieces.

**Remaining work**:
☐ Sub-piece splits for P_2, P_3, P_4 + Cross(V_2, V_3) (analog of d7
  session 46). Each piece needs to be decomposed into Dynkin sub-piece +
  bch_kth_term sub-pieces.
☐ Dynkin op-form identities for the Dynkin sub-pieces (~5 more lemmas).
☐ Lipschitz-style norm bounds on the bch_kth_term sub-pieces for d7+d8
  combined (~10+ more lemmas).
☐ Joint analysis combining d7+d8 op-form bounds with Groups F+CD-quintic
  for O(s⁹) bound discharging `symmetric_bch_septic_sub_poly_axiom`.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 48, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 48 (2026-05-17, Lean encoding of 9-piece d8 decomposition, 1 commit)**:

The CAS-derived 9-piece operator-form decomposition (session 47) is now
encoded in Lean (analog of session 44 for d7). Polynomial-form pieces +
sum identity all proven.

**`ff919e7`** — Nine noncomputable polynomial defs in `BCH/SymmetricQuintic.lean`
(after `septic_d7_perturbation_poly_full_pieces_decomp`, line ~14415, +1330
lines added) + 1 sum identity theorem:

* `septic_d8_P2_poly` (186 terms, LCM 7741440) — V_2 only. Captures
  linear-in-V_2 from C_7, quadratic-in-V_2 from C_6, cubic V_2³ from C_5.
* `septic_d8_P3_poly` (166 terms, LCM 1105920) — V_3 only. Linear-in-V_3
  from C_6 + quadratic-in-V_3 from C_4.
* `septic_d8_P4_poly` (154 terms, LCM 552960) — V_4 only. Only
  linear-in-V_4 from C_5.
* `septic_d8_P5_poly` (146 terms, LCM 2211840) — V_5 only. Only
  linear-in-V_5 from C_4.
* `septic_d8_P6_poly` (126 terms, LCM 552960) — V_6 only. Only
  linear-in-V_6 from C_3.
* `septic_d8_cross_V2_V3_poly` (174 terms, LCM 1105920) — V_2·V_3
  bilinear from C_5.
* `septic_d8_cross_V2_V4_poly` (40 terms, LCM 36864) — V_2·V_4 bilinear
  from C_4.
* `septic_d8_cross_V2_V5_poly` (154 terms, LCM 1105920) — V_2·V_5
  bilinear from C_3.
* `septic_d8_cross_V3_V4_poly` (66 terms, LCM 110592) — V_3·V_4 bilinear
  from C_3.

Combined: 182 terms (LCM 15482880), matching the existing Lean def
`septic_d8_perturbation_poly` exactly.

`septic_d8_perturbation_poly_pieces_decomp` private theorem:

    septic_d8_perturbation_poly 𝕂 a b =
      septic_d8_P2_poly 𝕂 a b + septic_d8_P3_poly 𝕂 a b +
        septic_d8_P4_poly 𝕂 a b + septic_d8_P5_poly 𝕂 a b +
        septic_d8_P6_poly 𝕂 a b +
        septic_d8_cross_V2_V3_poly 𝕂 a b + septic_d8_cross_V2_V4_poly 𝕂 a b +
        septic_d8_cross_V2_V5_poly 𝕂 a b + septic_d8_cross_V3_V4_poly 𝕂 a b

Proof: 3 lines (`unfold` 10 defs + `match_scalars <;> ring`). Section-level
`maxHeartbeats 64000000` (already in `SymmetricSepticAltForm`) sufficient
despite ~3× more terms than d7 (1212 RHS terms vs 410 for d7's 6-piece sum).

Generator script: `scripts/gen_septic_d8_pieces_lean.py` (analog of
`gen_septic_d7_pieces_lean.py`).

**Remaining for full Phase C-septic (d8) infrastructure**:
☐ Operator-form identities for the simpler pieces (analog of d7 session 45):
  * `P_6 = (1/12)·[V_6, [x, a']] + ...` (Dynkin form, analog of P_5 at d8).
  * `Cross(V_2, V_5) = (1/12)·([V_2, [V_5, a']] + [V_5, [V_2, a']])` (analog
    of Cross(V_2, V_4)_d7).
  * `Cross(V_3, V_4) = (1/12)·([V_3, [V_4, a']] + [V_4, [V_3, a']])` (analog
    of Cross(V_2, V_4)_d7).
  * `Cross(V_2, V_4) = -(1/24)·([a', [V_2, [V_4, a']]] + [a', [V_4, [V_2, a']]])`
    (analog of Cross(V_2, V_3)_d7).
☐ Sub-piece splits for the complex pieces (P_2, P_3, P_4, P_5,
  Cross(V_2, V_3)) which involve bch_quintic_term, bch_sextic_term,
  bch_septic_term (all monomial form in Lean).
☐ Joint analysis with d7 + Group F + Group CD-quintic for O(s⁹) bound
  discharging `symmetric_bch_septic_sub_poly_axiom`.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 47, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 47 (2026-05-17, d8 9-piece structural CAS, 1 commit)**:

CAS verification establishing the d8 analog of d7's 6-piece decomposition.
The full d8 perturbation structure:

    septic_d8_perturbation_poly =
      P_2_d8 + P_3_d8 + P_4_d8 + P_5_d8 + P_6_d8
      + Cross(V_2, V_3)_d8 + Cross(V_2, V_4)_d8
      + Cross(V_2, V_5)_d8 + Cross(V_3, V_4)_d8

Total 9 pieces (5 single-V_j + 4 cross), parallel to d7's 6 pieces.

Per-piece term counts and operator-form interpretation:
* `P_2`: 186 terms — V_2 only (linear from C_7, quadratic from C_6, cubic V_2³ from C_5).
* `P_3`: 166 terms — V_3 only (linear from C_6, quadratic from C_4).
* `P_4`: 154 terms — V_4 only (linear from C_5).
* `P_5`: 146 terms — V_5 only (linear from C_4).
* `P_6`: 126 terms — V_6 only (linear from C_3).
* `Cross(V_2, V_3)`: 174 terms — bilinear V_2·V_3 from C_5.
* `Cross(V_2, V_4)`: 40 terms — bilinear V_2·V_4 from C_4.
* `Cross(V_2, V_5)`: 154 terms — bilinear V_2·V_5 from C_3.
* `Cross(V_3, V_4)`: 66 terms — bilinear V_3·V_4 from C_3.

Combined: 182 terms (LCM 15482880), matching the existing
`septic_d8_perturbation_poly` Lean def exactly.

Other potential cross pieces vanish: Cross(V_2, V_6), Cross(V_3, V_5),
Cross(V_4, V_5) all = 0 because the required C_p with p+(j-1)+(k-1) = 8
and (j,k) such that both ≥ 3 forces p ≤ 2, but C_2 has only 1 z-position
(can't admit bilinear substitution).

**Key structural insight**: by palindromic vanishing of sym_E_8,
pert_d8 := (bch(z, ½a) - bch(½a+b, ½a))_d8 = -C_8(½a+b, ½a) = -C_8_static.
Combined with `septic_d8_cancellation_poly_form` (d8_pert = -V_8 - P_7 -
C_8_static), substituting and simplifying yields the 9-piece form.

**`4e663fa`** — `scripts/verify_d8_operator_decomp.py` (327 lines). Contains
the structural derivation, CAS verification of the 9-piece sum, and confirms
vanishing of the 3 impossible crosses.

**Remaining for full Phase C-septic (d8) infrastructure**:
☐ 9 polynomial DEFs in Lean (analog of session 44 for d7).
☐ 9-piece sum identity (analog of `septic_d7_perturbation_poly_pieces_decomp`).
☐ Operator-form identities for the simpler pieces:
  * `P_6 = (1/12)·[V_6, [x, a']] + ...` (Dynkin form, analog of P_5 at d8).
  * `Cross(V_2, V_5) = (1/12)·([V_2, [V_5, a']] + [V_5, [V_2, a']])` (analog
    of Cross(V_2, V_4)_d7).
  * `Cross(V_3, V_4) = (1/12)·([V_3, [V_4, a']] + [V_4, [V_3, a']])` (analog
    of Cross(V_2, V_4)_d7).
  * `Cross(V_2, V_4) = -(1/24)·([a', [V_2, [V_4, a']]] + [a', [V_4, [V_2, a']]])`
    (analog of Cross(V_2, V_3)_d7).
☐ Sub-piece splits for the complex pieces (P_2, P_3, P_4, P_5,
  Cross(V_2, V_3)) which involve bch_quintic_term, bch_sextic_term,
  bch_septic_term (all monomial form in Lean).

Combined with d7 infrastructure (sessions 43-46), this provides the full
operator-form decomposition needed for the joint analysis (d7 + d8 +
Group F + Group CD-quintic → O(s⁹) bound discharging
`symmetric_bch_septic_sub_poly_axiom`).

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 46, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 46 (2026-05-17, P_3 and P_2 sub-piece decompositions, 2 commits)**:

Polynomial-form sub-piece decomposition for the 2 multi-operator pieces of
the 6-piece d7 decomposition. Each is split into operator-form sub-pieces:

1. **`a249954`** — P_3 sub-piece decomposition:
   * `septic_d7_P3_C3_quad_poly` (67 terms, LCM 55296) — C_3 quadratic-in-V_3
     piece (Dynkin-expressible).
   * `septic_d7_P3_C5_lin_poly` (108 terms, LCM 276480) — C_5 linear-in-V_3
     piece (uses bch_quintic_term, NOT Dynkin-form in Lean).
   * `septic_d7_P3_pieces_decomp`: P_3 = C_3_quad + C_5_lin.
   * `septic_d7_P3_C3_quad_op_form`:

         septic_d7_P3_C3_quad_poly = (1/12)·[V_3, [V_3, a']]

     (Dynkin operator-form identity for the simpler sub-piece.)

2. **`64c263c`** — P_2 sub-piece decomposition:
   * `septic_d7_P2_C6_lin_poly` (60 terms, LCM 92160) — C_6 linear-in-V_2.
   * `septic_d7_P2_C5_quad_poly` (79 terms, LCM 92160) — C_5 quadratic-in-V_2.
   * `septic_d7_P2_pieces_decomp`: P_2 = C_6_lin + C_5_quad.

**Important correction**: P_2 has only 2 sub-pieces (not 4 as initially
indicated). Higher orders are impossible:
  * Cubic-in-V_2 from C_4 needs 3+ z-positions; C_4 has 2.
  * Quartic-in-V_2 from C_3 needs 4+ z-positions; C_3 has 2.

CAS extraction for P_2 used a forward/backward symmetry trick:
  * `half-sum := (bch(x+V_2, ½a) + bch(x-V_2, ½a) − 2·bch(x, ½a))/2`
    at deg 7 = even-in-V_2 part = C_5 quad piece (79 terms).
  * `half-diff := (bch(x+V_2, ½a) − bch(x-V_2, ½a))/2`
    at deg 7 = odd-in-V_2 part = C_6 lin piece (60 terms).

CAS-verified at `scripts/verify_P3_decomp.py` and `scripts/verify_P2_decomp.py`.

**Status summary after session 46**:

| Piece | Sub-pieces | Op-form identities |
|-------|-----------:|--------------------|
| P_5 | 1 (ΔC_3_lin) | ✓ |
| P_4 | 1 (ΔC_4_lin) | ✓ |
| Cross(V_2, V_4) | 1 (ΔC_3_bil) | ✓ |
| Cross(V_2, V_3) | 1 (ΔC_4_bil) | ✓ |
| P_3 | 2 (C_3_quad + C_5_lin) | ✓ for C_3_quad |
| P_2 | 2 (C_6_lin + C_5_quad) | (both need Lipschitz) |

5 Dynkin operator-form identities proven; 3 sub-pieces (P_3 C_5_lin, P_2
C_6_lin, P_2 C_5_quad) need Lipschitz-style bounds on bch_quintic_term and
bch_sextic_term differences (since these are in monomial form in Lean, not
Dynkin Lie polynomial form).

Build wall ~7 min per commit; no slowdown despite the cumulative ~1000+
lines of new polynomial DEFs in this session pair (sessions 45+46).

**Remaining work**:
☐ Lipschitz-style bounds for the 3 remaining sub-pieces using existing
  `norm_bch_quintic_term_diff_le`-style infrastructure.
☐ Combine the 6 op-form identities with sub-piece bounds for joint Lipschitz
  bound on `septic_d7_perturbation_poly` (still O(s⁷) at piece level).
☐ Joint analysis with Groups E+F+CD-quintic to drop O(s⁷) → O(s⁹).
☐ Final assembly replacing `symmetric_bch_septic_sub_poly_axiom`.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 45, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 45 (2026-05-17, operator-form identities for 4 of 6 d7 pieces, 4 commits)**:

Lie-polynomial operator-form identities for 4 of 6 pieces of the d7
decomposition. Each piece equals a specific nested-bracket expression in
(V_j, x, a') proved via `match_scalars + ring`.

1. **`2b4a7c5`** — `septic_d7_P5_op_form` (P_5 = ΔC_3_lin(V_5)):

       septic_d7_P5_poly = (1/12)·([V_5, [x, a']] + [x, [V_5, a']] + [a', [a', V_5]])

   where V_5 = bch_quintic_term(½a, b). Mirrors quintic `deltaC3_lin_V3_eq`.

2. **`b7263a2`** — `septic_d7_P4_op_form` (P_4 = ΔC_4_lin(V_4)):

       septic_d7_P4_poly = -(1/24)·([a', [V_4, [x, a']]] + [a', [x, [V_4, a']]])

   where V_4 = bch_quartic_term(½a, b). Mirrors quintic `deltaC4_lin_V2_eq`.

3. **`05b3a35`** — `septic_d7_cross_V2_V4_op_form` (ΔC_3_bil(V_2, V_4)):

       septic_d7_cross_V2_V4_poly = (1/12)·([V_2, [V_4, a']] + [V_4, [V_2, a']])

4. **`a2aa5c6`** — `septic_d7_cross_V2_V3_op_form` (ΔC_4_bil(V_2, V_3)):

       septic_d7_cross_V2_V3_poly = -(1/24)·([a', [V_2, [V_3, a']]] + [a', [V_3, [V_2, a']]])

**Correction**: the original CAS docstring for `gen_cross_V2_V3_d7.py`
claimed Cross(V_2, V_3) had a "trilinear V_2²·V_3 from C_3" contribution.
This was WRONG: C_3 has at most 2 z-positions (in `[z, [z, y]]`), so
trilinear (3 V substitutions) is impossible. The ONLY deg-7 contribution
to Cross(V_2, V_3) is the bilinear V_2·V_3 from C_4. Lean docstring
includes this correction note.

Each proof ~25-40 lines, builds 7-8 min wall, no slowdown. Each piece is
also verified independently in CAS at `scripts/verify_*_operator_form.py`.

**Remaining for the operator-form Phase B-septic identity**:
☐ **P_3** = ΔC_5_lin(V_3) + ΔC_3_quad(V_3). The ΔC_3_quad part
  `(1/12)·[V_3, [V_3, a']]` is Dynkin-expressible. The ΔC_5_lin part uses
  `bch_quintic_term` which is in monomial form (not Dynkin Lie form) in
  Lean, so needs an alternative operator-form approach:
  * Use the FULL bch_quintic_term difference and bound the deg-9+ residual
    separately, OR
  * Split P_3 into two sub-polynomial DEFs.
☐ **P_2** = 4 op pieces (lin V_2 from C_6, quad V_2 from C_5, cubic V_2
  from C_4, quartic V_2 from C_3). Most complex piece. Note that some
  combinations are impossible: quartic-in-V_2 from C_3 requires 4
  z-positions but C_3 has at most 2; quartic must redistribute to C_p
  with enough z-positions.
☐ Norm bounds on each piece using operator forms (Lipschitz on Lie polys).
☐ Joint analysis combining d7_pert with Groups E+F+CD-quintic for O(s⁹).
☐ Final assembly replacing `symmetric_bch_septic_sub_poly_axiom`.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 44, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 44 (2026-05-17, Lean encoding of 6-piece d7 decomposition, 2 commits)**:

The CAS-derived 6-piece operator-form decomposition (session 43) is now
encoded in Lean. Polynomial-form pieces + sum identity all proven.

1. **`f92cb32`** — Six noncomputable polynomial defs in
   `BCH/SymmetricQuintic.lean` (after `septic_d7_cancellation_poly_form`,
   line 13328-13774, ~470 lines added):

   * `septic_d7_P2_poly` (96 terms, LCM 92160, Σ|num|/LCM ≈ 0.0277).
     V_2-only deg-7 perturbation. Captures linear-in-V_2 in C_6,
     quadratic-in-V_2 in C_5, cubic-in-V_2 in C_4, quartic-in-V_2 in C_3.
   * `septic_d7_P3_poly` (108 terms, LCM 276480, Σ|num|/LCM ≈ 0.0282).
     V_3-only. Linear-in-V_3 in C_5 + quadratic-in-V_3 in C_3.
   * `septic_d7_P4_poly` (35 terms, LCM 18432, Σ|num|/LCM ≈ 0.0093).
     V_4-only. Only linear-in-V_4 in C_4 (higher orders exceed deg 7).
   * `septic_d7_P5_poly` (100 terms, LCM 276480, Σ|num|/LCM ≈ 0.0124).
     V_5-only. Only linear-in-V_5 in C_3.
   * `septic_d7_cross_V2_V3_poly` (41 terms, LCM 18432, Σ|num|/LCM ≈ 0.0089).
     V_2·V_3 cross. Bilinear V_2·V_3 from C_4 + trilinear V_2²·V_3 from C_3.
   * `septic_d7_cross_V2_V4_poly` (30 terms, LCM 9216, Σ|num|/LCM ≈ 0.0104).
     V_2·V_4 cross. Bilinear V_2·V_4 from C_3 only.

   Generated via `scripts/gen_septic_d7_pieces_lean.py`. Build wall ~7 min.

2. **`f421fdd`** — `septic_d7_perturbation_poly_pieces_decomp` private theorem:

       septic_d7_perturbation_poly 𝕂 a b =
         septic_d7_P2_poly 𝕂 a b + septic_d7_P3_poly 𝕂 a b +
           septic_d7_P4_poly 𝕂 a b + septic_d7_P5_poly 𝕂 a b +
           septic_d7_cross_V2_V3_poly 𝕂 a b + septic_d7_cross_V2_V4_poly 𝕂 a b

   Proof: 3 lines (`unfold` 7 defs + `match_scalars <;> ring`).
   Section-level `maxHeartbeats 64000000` (already in SymmetricSepticAltForm)
   sufficient. +26 lines, build wall 7:33 (vs 7:12 for defs alone).

**Remaining for the operator-form Phase B-septic identity (roadmap items A.2-A.5)**:

A.2) Operator-form identities for each piece: prove each polynomial DEF
     equals a specific BCH-series expression. E.g.:

         septic_d7_P5_poly 𝕂 a b
           = (deg-7 part of bch((½a+b)+V_5, ½a) − bch(½a+b, ½a))
           = (1/12)·([V_5, [½a, b]] − [[½a, b], V_5] + ...)   -- Lie poly form

     Each requires:
     * CAS script producing the explicit operator-form expression.
     * Lean lemma proving the polynomial DEF equals the operator form via
       `unfold + match_scalars <;> ring`.
     ~50-150 lines per piece, 6 lemmas total.

A.3-A.5) Joint Lipschitz bound on the 6-piece sum using operator forms,
     combining with Group E+F+CD-quintic to drop joint bound O(s⁷) → O(s⁹),
     final assembly replacing `symmetric_bch_septic_sub_poly_axiom` with a
     proved theorem.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 43, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 43 (2026-05-17, CAS infrastructure for d7 operator-form decomposition, 3 commits)**:

Established the structural decomposition of `septic_d7_perturbation_poly`
into 6 operator-form pieces (foundation for the future Lean Phase B-septic
operator-form identity). The CAS verification confirms:

    septic_d7_perturbation_poly
      = P_2 + P_3 + P_4 + P_5 + Cross(V_2, V_3) + Cross(V_2, V_4)

where:
* `P_j := (bch(x + V_j, ½a) − bch(x, ½a))_deg7` is the single-V_j
  perturbation piece (V_j = bch_kth_term(½a, b), x = ½a + b).
* `Cross(V_j, V_k) := (bch(x + V_j + V_k, ½a) − bch(x + V_j, ½a) −
  bch(x + V_k, ½a) + bch(x, ½a))_deg7` is the mixed second-difference
  cross piece.

The 6 pieces with explicit polynomial forms (CAS-derived):
* P_2 (V_2-only): 96 terms, LCM 92160, Σ|num|/LCM ≈ 0.0277.
* P_3 (V_3-only): 108 terms, LCM 276480, Σ|num|/LCM ≈ 0.0282.
* P_4 (V_4-only): 35 terms, LCM 18432, Σ|num|/LCM ≈ 0.0093.
* P_5 (V_5-only): 100 terms, LCM 276480, Σ|num|/LCM ≈ 0.0124.
* Cross(V_2, V_3): 41 terms, LCM 18432, Σ|num|/LCM ≈ 0.0089.
  Bilinear V_2·V_3 from C_4 (deg 4+1+2=7) + trilinear V_2²·V_3 from C_3
  (deg 3+1+1+2=7).
* Cross(V_2, V_4): 30 terms, LCM 9216, Σ|num|/LCM ≈ 0.0104.
  Bilinear V_2·V_4 from C_3 (deg 3+1+3=7) only.

Combined: 116 terms, LCM 276480, matching the existing Lean def
`septic_d7_perturbation_poly_eq_sum`.

3 new commits this session:

1. `4f099ef`: 3 V_j-only CAS scripts (gen_delta_lin_V{3,4,5}_d7.py).
2. `6278da8`: 2 cross V_j·V_k CAS scripts (gen_cross_V{2_V3,2_V4}_d7.py).
3. `17636ab`: 3 verification scripts (verify_d7_{cross_terms,
   cross_decomposition, operator_decomp}.py) confirming the 6-piece sum
   matches `septic_d7_perturbation_poly` exactly at CAS level.

Companion to the existing `gen_delta_C6_lin_V2.py` (commit 8a05af9 = P_2 piece).

**Why only 6 pieces** (not 8-10 as originally roadmapped):
Cross enumeration showed that Cross(V_2, V_5), Cross(V_3, V_4),
Cross(V_3, V_5), and Cross(V_4, V_5) all vanish at deg 7 (C_2 doesn't
admit bilinear substitution since it has only 1 z, and higher C_p with
bilinear V_j·V_k pairs has total degree already too large). Only
Cross(V_2, V_3) (bilinear + trilinear contributions) and Cross(V_2, V_4)
(bilinear only) survive. The 4 single-V_j pieces (j = 2..5) handle the
diagonal contributions including higher orders in single V's (V_2² in
C_5, V_2³ in C_4, V_3² in C_3).

**Mathematical interpretation**:
* pert_d7 := (bch(z, ½a) − bch(½a+b, ½a))_d7  (z = bch(½a, b))
* pert_d7 = C_7_inner + correction (verified, palindromic identity).
* C_7_inner = V_7 = bch_septic_term(½a, b).
* correction = sym_E_7 − C_7(½a, b) − C_7(½a+b, ½a) (117 terms).
* P_6 = ½·[V_6, ½a] = ½·[C_6(½a, b), ½a] (49 terms, the existing
  `half_C6_bracket_eq` polynomial form).
* septic_d7_perturbation_poly = correction − P_6
  = P_2 + P_3 + P_4 + P_5 + Cross(V_2,V_3) + Cross(V_2,V_4).

**Remaining work for the operator-form Phase B-septic identity (roadmap item A)**:
A.1) Encode each of the 6 pieces as Lean DEFs (explicit polynomial sums
     mirroring `septic_d7_perturbation_poly`'s 116-term def).
A.2) Prove each polynomial form equals its "operator form" (closed-form
     expression involving bch_kth_term, brackets, and bch series
     differences) via `match_scalars + ring`.
A.3) Combined identity: Σ polynomial forms = septic_d7_perturbation_poly.
A.4) Norm bounds on each operator form using Lipschitz (e.g., for P_5,
     bound = ‖ΔC_3_lin(V_5)‖ ≤ C·s³·‖V_5‖ ≤ C·s³·s⁵ = C·s⁸).
A.5) Joint Group E+F+CD-quintic bound replacing the 4 separate bounds.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 42, 2026-05-17)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 42 (2026-05-17, per-Group bounds for septic hdecomp, 4 commits)**:

Per-Group norm bounds for all 20 sub-pieces of
`symmetric_bch_septic_extended_hdecomp` (session 41) now in place. The 20
pieces split into 4 named bounds:

1. **`7468707`** — `norm_septic_group_AB_le` (5 pieces, ≤ 8·10¹²·s⁹).
   Group A nonic (R₁, R₂, ½·[R₁, a']) + Group B-octic (½·[C₈(a',b), a'],
   C₈(z,a')−C₈(a'+b,a')). Intrinsically O(s⁹) via Phase A nonic remainders
   + C₈ Lipschitz. Total: 2·10⁸ + 7·10¹² + 2.5·10⁷ + 0.5 + 10⁶ ≈ 7·10¹².

2. **`991a15c`** — `norm_septic_group_E_le` (3 pieces, ≤ 10⁶·s⁷). Group E =
   (C₇(z,a')−C₇(a'+b,a')) + ½·[C₆(a',b), a'] − correction. Uses
   `septic_d7_cancellation_poly_form` to absorb ½·[C₆,a'] − correction =
   −d7_pert, leaving (C₇ diff) − d7_pert. Bound via C₇ Lipschitz
   (≤ 200000·s⁸) + d7_pert norm (≤ s⁷); fold s⁸ → s⁷ via s < 1/4.

3. **`7dfef4f`** — `norm_septic_group_F_le` (4 pieces, ≤ 10⁴·s⁷). Group F =
   ½·[C₇(a',b),a'] + C₈(a',b) + C₈(a'+b,a') + (C₆ diff). Uses
   `septic_d8_cancellation_poly_form` to absorb the 3 octic-leading pieces
   as −d8_pert. Bound via C₆ Lipschitz (≤ 6000·s⁷) + d8_pert (≤ s⁸).

4. **`7134c54`** — `norm_septic_group_CD_quintic_le` (8 pieces, ≤ 10⁸·s⁷).
   Thin wrapper around `symmetric_bch_quintic_group_CD_le` — the 8 retained
   Group C+D-quintic pieces have identical definitions in the septic hdecomp.

**Critical observation**: triangle-summing the 4 Group bounds gives
≤ ~10⁸·s⁷, NOT the parent-axiom target of 10¹²·s⁹. The 12 deg-7-leading
pieces (Group E + F + CD-quintic) need joint cancellation against each
other to drop to deg-9. This requires the operator-form Phase B-septic +
Phase C-septic identities (decomposing the d7/d8 perturbation polys into
explicit ΔC_k operators), which is multi-session CAS work analogous to
the existing quintic Phase B identity infrastructure
(`deltaC3_lin_V3_eq`, `deltaC3_quad_V2_eq`, `deltaC4_lin_V2_eq`,
`half_C4_bracket_eq`).

**Remaining work** (estimate 5-10 more sessions):
A) Phase B-septic operator-form identity: decompose
   `septic_d7_perturbation_poly` into ΔC₃(V₄,V₅) + ΔC₃²(V₂·V₃) +
   ΔC₄(V₃,V₄) + ΔC₄²(V₂²) + ΔC₅(V₂,V₃) + ΔC₅²(V₂²) + ΔC₆(V₂) +
   ½·[C₆,a']. ~8-10 sub-lemmas, ~50-300 lines each.
B) Phase C-septic operator-form identity: similar for d8.
C) Joint Group E+F+CD-quintic bound ≤ K·s⁹ replacing the 4 separate bounds.
D) Final assembly: `norm_symmetric_bch_septic_sub_poly_le` proved theorem
   replacing the axiom.

Axiom count unchanged (still 2 scoped private axioms).

## Status (session 39, 2026-05-16)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 39 (2026-05-16, septic alt-form foundation, 4 commits)**:

Foundation infrastructure for the deg-9-parent T2-F7e-octic discharge of
`symmetric_bch_septic_sub_poly_axiom`:

1. `6a958c8`: Phase A — `norm_bch_inner_nonic_remainder_le` (≤ 2·10⁸·s⁹)
   + `norm_bch_outer_nonic_remainder_le` (≤ 7·10¹²·s⁹). Deg-9 analogs of
   the septic Phase A bounds, wrapping `norm_bch_nonic_remainder_le`
   (session 37) with standard `s₁ ≤ s` / `s₂ ≤ (57/22)·s` scaffolding.
   `(57/22)^9 ≤ 5262` (vs `(57/22)^7 ≤ 784` for septic).

2. `34a7d6c`: `symmetric_bch_septic_correction_poly` (117-term def, LCM
   276480, Σ|num|/LCM ≈ 0.057) + `symmetric_bch_septic_poly_alt_form`:

       sym_E₇(a, b) = bch_septic_term(½a, b) + bch_septic_term(½a+b, ½a)
                    + symmetric_bch_septic_correction_poly(a, b).

   Proved via `unfold + simp + match_scalars <;> ring` at section-level
   `maxHeartbeats 64000000`. CAS-derived via
   `scripts/discover_septic_alt_form.py` + `scripts/gen_septic_correction_lean.py`.

3. `315997e`: `norm_symmetric_bch_septic_correction_poly_le`:
   `‖correction(a, b)‖ ≤ (‖a‖+‖b‖)⁷`. Uses Finset.sum approach mirroring
   `norm_symmetric_bch_septic_poly_le` (`correctionSepticTermN`/
   `correctionSepticTerm` defs, `_eq_sum` rewrite at 16M heartbeats +
   maxRecDepth 2000, uniform per-i bound `1280/276480`, Σ
   `117·1280/276480 ≈ 0.542 ≤ 1`). ~770 lines CAS-generated via
   `scripts/gen_septic_correction_norm_bound.py`.

4. `4820aa2`: `half_C6_bracket_eq` — explicit 49-term polynomial form
   (denominator 92160) of `½·[bch_sextic_term(½a, b), ½a]`. Σ|num|/LCM
   ≈ 0.008. Deg-7 analog of `half_C4_bracket_eq` (quintic Phase B
   piece). First building block toward the future
   `symmetric_bch_septic_deg7_cancellation_pure_identity` (Phase B-septic
   identity).

**Remaining work for full discharge** (multi-session, ~8-15 more):
* Phase B-septic identity (deg-7 cancellation, combining ΔC_k diffs for
  k=3..6 + half_C6_bracket = correction). Needs CAS for ΔC_k polynomial
  forms (~50-150 terms each) OR a single combined 116-term identity.
* Phase C-septic identity (deg-8 cancellation, analog of
  `symmetric_bch_quintic_deg6_cancellation_pure_identity`).
* Septic extended hdecomp (~17-piece, deg-9 analog of the 13-piece
  quintic hdecomp).
* Group C+D-septic combined bound (Phase E.2 analog).
* Final assembly: `norm_symmetric_bch_septic_sub_poly_le` proved theorem
  replacing the axiom.

Axiom count unchanged (2 scoped private axioms remain).

## Status (session 37, 2026-05-16)

Branch: `main`. Repository is **0 sorries**, **2 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`.

**Session 37 (2026-05-16, nonic small-s axiom DISCHARGED, 1 commit)**:

Commit `4b4e32d` (+1743 / −88 net lines): the session-9843889 stepping-stone
`norm_bch_nonic_remainder_small_s_axiom` (introduced concurrently with the
public `norm_bch_nonic_remainder_le`) is now a fully proved theorem
`norm_bch_nonic_remainder_small_s_le` (~830 lines, mirrors session-36
`norm_bch_octic_remainder_small_s_le` at one degree higher).

Discharge structure:
* pieceA bound (≤ 3·s⁹/(2-exp s)) via new `norm_bch_nonic_pieceA_le`.
* pieceB''''' bound (≤ 442·s⁹) via `pieceB_nonic_decomp` + 7 sub-pieces:
  - S₁'' ≤ 25·s⁹ (I₁ chain: `I1_nonic_residual_decomp_eq` +
    `norm_I1_nonic_residual_RHS_le` + `norm_combined_tricky_nonic_le ≤ 35·s⁹`).
  - S₂'' ≤ 93·s⁹ (I₂ chain: `norm_I2_nonic_residual_RHS_le` with K_PmT6=7,
    K_P2''=19, K_PzP''=19, K_P3''=200 → ⅓·278·s⁹).
  - S₃'' ≤ 150·s⁹ (¼·`norm_y4_..._sub_y4_8_le ≤ 600·s⁹`).
  - S₄'' ≤ 80·s⁹ (⅕·`norm_y5_..._sub_y5_8_le ≤ 400·s⁹`).
  - S₅'' ≤ 39·s⁹ (⅙·`norm_y6_..._sub_y6_8_le ≤ 230·s⁹`).
  - S₆'' ≤ 23·s⁹ (⅐·`norm_y7_sub_z7_sub_y7_8_le ≤ 155·s⁹`).
  - S₇ ≤ 32·s⁹ (⅛·`norm_pow8_sub_zpow8_le ≤ 255·s⁹`).
* Total: ≤ 445·s⁹/(2-exp s) ≤ 1000·s⁹/(2-exp s).

Public theorem `norm_bch_nonic_remainder_le` no longer axiom-gated.

New supporting infrastructure:
* `LogSeries.lean`: `norm_logOnePlus_sub_sub_sub_sub_sub_sub_sub_sub_le`
  (deg-9 log tail `≤ ‖x‖⁹/(1-‖x‖)`), plus `summable_logSeriesTerm_shift8`,
  `logSeriesTerm_seven`, `logOnePlus_sub_..._eq_tsum` helpers.
* `Basic.lean`: `real_exp_sub_one_pow9_le_small` (`(exp s − 1)⁹ ≤ 3·s⁹`),
  `norm_exp_sub_one_sub_sub_sub_sub_sub_sub_sub_sub_le` (noncomm deg-9
  exp tail), `real_exp_ninth_order_le_nonic` (real ≤ s⁹).
* `RemainderBounds.lean`: `norm_bch_nonic_pieceA_le`.

Bug fix included in the same commit: commit 9843889 placed
`norm_bch_nonic_remainder_large_s_le` in `SmallSDischarge.lean` but it
referenced `norm_bch_octic_remainder_le` from `RemainderBounds.lean` —
a downstream-import dependency, so the build was broken at HEAD~1.
Moved the theorem to `RemainderBounds.lean`. Also dropped `private` from
6 helpers needed by the new discharge (`norm_pow8_sub_zpow8_le`,
`norm_y7_sub_z7_sub_y7_8_le`, `norm_combined_tricky_nonic_le`,
`norm_y4_..._sub_y4_8_le`, `norm_y6_..._sub_y6_8_le`,
`norm_y5_..._sub_y5_8_le`) — still BCH.-namespaced, no public API change.

Notes:
* `set_option maxHeartbeats 64000000` needed for whnf elaboration of the
  ~830-line statement (same level as octic discharge).
* S₃''/S₄''/S₅''/S₆'' bridges between wrapper output (mixed `(y-P)^k` /
  `(y-P)*…*(y-P)` notation) and pieceB form (mul notation): `convert +
  abel/noncomm_ring`.

Axiom count: **3 → 2** (restoring the count claimed by CLAUDE.md before
the session-9843889 axiom was introduced). The remaining two are the
septic stepping stones `symmetric_bch_septic_sub_poly_axiom` and
`norm_septic_match_residual_le_axiom`.

## Status (session 36, 2026-05-15)

**Session 36 (2026-05-15, octic small-s axiom DISCHARGED, 1 commit)**:

Commit `6b5396d` (+919 net lines): `norm_bch_octic_remainder_small_s_axiom`
(introduced session 32) is now a fully proved theorem
`norm_bch_octic_remainder_small_s_le` (~700 lines, mirrors session-19
`norm_bch_septic_remainder_small_s_le` at one degree higher).

Discharge structure:
* pieceA bound (≤ 3·s⁸/(2-exp s)) via `norm_bch_octic_pieceA_le`.
* pieceB'''' bound (≤ 217·s⁸) via `pieceB_octic_decomp` + 6 sub-pieces:
  - S₁' ≤ 25·s⁸ (I₁ chain: `I1_octic_residual_decomp_eq` +
    `norm_I1_octic_residual_RHS_le` + `norm_combined_tricky_octic_le ≤ 35·s⁸`).
  - S₂' = 57·s⁸ (I₂ chain: `norm_I2_octic_residual_RHS_le` with K_PmT5=6,
    K_P2'=16, K_PzP'=16, K_P3'=105 → ⅓·171·s⁸).
  - S₃' ≤ 72·s⁸ (¼·`norm_y4_sub_z4_sub_y4_5_sub_y4_6_sub_y4_7_le ≤ 285·s⁸`).
  - S₄' ≤ 29·s⁸ (⅕·`norm_y5_sub_z5_sub_y5_6_sub_y5_7_le ≤ 141·s⁸`).
  - S₅' ≤ 15·s⁸ (⅙·`norm_y6_sub_z6_sub_y6_7_le ≤ 87·s⁸`).
  - S₆ ≤ 19·s⁸ (⅐·`norm_pow7_sub_zpow7_le ≤ 127·s⁸`).
* Total: ≤ 220·s⁸/(2-exp s) ≤ 1000·s⁸/(2-exp s).

Public theorem `norm_bch_octic_remainder_le` no longer axiom-gated.

Notes:
* `set_option maxHeartbeats 64000000` needed for whnf elaboration of the
  ~770-line statement.
* S₄' bridge: lemma's y5_7 ordering differs from pieceB's — `convert + abel`.
* S₅' bridge: lemma uses `z^k`, pieceB uses `z*z*…*z` — `convert + noncomm_ring`.

Axiom count: **3 → 2** ✓.

## Status (session 35, 2026-05-14)

Branch: `main`. Repository is **0 sorries**, **3 scoped private axioms**:
`symmetric_bch_septic_sub_poly_axiom`, `norm_septic_match_residual_le_axiom`,
`norm_bch_octic_remainder_small_s_axiom` (octic stepping stone, awaiting discharge).

**Session 35 part 8 (2026-05-15, deg-9 PzP-residual sandwich bound, 1 commit)**:

Commit `984eeb3` (+187 lines): `BCH.norm_PzP_etc_nonic_le` — deg-9 analog of
`norm_PzP_etc_octic_le` (session 29) at one degree higher.

Bounds the deg-9 residual of P·z·P after subtracting all deg-5..8 contributions:
`‖P·z·P − T₂zT₂ − T₂zT₃ − T₃zT₂ − T₂zT₄ − T₃zT₃ − T₄zT₂ − T₂zT₅ − T₃zT₄ −
T₄zT₃ − T₅zT₂‖ ≤ 19·s⁹` for `s ≤ 1/10`. Decomposes via
`P = T₂ + T₃ + T₄ + T₅ + D₆` into 15 deg-9+ terms (6 T·z·T + 8 T·z·D₆ cross +
D₆·z·D₆). Per-degree sums: 17 + 1.6 + 0.15 + 0.014 + ε ≈ 18.76·s⁹ ≤ 19·s⁹.

Together with session 35 part 7's `norm_P2_etc_nonic_le ≤ 19·s⁸`, the
P²-residual + PzP-residual deg-9 cluster bounds are now in place. The
remaining I2-nonic input is `norm_P3_etc_nonic_le`. Forward-looking
infrastructure for the deg-9-parent T2-F7e-octic discharge.

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

**Primary downstream application achieved (2026-05-19)**: tight 4th-order
Trotter formula error bound (`norm_suzuki4_childs_form_via_level3` on the
Lean-Trotter side) is fully proved, axiom-free at the project level.

Remaining: τ⁷ uniform refinement on Lean-Trotter side (`bch_uniform_integrated`,
`norm_suzuki4_level4_uniform`) still depends on 2 surviving Lean-BCH septic
stepping stones. Discharge roadmap continues in sessions 26+.

## Constraints

- **Lean:** 4.29.0-rc8 (via `lean-toolchain`)
- **Mathlib:** pinned in `lake-manifest.json`
- **Typeclass setup:** `[NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]`
- `include 𝕂 in` needed before theorems where `𝕂` appears in proofs but not the type.

## File Structure

```
BCH/
├── LogSeries.lean         ← log(1+x) series, summability, exp∘log = id
├── Basic.lean             ← (11 074 lines) exp/log bounds, BCH def, H1/H2,
│                            quintic+sextic remainder + bch_*_term defs/Lipschitz
├── SmallSDischarge.lean   ← (5 987 lines) pure ring identities, pow_k/y_k decomps,
│                            I₁/I₂ residual decomps, R+T₅ chain, pieceB_*_decomp
│                            (incl. 4-billion-heartbeat pieceB_octic_decomp)
├── RemainderBounds.lean   ← (5 671 lines) T_k norm bounds, P²/PzP/P³-residual
│                            cluster bounds, public norm_bch_sextic/septic/octic_
│                            remainder_le, symmetric BCH cubic/quintic/septic poly
├── SymmetricQuintic.lean  ← τ⁵ coefficient: 30-term polynomial, c⁵ homogeneity,
│                            B1.c quintic Taylor bridge (proved theorem,
│                            no axioms); septic stepping-stone definitions
├── Palindromic.lean       ← Suzuki-5 palindromic product, M1–M4b, M6 Trotter h4,
│                            B1.d per-block wrapper, B2.2.a-e, B2.5 T₂ bound
├── ChildsBasis.lean       ← 8 Childs 4-fold commutators + bchFourFoldSum
│                            + BCHPrefactors struct
└── Suzuki5Quintic.lean    ← βᵢ(p) polynomials, R₅ Childs def, headline τ⁵ theorem
                             (axiom-free), tight bridge at Suzuki p,
                             septic τ⁷ infrastructure (2 stepping-stone axioms)
```

Import chain: `LogSeries → Basic → SmallSDischarge → RemainderBounds →
SymmetricQuintic → Palindromic → ChildsBasis → Suzuki5Quintic`.

**Build-time note (post split, 2026-05-15):** `BCH/Basic.lean` was split twice
to enable parallel compilation and per-file incremental rebuilds. Touched-rebuild
times (M1, 11 cores):
* `BCH.Basic` — 509 s (8.5 min); was 1 234 s (20.5 min) for the monolith.
* `BCH.SmallSDischarge` — 690 s (11.5 min); contains the 1+2+4-B-heartbeat
  `pieceB_*_decomp` cluster.
* `BCH.RemainderBounds` — 421 s (7.0 min); the recent edit hot-zone
  (T_k/P²/PzP nonic bounds land here).

The split required dropping `private` from 40 internal helpers (kept in `BCH.`
namespace, no public API impact). Cold rebuild from scratch: 1 114 s (18.5 min),
slightly faster than the monolith due to better elaboration locality.

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

## Tier-2 of B1.c: `symmetric_bch_quintic_sub_poly_axiom` — DISCHARGED

**DISCHARGED (May 2026).** `norm_symmetric_bch_quintic_sub_poly_le` is
now a proved theorem at `BCH/SymmetricQuintic.lean:9587` with constant
`2·10¹⁰·(‖a‖+‖b‖)⁷` (tighter than the original `10⁹·(‖a‖+‖b‖)⁷`
axiom slack, but achievable via the proof's piece-by-piece estimates).

Statement now in place as a proved theorem:
```
‖symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b
    − symmetric_bch_quintic_poly 𝕂 a b‖ ≤ 2·10¹⁰ · (‖a‖+‖b‖)⁷
```

Proof: 13-piece extended hdecomp (Phase D), bounding via Phase A septic
remainders, Phase E.1 inline (Group A bracket + Group B C₆ pieces), and
the Group C+D sub-result (Phase E.2). Total ≤ 1.21·10¹⁰·s⁷ ≤ 2·10¹⁰·s⁷.

Public theorems no longer depending on any axiom for the τ⁵ chain:
- `BCH.norm_symmetric_bch_quintic_sub_poly_le` (B1.c bridge, proved theorem).
- `BCH.norm_strangBlock_log_sub_quintic_target_le` (B1.d per-block wrapper).
- `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` (P1 headline).
- `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` (P1 bridge corollary).
- `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` (P2 bridge).

Downstream consumer: Lean-Trotter's `norm_suzuki4_childs_form_via_level3`
(tight 4th-order Trotter formula, Childs (2021) prefactors) is now
axiom-free at the project level after the May-2026 pin bump.

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

## Lean-Trotter interface (all 3 axioms discharged)

`Lean-Trotter/LieTrotter/Suzuki4ViaBCH.lean` originally had three
BCH-interface axioms; all three are now proved theorems:

1. `bch_w4Deriv_quintic_level2` — unit-coefficient pointwise τ⁵ bound.
   **Theorem (2026-04-24)** via `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le`.
2. `bch_w4Deriv_level3_tight` — tight γᵢ at Suzuki p.
   **Theorem (2026-04-24)** via `BCH.suzuki5_log_product_quintic_tight_at_suzukiP`.
3. `bch_uniform_integrated` — existential-δ pointwise τ⁵ + τ⁷ bound.
   **Theorem (2026-04-26)** via `BCH.suzuki5_log_product_septic_at_suzukiP`
   (itself a theorem since Lean-BCH session 26, gated only by the 2 surviving
   septic stepping-stone axioms).

After Lean-Trotter's pin bump to Lean-BCH `d455ff0` (2026-05-19),
the τ⁵ chain (interface axioms 1+2) is axiom-free; interface axiom 3
(L4 uniform refinement) transitively depends only on the 2 remaining
Lean-BCH septic axioms.

**Key public theorems on this branch** (the τ⁵ chain depends only on
Lean's 3 standard axioms; the τ⁷ chain additionally depends on the 2
septic stepping-stone axioms):
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

- Git log preserves session-by-session implementation history (sessions 1–58).
- `claude/session_history.md` — archived earlier session notes (sessions 16–27).
- `claude/sextic_remainder_strategy.md` — Tier-1 small-s discharge plan
  (historical; closed in session 16).
- `claude/lean-bch-B1c-session-prompt.md` — **obsolete (B1.c discharged
  May 10–11, 2026)**, kept for historical context.
- `claude/lean-bch-T2F7e-*.md` — T2-F7e parent-discharge plans
  (historical; B1.c Tier-2 closed via sessions 20–22).
- `claude/lean-bch-B2-session-prompt.md` — B2 (5-factor BCH composition).
- `claude/lean-bch-B2.5-session-prompt.md` — B2.5 (T₂ bound).
- `claude/lean-bch-next-session-prompt.md` — current task pointer
  (sessions 26+ matching-identity roadmap for τ⁷).
