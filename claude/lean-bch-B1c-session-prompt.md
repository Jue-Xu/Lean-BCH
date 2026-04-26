# Lean-BCH next session — B1.c (quintic Taylor bridge for symmetric BCH)

## Status update (2026-04-26, session 13)

**P1 axiom discharged (session 12).** Repository on `main` @ `4cc5a5a`,
0 sorries, 1 scoped private axiom (`symmetric_bch_quintic_sub_poly_axiom`
= B1.c) + Lean's 3 standard. After session 12, Lean-Trotter also added
a new axiom `suzuki5_R5_R7_identification_axiom` for axiom-3 work
(commit `cf5eea3`); this is independent of B1.c.

**Session 13 added Tier-1 foundation pieces only:**

- `BCH/LogSeries.lean`: `summable_logSeriesTerm_shift5`,
  `logSeriesTerm_four`, `logOnePlus_sub_sub_sub_sub_sub_eq_tsum`,
  `norm_logOnePlus_sub_sub_sub_sub_sub_le` (~45 lines).
- `BCH/Basic.lean`: `norm_exp_sub_one_sub_sub_sub_sub_sub_le`,
  `real_exp_sixth_order_le_sextic` (~108 lines).

These are mechanical mirrors of the existing order-5 patterns
(`norm_logOnePlus_sub_sub_sub_sub_le`, `norm_exp_sub_one_sub_sub_sub
_sub_le`, `real_exp_fifth_order_le_quintic`) at one degree higher. Build
clean. Both private (consumed only within Basic.lean's planned
`norm_bch_sextic_remainder_le`).

**Remaining for full B1.c (Tier 1 + Tier 2 + Tier 3) — see below.**

## Context

Continuing Priority B (discharge `suzuki5_R5_identification_axiom` on
branch `trotter-5factor-palindromic`). Prior sessions closed:

- **B1.a** (CAS extraction): 30 non-zero 5-letter words + rational
  coefficients for the 3-factor Strang block's τ⁵ coefficient, LCM 5760.
- **B1.b** (definition + homogeneity + norm bound): fully proved in
  `BCH/SymmetricQuintic.lean`. `symmetric_bch_quintic_poly` is defined,
  `symmetric_bch_quintic_poly_smul` (c⁵ homogeneity) and
  `norm_symmetric_bch_quintic_poly_le` (`‖E₅‖ ≤ s⁵`) both depend only
  on the 3 standard Lean axioms.

**Current state**:
- Lean-BCH `trotter-5factor-palindromic` @ rev `e8d8858`. 0 sorries,
  1 scoped `private axiom` (`suzuki5_R5_identification_axiom` on P1).
- Lean-Trotter `main` @ rev `705791a`. Axioms 1 and 2 converted to
  theorems; both chain to Lean-BCH's single P1 axiom. Axiom 3
  (`bch_uniform_integrated`) still bare.

## Goal of this session — B1.c

Prove the **quintic Taylor bridge** for the 3-factor symmetric BCH:

```lean
theorem norm_symmetric_bch_quintic_sub_poly_le
    {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b −
       symmetric_bch_quintic_poly 𝕂 a b‖ ≤
      K * (‖a‖ + ‖b‖) ^ 7
```

where `K` is some explicit constant (probably ~10⁸ or similar, analogous
to the `10⁷` in `norm_symmetric_bch_cubic_sub_poly_le`).

**Rationale**: by palindromic symmetry, degrees 2, 4, 6 of the symmetric
BCH vanish. So `symmetric_bch − (a+b) − cubic_poly − quintic_poly =
O(s⁷)`, which is a tighter bound than the existing
`norm_symmetric_bch_cubic_sub_poly_le` (O(s⁵)). The new bound factors
out the τ⁵ coefficient too.

## Proof template

Template is `norm_symmetric_bch_cubic_sub_poly_le` in
`BCH/Basic.lean` around line 3798. That theorem proves `symmetric_bch −
(a+b) − cubic_poly = O(s⁵)` via a 6-term algebraic decomposition + norm
bounds. For B1.c, we extend this to one higher order.

### Required new infrastructure

Before the main theorem, likely need these new pieces in `BCH/Basic.lean`:

1. **[DONE session 13]** Log/exp tail bounds at order 6:
   - `norm_logOnePlus_sub_sub_sub_sub_sub_le` (in LogSeries.lean)
   - `norm_exp_sub_one_sub_sub_sub_sub_sub_le`
   - `real_exp_sixth_order_le_sextic`

2. **[TODO]** `bch_quintic_term 𝕂 a b : 𝔸` — the τ⁵ coefficient of
   `bch(a, b) = a + b + ½[a,b] + bch_cubic_term + bch_quartic_term +
   bch_quintic_term + O(s⁶)`. Analog of existing `bch_cubic_term` and
   `bch_quartic_term`. **Definition discovery requires CAS** — the Hall
   basis Z₅ has 6 free Lie algebra dim'l elements with non-trivial
   rational coefficients. Recommend extending
   `Lean-Trotter/scripts/compute_bch_prefactors.py` to extract Z₅
   symbolically (the `ncpoly_log_one_plus(ncpoly_mul(exp_a, exp_b),
   max_degree=5)` call already returns the full degree-5 BCH expansion;
   subtract the known degrees 1-4 to get Z₅ as an NC-polynomial).

3. **[TODO]** `bch_quintic_term_smul` — `c⁵` homogeneity. Analog of
   `bch_cubic_term_smul` / `bch_quartic_term_smul`.

4. **[TODO]** `norm_bch_quintic_term_le` — `‖bch_quintic_term a b‖ ≤
   K·(‖a‖+‖b‖)⁵`. Explicit constant via triangle inequality on the
   term's definition.

5. **[TODO]** `quintic_identity` — analog of `quartic_identity`
   (Basic.lean:1563), one degree higher. Statement form:
   `½W_H1 + ⅓z³ + ¼y⁴ - bch_cubic_term - bch_quartic_term - bch_quintic_term =
    [quintic+ terms expressible via F₁, F₂, G₁, G₂, E·b, a·E, etc.]`.
   Discovery requires CAS. The existing 100-line `quartic_identity` proof
   at 64M heartbeats indicates the analog will be ~150-200 lines at
   higher heartbeat budget.

6. **[TODO]** `norm_bch_sextic_remainder_le` — for `bch(a, b)`, bound on
   `‖bch(a, b) − (a+b) − ½[a,b] − cubic − quartic − quintic‖ ≤
    K·(‖a‖+‖b‖)⁶/(2−exp(s))`.
   Analog of `norm_bch_quintic_remainder_le` (~800 lines, one order higher).

### Main theorem proof structure (mirror of the cubic version)

```
theorem norm_symmetric_bch_quintic_sub_poly_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 1/4) :
    ‖symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b −
       symmetric_bch_quintic_poly 𝕂 a b‖ ≤ K * s^7 := by
  -- Setup (same as cubic version): a' = ½a, s, s₁.
  set a' := (2 : 𝕂)⁻¹ • a
  set s := ‖a‖ + ‖b‖
  set s₁ := ‖a'‖ + ‖b‖

  -- Inner BCH: z = bch(a', b). Use the NEW sextic remainder bound.
  set z := bch (𝕂 := 𝕂) a' b
  set R₁ := z − (a' + b) − ½•[a',b] − bch_cubic_term 𝕂 a' b
             − bch_quartic_term 𝕂 a' b − bch_quintic_term 𝕂 a' b
  have hR₁_le : ‖R₁‖ ≤ K₁·s₁⁶/(2−exp(s₁)) := norm_bch_sextic_remainder_le ...

  -- Outer BCH: bch(z, a'). Use the same sextic remainder.
  set R₂ := bch (𝕂 := 𝕂) z a' − (z + a') − ½•[z,a'] −
    bch_cubic_term 𝕂 z a' − bch_quartic_term 𝕂 z a' −
    bch_quintic_term 𝕂 z a'
  have hR₂_le : ‖R₂‖ ≤ K₂·(‖z‖+‖a'‖)⁶/(2−exp(‖z‖+‖a'‖)) := ...

  -- Algebraic decomposition (the hard part): an identity expressing
  -- symmetric_bch − (a+b) − cubic_poly − quintic_poly as a sum of:
  --   R₁, R₂, [R₁, a']/2, [C₄(a',b), a']/2, [C₅(a',b), a']/2,
  --   C₃/C₄/C₅ sextic residuals, and other degree-6+ terms.
  -- Analog of the 6-term decomp in cubic proof, extended to include
  -- degree-5 terms (which should cancel by palindromic symmetry).

  have hdecomp : symmetric_bch_cubic 𝕂 a b − symmetric_bch_cubic_poly 𝕂 a b
      − symmetric_bch_quintic_poly 𝕂 a b = (sum of ~8 terms) := by
    -- unfold definitions, then noncomm_ring (after scalar clearing).
    sorry

  -- Each piece of the decomposition is O(s⁷) (bound by combinations of
  -- norm bounds on R₁, R₂, commutators, etc.).
  -- Sum + triangle inequality gives the final bound.
  ...
```

### The deep difficulty

The **algebraic decomposition (`hdecomp`)** is the real work. For the
cubic proof it was 6 terms; for the quintic it'll be ~8-10. Each term
must be discovered by careful BCH expansion comparison. The CAS pipeline
`scripts/compute_bch_prefactors.py` (Lean-Trotter) already does this
symbolically to degree 5 — you can extend it to degree 7 and extract the
decomposition terms mechanically.

**Recommended workflow**:
1. Extend `compute_bch_prefactors.py` to degree 7. Print the expansion of
   `symmetric_bch(a, b) − (a+b) − cubic_poly(a, b) − quintic_poly(a, b)`.
   Verify it's O(s⁷) — all degree-5 words in the residual should be zero.
2. Decompose the residual into:
   - `R₁`-related terms (inner BCH sextic residual)
   - `R₂`-related terms (outer BCH sextic residual)
   - Nested-commutator corrections
3. Verify the decomposition symbolically in Python.
4. Port to Lean.

### Expected scope

**~300-500 lines of Lean** across `Basic.lean` (new quintic/sextic
primitives) and `SymmetricQuintic.lean` (main theorem). 1-2 focused
sessions, dominated by:
- (a) Discovering and verifying the `hdecomp` algebraic identity
  (symbolic, needs Python CAS).
- (b) Proving it in Lean via `noncomm_ring` after scalar clearing.
- (c) Bounding each of the ~8 pieces.

If `hdecomp` is too tangled, there's a **fallback**: introduce
`symmetric_bch_quintic_sub_poly_axiom` as a scoped private axiom (same
pattern as Suzuki5Quintic's Tier-2 axiom). This produces B1.c's
signature usable by B1.d and B2, at the cost of one more axiom to
eventually discharge.

## After B1.c: B1.d and beyond

Once `norm_symmetric_bch_quintic_sub_poly_le` is in place:

- **B1.d (~1-2 hours)**: add the `strangBlock_log` wrapper theorem
  `norm_strangBlock_log_sub_quintic_le` in `BCH/Palindromic.lean`.
  Signature:
  ```
  ∃ δ > 0, ∃ K ≥ 0, ∀ τ : ℝ, ‖τ‖ < δ →
    ‖strangBlock_log A B c τ − (c·τ)•(A+B)
       − (c·τ)³•symmetric_bch_cubic_poly A B
       − (c·τ)⁵•symmetric_bch_quintic_poly A B‖ ≤
    K·|c·τ|⁷·(‖A‖+‖B‖)⁷
  ```
  Trivial reduction: substitute `c·τ·A` for `a` and `c·τ·B` for `b` in
  `norm_symmetric_bch_quintic_sub_poly_le`, use `symmetric_bch_cubic_poly_smul`
  and `symmetric_bch_quintic_poly_smul` to pull out scalars.

- **B2** (multi-week): symbolic 5-factor composition. Substitute the
  Tier-1 expansion into `suzuki5_bch = bch(bch(2X, Y), 2X)`. Collect
  τ⁵ coefficient. Project onto Childs basis with 2 free parameters to
  get `suzuki5_R5` identification.

- **B3** (~1 day): triangle inequality assembly. Combine B1.d + B2 +
  existing `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`.

- **B4** (trivial): remove `suzuki5_R5_identification_axiom`.

## Setup

```bash
cd ~/Documents/Claude/Projects/Lean-BCH
git checkout trotter-5factor-palindromic
git pull
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build        # baseline, should pass clean with 0 sorries
```

## Key files to know

- `BCH/Basic.lean` — existing `bch_cubic_term`, `bch_quartic_term`,
  `norm_bch_quintic_remainder_le`, `norm_symmetric_bch_cubic_sub_poly_le`
  (template). Around lines 1397 (cubic), 1493 (quartic), 3797 (main
  template).
- `BCH/SymmetricQuintic.lean` — `symmetric_bch_quintic_poly` (B1.b, done).
- `BCH/Palindromic.lean` — where B1.d lands.
- `Lean-Trotter/scripts/compute_bch_prefactors.py` — CAS pipeline, extend
  to degree 7 for decomposition discovery.

## Acceptance criteria

- **Main**: `norm_symmetric_bch_quintic_sub_poly_le` proved (ideally
  without new axiom).
- `lake build` passes clean, still 0 sorries.
- If successful: axiom count unchanged (still 1 P1 axiom).
- If axiom fallback used: 1 new scoped private axiom, clearly
  documented with discharge roadmap. Report change in axiom count.
- Pushed commit + rev hash reported for future Lean-Trotter sync (no
  Lean-Trotter side changes needed for B1.c alone).

## Time estimate

- Decomposition discovery via CAS: **1-3 hours** (pure Python).
- Lean proof of `hdecomp` + norm bounds: **4-8 hours**.
- Total B1.c session: **1-2 days** focused work.
- B1.d (after B1.c): **~1-2 hours**.

## Fallback plan

If B1.c's `hdecomp` proves intractable after ~1 day of attempt:

1. Introduce `symmetric_bch_quintic_sub_poly_axiom` (scoped private)
   with the target statement.
2. Prove the theorem via the axiom.
3. Document the axiom with the "extend CAS to degree 7, port to Lean"
   roadmap.
4. Proceed with B1.d and B2 using the theorem.

This defers ~1 week of work but unblocks the larger B2 work. The axiom
is at lower abstraction than the current P1 axiom, so it's structurally
preferable once the roadmap is clear.
