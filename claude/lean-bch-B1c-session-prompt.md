# Lean-BCH next session — B1.c (quintic Taylor bridge for symmetric BCH)

## Status update (2026-05-05, session 14 — sextic_pure_identity PROVED)

**Major progress on B1.c.** Repository on `main` @ `dcf140f`, 0 sorries,
still just 1 scoped private axiom (B1.c). Two BCH axioms total (B1.c +
septic_at_suzukiP, the latter for axiom-3 work).

**Session 14 achievement** (continuing 13): the **`sextic_pure_identity`**
is now a fully proved Lean theorem in `BCH/Basic.lean` (commit
`1763d10`, +104 lines, 0 new axioms, build clean):

```lean
private theorem sextic_pure_identity (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : 𝕂)⁻¹ • a ^ 2 + (2 : 𝕂)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : 𝕂)⁻¹ • a ^ 3 + ... + (6 : 𝕂)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : 𝕂)⁻¹ • a ^ 4 + ... + (24 : 𝕂)⁻¹ • b ^ 4
    let W5 : 𝔸 := (60 : 𝕂)⁻¹ • a ^ 5 + ... + (6 : 𝕂)⁻¹ • (a ^ 3 * b ^ 2)
                - (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂)
    let y3_5 : 𝔸 := z^2 * T₃ + z * T₃ * z + T₃ * z^2 + z * T₂^2
                  + T₂ * z * T₂ + T₂^2 * z
    let y4_5 : 𝔸 := z^3 * T₂ + z^2 * T₂ * z + z * T₂ * z^2 + T₂ * z^3
    (2:𝕂)⁻¹ • W5 + (3:𝕂)⁻¹ • y3_5 - (4:𝕂)⁻¹ • y4_5 + (5:𝕂)⁻¹ • z^5
      - bch_quintic_term 𝕂 a b = 0
```

Proof: ×720 scalar clearing + ~30 simp lemmas (incl. 3 new
`(720) * ((720)⁻¹ * N) = N` lemmas to handle nested inverses in the
bch_quintic_term expansion) + noncomm_ring at maxHeartbeats 4 billion.
Build time ~8 minutes.

**Key insight**: The natural extension of `quartic_identity` operates
at the level of SUBSTITUTED polynomials in {a, b}, not unsubstituted
{a, b, ea, eb}. This sidesteps the bbbba/bbbbA coupling obstruction
that blocked the parametric search at session 13.

**Next concrete step — `norm_bch_sextic_remainder_le`** (~800 lines).
Mirrors `norm_bch_quintic_remainder_le` at Basic.lean:2769, extending
one degree higher:

- pieceA = log tail at order 6, bounded by `‖y‖⁶/(1-‖y‖)` ≤
  `(exp(s)-1)⁶/(2-exp(s))` (uses `norm_logOnePlus_sub_sub_sub_sub_sub_le`).
- pieceB = ½W + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅. Decompose:
  - I_1 = ½W + ⅓z³ - C₃ → quartic_identity
  - I_2 = ⅓(y³-z³), I_3 = -¼y⁴+¼z⁴, I_4 = ⅕y⁵-⅕z⁵: telescoping
  - I_5 = -¼z⁴, I_6 = +⅕z⁵: pure {a, b} terms
  - quintic_pure_identity for deg-4 cancellation, sextic_pure_identity
    for deg-5 cancellation.
- Each residual O(s⁶/(2-exp s)). Constants probably ~10000.

After norm_bch_sextic_remainder_le, extend cubic template
`norm_symmetric_bch_cubic_sub_poly_le` (line ~3798) to give B1.c
(`norm_symmetric_bch_quintic_sub_poly_le`), ~400-600 additional lines.

**Total remaining for B1.c discharge: ~1500-2000 lines of Lean.**

---

## Status update (2026-04-26, session 13)

**P1 axiom discharged (session 12).** Repository on `main` @ `973b5d6`,
0 sorries, 1 scoped private axiom (`symmetric_bch_quintic_sub_poly_axiom`
= B1.c) + Lean's 3 standard. After session 12, Lean-Trotter also added
a new axiom `suzuki5_R5_R7_identification_axiom` for axiom-3 work
(commit `cf5eea3`); this is independent of B1.c.

**Session 13 added Tier-1 foundation + bch_quintic_term (~488 lines, all
zero new axioms, build clean):**

### `BCH/LogSeries.lean` (~45 lines)
- `summable_logSeriesTerm_shift5`, `logSeriesTerm_four` (simp),
  `logOnePlus_sub_sub_sub_sub_sub_eq_tsum`,
  `norm_logOnePlus_sub_sub_sub_sub_sub_le`. Mechanical extension of the
  existing order-5 pattern at one degree higher.

### `BCH/Basic.lean` (~443 lines)
- `norm_exp_sub_one_sub_sub_sub_sub_sub_le` (private),
  `real_exp_sixth_order_le_sextic` (private).
- **`bch_quintic_term`** — the τ⁵ BCH coefficient (Z₅) defined via 30
  explicit 5-letter words on `{a, b}` with rational coefficients,
  decomposed into 4 sub-groups by absolute coefficient:
  - `bch_quintic_group_1` (4 monomials, |coeff|=1): -1/720·{aaaab,
    abbbb, baaaa, bbbba}
  - `bch_quintic_group_4` (10 monomials, |coeff|=4): +1/180·{...}
  - `bch_quintic_group_6` (14 monomials, |coeff|=6): -1/120·{...}
  - `bch_quintic_group_24` (2 monomials, |coeff|=24): +1/30·{ababa, babab}
- `bch_quintic_term_smul`: `Z₅(c•a, c•b) = c⁵·Z₅(a, b)` (analog of
  `bch_cubic_term_smul` / `bch_quartic_term_smul`).
- `norm_bch_quintic_term_le`: `‖Z₅(a, b)‖ ≤ s⁵` (sum of |coeffs| =
  4+40+84+48 = 176; multiplied by `‖(720)⁻¹‖ = 1/720` gives
  `176/720 ≈ 0.244`).

### `Lean-Trotter/scripts/extract_bch_z5.py` (~204 lines, local commit `8c30bf2`)
- CAS extraction script. Re-uses `compute_bch_prefactors.py`
  infrastructure. Output is the source of truth for `bch_quintic_term`.
- Verifies degree 1 = a + b and degree 2 = ½(ab - ba) match the H1
  form before extracting Z₅. Prints both NC-polynomial form, grouped
  Lean expression form, and the LCM-720 integer-coefficient form.

**Remaining for full B1.c (5 steps) — see below.**

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

2. **[DONE session 13]** `bch_quintic_term 𝕂 a b : 𝔸` — the τ⁵ coefficient
   of `bch(a, b)`. Defined as 30 explicit 5-letter words on `{a, b}`
   grouped by absolute coefficient (4 sub-groups: 1/4/6/24). Extracted
   by CAS at `Lean-Trotter/scripts/extract_bch_z5.py`.

3. **[DONE session 13]** `bch_quintic_term_smul` — `c⁵` homogeneity.

4. **[DONE session 13]** `norm_bch_quintic_term_le` — `‖Z₅(a,b)‖ ≤ s⁵`.

5. **[NEXT, partial progress]** `quintic_identity` — analog of
   `quartic_identity` (Basic.lean:1898), one degree higher. **Genuinely
   the hardest technical step left.**

   Confirmed LHS form (verified via CAS substitution check at
   `Lean-Trotter/scripts/discover_quintic_identity.py`, rev 9ee89b4):
   ```
   LHS = ½W_H1 + ⅓y³ - ¼y⁴ + ⅕y⁵ - C₃ - C₄ - C₅
   ```
   substituting ea → exp(a)_6, eb → exp(b)_6 gives a polynomial in
   {a, b} with all degrees ≤5 vanishing (only 64 degree-6 terms remain).

   **Parametric RHS solver attempt (rev fb5a735, then iterated to ~133
   basis elements in current session 13)**: progressively tried 17,
   then 61, then 86, then 115, then 131-133 candidate basis (G's, F's,
   cross-products, P·X, z·Y, sandwich D-D-D triples, F-sandwich
   sandwiches like aF₂a, bF₁b, ba·D₁·ba; explicit a^k·D_m·a^l for k+l=4
   and a·D₂·a·D₂·a alternations; y² and y³ direct). All attempts:
   **INCONSISTENT — basis insufficient.**

   Diff-driven analysis after each iteration narrowed down what's
   missing. With 131 elements (last attempt session 13):
   - 0 monomials uncovered (every LHS_full monomial appears in some
     basis element's support).
   - 1 inconsistency row remains: `720·LHS[bbbba] + 720·LHS[bbbbA] = 1`,
     i.e., the basis can produce bbbba and bbbbA only in COUPLED form
     (e.g., bbbbD₁ = bbbbA - bbbb - bbbba), so it can't simultaneously
     match LHS[bbbba] = +1/720 (from -C₅) and LHS[bbbbA] = 0.

   **Why this is structurally hard**: the LHS has pure {a, b} 5-letter
   contributions (from -C₅) of specific coefficients that the natural
   "compensated" basis (each sandwich produces COUPLED ea-monomial +
   pure-{a,b} contributions) can't isolate. The natural decomposition
   isn't "sum of sandwich elements" — it requires a more subtle
   structural identity.

   **Tried also** (rejected): switching LHS to ½W + ⅓z³ - ¼z⁴ + ⅕z⁵ -
   C₃ - C₄ - C₅ (z-powers instead of y-powers). This makes things
   worse: more pure {a, b} contributions (32 deg-5 words from ⅕z⁵
   instead of just C₅'s 30).

   **STRATEGY (a) VERIFIED — `sextic_pure_identity` holds at deg 5**
   (Lean-Trotter rev `6d029b6`, session 13):

   ```
   ½·W_subst[5] + ⅓·y³_subst[5] - ¼·y⁴_subst[5] + ⅕·y⁵_subst[5] - C₅ = 0
   ```

   Verified by CAS to give EXACTLY 0 non-zero monomials in pure {a, b}.
   Component sizes: W_subst[5] has 26 monomials, y³_subst[5]/y⁴_subst[5]
   /y⁵_subst[5] each have 32, C₅ has 30. After coefficient combination:
   identity = 0 in {a, b} algebra.

   Also re-verified the existing quintic_pure_identity at deg 4:
   `½·W_subst[4] + ⅓·y³_subst[4] - ¼·z⁴ - C₄ = 0`.

   **Key insight**: The natural extension of `quartic_identity` DOES
   exist, but at the level of SUBSTITUTED polynomials in {a, b},
   NOT at the unsubstituted {a, b, ea, eb} ring level. The earlier
   parametric search was looking for a structural decomposition where
   each summand was bounded by O(s⁶) in unsubstituted form, which is
   impossible (per the bbbba/bbbbA coupling obstruction). The
   sextic_pure_identity sidesteps this by working post-substitution.

   **Next concrete step (Lean port)**:

   Define a `private theorem sextic_pure_identity` in `BCH/Basic.lean`,
   analogous to `quintic_pure_identity` at line 2705. The Lean form:

   ```lean
   private theorem sextic_pure_identity (𝕂 : Type*) [RCLike 𝕂]
       {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (a b : 𝔸) :
       (let W5 := ⟨26-monomial polynomial in a, b⟩;
        let y3_5 := z²·T₃ + z·T₃·z + T₃·z² + z·T₂² + T₂·z·T₂ + T₂²·z;
        let y4_5 := z³·T₂ + z²·T₂·z + z·T₂·z² + T₂·z³;
        let y5_5 := z⁵;
        (2:𝕂)⁻¹ • W5 + (3:𝕂)⁻¹ • y3_5 - (4:𝕂)⁻¹ • y4_5 +
          (5:𝕂)⁻¹ • y5_5 - bch_quintic_term 𝕂 a b) = 0
   ```

   where T₂ = a·b + ½a² + ½b² (= P₂ in existing proof) and
         T₃ = ⅙a³ + ½a²b + ½ab² + ⅙b³.

   Proof: ×720 scalar clearing (LCM of 2,3,4,5 = 60; ×720 covers C₅'s
   denominator) + `noncomm_ring` on the resulting integer-coef identity.
   Total ~150 monomials at deg 5 after expansion.

   Estimated **~300-500 Lean lines** for the identity itself, plus
   downstream usage in `norm_bch_sextic_remainder_le`. Heartbeats
   probably 100M-500M (analog to quintic_pure_identity's 800M).

   **Alternative strategies** (if Tier 1 still proves too costly):
   - **(b)** Loosen B1.c bound from O(s⁷) to O(s⁵)·O(s²): ‖sym_bch -
     sym_E₃ - sym_E₅‖ ≤ ‖sym_bch - sym_E₃‖ + ‖sym_E₅‖ ≤ 10⁷·s⁵ + s⁵.
     Doesn't give the τ⁶ shape needed downstream.
   - **(c)** Lyndon-Hall basis (6 deg-5 free Lie elements).
   - **(d)** Keep axiom + proceed downstream.

6. **[After 5]** `norm_bch_sextic_remainder_le` — for `bch(a, b)`, bound:
   `‖bch(a, b) − (a+b) − ½[a,b] − cubic − quartic − quintic‖ ≤
    K·(‖a‖+‖b‖)⁶/(2−exp(s))`.
   Analog of `norm_bch_quintic_remainder_le` (Basic.lean:2326, ~800 lines).
   Strategy: extend the existing pieceA/pieceB decomposition. pieceA uses
   the new `norm_logOnePlus_sub_sub_sub_sub_sub_le`. pieceB uses the new
   `quintic_identity` to extract `bch_quintic_term`.

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
