# Lean-BCH next session — B2 (symbolic 5-factor BCH composition → Childs basis)

## Context

Continuing Priority B (discharge `suzuki5_R5_identification_axiom` — the
last symbolic obstacle to converting Lean-Trotter's `bch_w4Deriv_quintic_level2`
axiom to a theorem). Prior sessions closed:

- **B1.a** (CAS extraction): 30 non-zero 5-letter words for the 3-factor
  Strang block's τ⁵ coefficient.
- **B1.b** (definition + homogeneity + norm bound): `symmetric_bch_quintic_poly`
  fully proved in `BCH/SymmetricQuintic.lean`.
- **B1.c** (quintic Taylor bridge): `norm_symmetric_bch_quintic_sub_poly_le`
  via Tier-2 axiom `symmetric_bch_quintic_sub_poly_axiom` (1 new private axiom,
  documented with Tier 1/2/3 discharge roadmap in CLAUDE.md).
- **B1.d** (per-block wrapper): `norm_strangBlock_log_sub_quintic_target_le`
  in `BCH/Palindromic.lean`. Trivial reduction via homogeneity from B1.c.

**Current state**:
- Lean-BCH `trotter-5factor-palindromic` @ rev `34fc858`. 0 sorries,
  **2 scoped private axioms**: `suzuki5_R5_identification_axiom` (P1) and
  `symmetric_bch_quintic_sub_poly_axiom` (P3, the B1.c axiom).
- Sessions 9 progress: **B2.2.a, b, c, d ALL DONE** with zero new axioms
  (full bounds for `sym_cubic_poly` and `sym_quintic_poly` on
  `(α•V+δa, β•V+δb)` inputs). Only **B2.2.e** (Childs-basis projection)
  remains.
- Lean-Trotter `main` @ rev `474ca0b`. Axioms 1 and 2 are theorems
  pinned against Lean-BCH P1. Axiom 3 (`bch_uniform_integrated`) bare.
- CAS verifier `Lean-Trotter/scripts/verify_strangblock_degree7.py`
  confirms degrees 2, 4, 6 of `log(exp(a/2)·exp(b)·exp(a/2))` vanish.
- CAS pipeline `Lean-Trotter/scripts/compute_bch_prefactors.py` already
  produces the βᵢ(p) prefactors from the Childs basis projection at
  degree 5.

## Goal of this session — B2

Close (or substantially advance) the **symbolic 5-factor BCH composition**:

```lean
private axiom suzuki5_R5_identification_axiom
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, ‖τ‖ < δ →
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖
        ≤ K * ‖τ‖ ^ 6
```

**Strategy** (this is what makes B2 multi-week):

```
       suzuki5_bch
   = bch(bch(2X, Y), 2X)                       -- M4a key step (already proved as
                                                  suzuki5_bch_eq_symmetric_bch)
   = (4X + Y) + symmetric_bch_cubic(4X, Y)     -- definitional unfolding

   = (4X + Y)
   + symmetric_bch_cubic_poly(4X, Y)
   + symmetric_bch_quintic_poly(4X, Y)
   + O((‖4X‖+‖Y‖)⁷)                            -- B1.c (= norm_symmetric_bch_quintic_sub_poly_le)
```

Each piece must be expanded to τ⁵ precision (using B1.d for `X` and `Y`),
collected on the **Childs 4-fold commutator basis** (`childsComm₁..₈`), and
matched to `suzuki5_R5 A B p = Σ βᵢ(p) · childsCommᵢ A B`.

## Sub-tasks

### B2.1 — Per-block decomposition (~2-3 days) — **DONE (session 9)**

Combine B1.d with the algebraic identity `4X+Y` to express:

```
4X + Y = τ•V + τ³·(4p³+(1-4p)³)·E_sym(A,B)
            + τ⁵·(4p⁵+(1-4p)⁵)·E_sym⁵(A,B)
            + Q(τ, A, B, p)
```

where `Q = O(τ⁷·s⁷)` is the residual. Under `IsSuzukiCubic p`, the τ³ term
vanishes (existing M4b machinery covers this).

**Implemented in session 9** (`BCH/Palindromic.lean`):
- `BCH.suzuki5_bch_quintic_coeff p := 4*p^5 + (1 - 4*p)^5` — analog of
  the existing `suzuki5_bch_cubic_coeff`.
- `BCH.strangBlock_log_target_quintic A B c τ` — per-block target
  `(cτ)•V + (cτ)³•E_sym + (cτ)⁵•E_quintic`.
- `BCH.suzuki5_targets_sum_quintic` — algebraic identity:
  `Σ_5 strangBlock_log_target_quintic = τ•V + C₃·τ³•E + C₅·τ⁵•E5`
  (proved without any axioms).
- `BCH.target_quintic_sum_4_form` — `4•T_p + T_q` restatement (no axioms).
- `BCH.norm_4X_plus_Y_sub_quintic_target_le` — the B1.d-based bound:
  `‖4X+Y - τ•V - τ³·C₃·E_sym - τ⁵·C₅·E_quintic‖ ≤ 4·10⁹·s_p⁷ + 10⁹·s_q⁷`.
  Depends on the B1.c P3 axiom only (via B1.d).
- `BCH.norm_suzuki5_bch_sub_smul_sub_quintic_le` — the **B2 stepping
  stone**: combines `suzuki5_bch_eq_symmetric_bch` with B1.c and B2.1 to
  get
  ```
  ‖suzuki5_bch − τ•V − C₃·τ³•E_sym − C₅·τ⁵•E_quintic
     − sym_cubic_poly(4X, Y) − sym_quintic_poly(4X, Y)‖ ≤ K·s⁷
  ```
  Depends on the P3 axiom only — **NOT P1**. This is significant: it means
  B2 framework produces useful intermediate results decoupled from the
  symbolic τ⁵ identification.

**Open after B2.1**: identify the residual

```
sym_cubic_poly(4X, Y) + sym_quintic_poly(4X, Y) ≡ τ⁵·suzuki5_R5 A B p + O(τ⁶)
```

(under `IsSuzukiCubic p`). This is the symbolic τ⁵ identification — the
genuine multi-week work of B2.2 + B2.3 + B2.4 below.

### B2.2 — `symmetric_bch_cubic_poly(4X, Y)` decomposition (~1 week)

Expand `symmetric_bch_cubic_poly(4X, Y)` symbolically. By definition,
`symmetric_bch_cubic_poly(a, b) = -(1/24)·[a,[a,b]] - (1/12)·[b,[a,b]] - ...`
(see `Basic.lean` line ~3565). With `a = 4X`, `b = Y`:

- Each X is `(pτ)•V + (pτ)³·E_sym + (pτ)⁵·E_sym⁵ + R₇(pτ)`, similarly Y.
- The cubic poly has degree 3 in (a, b), so the **leading τ-degree is 3**
  (each slot contributes τ¹ from the linear part).
- The **next-leading τ⁵ contribution** comes from one slot picking up the
  τ³·E_sym term while the other two stay at τ¹.

#### B2.2.a — `sym_quintic_poly(α•V, β•V) = 0` — **DONE (session 9)**

`BCH.symmetric_bch_quintic_poly_apply_smul_smul` in
`BCH/SymmetricQuintic.lean`. Each 5-letter word `xᵢ ∈ {α•V, β•V}`
collapses to `(α^k·β^(5−k))•V⁵`; the sum of word coefficients per k-group
is identically 0. Closed via `simp + ← add_smul + ring` after the 5-fold
smul-mul absorption helper `five_fold_smul_mul_eq`. Zero new axioms.

#### B2.2.b — `sym_cubic_poly(α•V, β•V) = 0` — **DONE (session 9)**

`BCH.symmetric_bch_cubic_poly_apply_smul_smul`. Trivial: the inner
commutator `(α•V)(β•V) − (β•V)(α•V) = αβ·V² − αβ·V² = 0` kills the
sym_cubic_poly definition. Zero new axioms.

#### B2.2.c — Multilinear Lipschitz for `sym_quintic_poly` — **DONE (session 9)**

`BCH.norm_symmetric_bch_quintic_poly_apply_smul_add_smul_add_le` in
`BCH/SymmetricQuintic.lean`:

```
‖sym_quintic_poly(α•V + δa, β•V + δb)‖ ≤ 2·N⁴·(‖δa‖+‖δb‖)
```

when `‖α•V‖, ‖β•V‖, ‖α•V+δa‖, ‖β•V+δb‖ ≤ N`. Built on the 5-letter
telescoping helper `word_5_diff_le` + B2.2.a vanishing + 30-term smul-diff
regrouping via `unfold + simp [smul_sub] + abel`. Numerical constant
`Σ |c_w|/5760 · 5 = 1216·5/5760 ≈ 1.056 ≤ 2`. Zero new axioms.

#### B2.2.d — Multilinear Lipschitz for `sym_cubic_poly` — **DONE (session 9)**

`BCH.norm_symmetric_bch_cubic_poly_apply_smul_add_smul_add_le` in
`BCH/Palindromic.lean`:

```
‖sym_cubic_poly(α•V + δa, β•V + δb)‖ ≤ (2/3)·(N²·D + N·D²)
```

Composes existing `norm_commutator_near_V_le` (gives
`‖[fA, fB]‖ ≤ 2·N·D + 2·D²` from `[α•V, β•V] = 0`) with
`norm_symmetric_bch_cubic_poly_le_commutator`. Zero new axioms.

#### B2.2.e — τ⁵ identification with Childs basis (~1 week)

Now with B2.2.c bound `‖sym_quintic_poly(4X, Y)‖ ≤ K·τ⁷` (since X, Y have
linear parts `(pτ)•V`, `((1-4p)τ)•V` of order τ and residuals of order
τ³), this term is absorbed in the τ⁷ residual.

The remaining contribution at τ⁵: the linear-in-residual part of
`sym_cubic_poly(4X, Y)`. Specifically, expanding the 6 3-letter words of
`sym_cubic_poly(α•V + δa, β•V + δb)` and projecting on the linear-in-δ
part (the ≥1-δ part with exactly one δ-factor):

```
sym_cubic_poly(4X, Y) at τ⁵ =
  Σ over (word, slot) with one δ-substitution
  (with (4pτ)V, ((1-4p)τ)V at non-δ slots)
```

Since each δ-factor is `(c·τ)³·E_sym(A,B)`, the resulting polynomial is a
4-fold commutator polynomial in (A, B) (3 slots filled with V = A+B and 1
slot with `E_sym(A, B)` which is itself a 3-fold commutator). Project onto
the Childs basis to identify `R5 - C₅·E_quintic`. CAS pipeline at
`compute_bch_prefactors.py` does this projection.

### B2.3 — `symmetric_bch_quintic_poly(4X, Y)` decomposition — partially absorbed by B2.2.c

Per the analysis above, the τ⁵ part of `sym_quintic_poly(4X, Y)` is **0**
(by B2.2.a after multilinear expansion). So B2.3 reduces to a triangle
inequality bound of `‖sym_quintic_poly(4X, Y)‖ ≤ K·τ⁷`, exactly the
content of B2.2.c.

### B2.4 — Childs basis projection (~3 days)

Match the combined τ⁵ coefficient to `suzuki5_R5 A B p`:

```
[per-block τ⁵ × C₅(p)·E_sym⁵]
  + [sym_cubic_poly(4X, Y) τ⁵-leading × Childs basis]
  + [sym_quintic_poly(4X, Y) τ⁵-leading × cancellation]
=
  τ⁵ · Σ_{i=1}^{8} βᵢ(p) · childsCommᵢ A B
```

The CAS pipeline (`Lean-Trotter/scripts/compute_bch_prefactors.py`)
already computes this projection symbolically. Porting it to Lean
requires expanding each piece in the Childs basis and verifying the
βᵢ(p) coefficients match.

### B2.5 — Triangle inequality assembly (~1 day)

Combine B2.1 + B2.2 + B2.3 + B2.4 + the residual bounds to prove:

```
‖suzuki5_bch − τ•V − τ⁵·suzuki5_R5‖ ≤ K·τ⁶
```

via triangle inequality on the decomposition pieces.

## Recommended workflow

1. Extend `compute_bch_prefactors.py` to print intermediate
   decompositions (per-block, sym_cubic_poly(4X,Y), sym_quintic_poly(4X,Y))
   so we can see what each piece contributes to the τ⁵ coefficient.
2. Verify the algebraic structure in Python before porting to Lean.
3. Port piece by piece: B2.1 (~3 days), B2.2 (~1 week), B2.3 (~1 week),
   B2.4 (~3 days), B2.5 (~1 day). **Total ~3-4 weeks.**

## Fallback plans

If B2 proves intractable in a single session block:

### Fallback 1: Full B2 axiom (already in place)

The P1 axiom `suzuki5_R5_identification_axiom` IS the B2 statement. Doing
nothing leaves it as is.

### Fallback 2: Partial discharge (B2.1 + B2.5 only)

Prove B2.1 and B2.5 with the τ⁵ identification deferred. Replace the
P1 axiom with a smaller `symmetric_bch_quintic_poly_4X_Y_to_R5_axiom`
asserting the τ⁵ identification specifically.

This provides incremental progress and isolates the genuinely-symbolic
work in a smaller axiom.

### Fallback 3: Hybrid (Tier 1 of B1.c discharge + skeleton B2)

Add `bch_quintic_term`, `bch_quintic_term_smul`, `norm_bch_quintic_term_le`
to `Basic.lean` (the easy parts of B1.c discharge — the hard part is the
sextic remainder bound). Set up B2 framework (definitions, target
polynomial, decomposition skeleton with sorries pending B2.2/B2.3/B2.4).

This makes incremental progress on both tracks.

## Setup

```bash
cd ~/Documents/Claude/Projects/Lean-BCH
git checkout trotter-5factor-palindromic
git pull
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build        # baseline: 0 sorries, 2 scoped private axioms
```

## Key files

- `BCH/Suzuki5Quintic.lean` — `suzuki5_R5`, βᵢ(p) prefactors,
  P1 axiom (lines 401-418), headline theorem (lines 439-444).
- `BCH/Palindromic.lean` — `suzuki5_bch`, `suzuki5_bch_eq_symmetric_bch`
  (line 1183, the M4a key step), `norm_strangBlock_log_sub_quintic_target_le`
  (B1.d, recently added).
- `BCH/SymmetricQuintic.lean` — `symmetric_bch_quintic_poly`,
  `norm_symmetric_bch_quintic_sub_poly_le` (B1.c, derived from new P3 axiom).
- `BCH/ChildsBasis.lean` — `childsComm₁..₈`, `bchFourFoldSum`.
- `Lean-Trotter/scripts/compute_bch_prefactors.py` — CAS pipeline producing
  the βᵢ(p) coefficients (already covers the τ⁵ projection at the symbolic
  level).
- `Lean-Trotter/scripts/verify_strangblock_degree7.py` — sanity-check
  CAS for B1.c statement.

## Acceptance criteria

- **Main**: `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` proved without
  the P1 axiom (i.e., P1 axiom can be removed). This corresponds to
  Lean-Trotter's `bch_w4Deriv_quintic_level2` becoming a fully-proved
  theorem (no axioms beyond Lean's 3 standard).
- `lake build` passes clean, still 0 sorries.
- If main goal not achievable in one session: report which sub-task
  (B2.1–B2.5) is closed and what's left.
- Pushed commit + rev hash for Lean-Trotter sync (Lean-Trotter's
  `Suzuki4ViaBCH.lean` axiom 1 will then close to 0 axioms).

## Time estimate

- **Conservative**: 3-4 weeks of focused work to fully discharge P1 axiom.
- **Per-session block**: 1-2 sub-tasks (~1-2 weeks of work).
- **Optimistic single-session**: B2.1 only (~2-3 days).

## What's left in the big picture after B2

- **B3** (~1 day): triangle inequality assembly (combining B1.d + B2 +
  M4b RHS bound).
- **B4** (trivial): remove the P1 axiom, then propagate to Lean-Trotter
  axiom 1 → theorem conversion.
- **Tier 1-3 of B1.c discharge** (~2-3 weeks): close the new P3 axiom
  (`symmetric_bch_quintic_sub_poly_axiom`) by adding the full sextic
  remainder + extending the cubic-template decomposition. Independent
  of B2; can happen in parallel.
- **Axiom 3 (Lean-Trotter `bch_uniform_integrated`)** (out of scope on
  this branch): order-7 BCH + R₇ + FTC-2 integration. Requires new
  `bch_septic_term` etc.

B2 is the highest-leverage remaining work — it discharges P1 and converts
Lean-Trotter axiom 1 to a theorem, which is the headline achievement.
