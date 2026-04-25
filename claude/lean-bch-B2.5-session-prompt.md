# Lean-BCH next session — B2.5 (triangle-inequality bound assembly for P1 discharge)

## Context

Continuing Priority B (discharge `suzuki5_R5_identification_axiom` — the
last symbolic obstacle to converting Lean-Trotter's `bch_w4Deriv_quintic_level2`
axiom to a theorem). Session 10 closed **all symbolic content** of B2.2.e
and the algebraic backbone of P1 discharge. What remains is purely
**triangle-inequality bound assembly** — mechanical, well-defined, ~100 lines.

## State at start of this session

- Lean-BCH `trotter-5factor-palindromic` @ rev `8a4b1dc`. 0 sorries,
  **2 scoped private axioms**: `suzuki5_R5_identification_axiom` (P1)
  and `symmetric_bch_quintic_sub_poly_axiom` (P3, the B1.c axiom).
- Lean-Trotter `main` @ rev `474ca0b`. Axioms 1 and 2 are theorems
  pinned against Lean-BCH P1. Axiom 3 (`bch_uniform_integrated`) bare.

## Session 10 closures (cornerstone work — all zero new axioms)

### Symbolic Childs-basis projections

- `BCH.comm_V_V_symmetric_bch_cubic_poly_eq_childs_basis`:
  `24 • [V,[V,sym_E_3]] = (C₁+C₃+C₅+C₇) + 2 • (C₂+C₄+C₆+C₈)`.
  Strategy: split monolithic noncomm_ring into 3 small ring identities.

- `BCH.smul_5760_symmetric_bch_quintic_poly_eq_childs_basis`:
  `5760 • E_5 = -7C₁ -12C₂ +16C₄ -16C₅ -48C₆ -8C₈`.
  Coefficients via Gauss-Jordan symbolic solve (`/tmp/extract_E5_childs.py`,
  Jacobi free params = 0). Proof: `Algebra.smul_def + map_intCast/map_ofNat
  + noncomm_ring` on ~126 monomials.

- `BCH.childsComm₂_eq_childsComm₃` and `BCH.childsComm₆_eq_childsComm₇`:
  Jacobi relations as exact ring identities (via noncomm_ring).

### Cornerstone matching identity ⭐⭐

- `BCH.L_leading_plus_E5_eq_R5`:
  `((1/3)·poly_p) • [V,[V,E_3]] + (4p⁵+(1-4p)⁵) • E_5 = suzuki5_R5 A B p`
  under `IsSuzukiCubic p`, where `poly_p := p(1-4p)(1-2p)(p²-(1-4p)²)`.

  Strategy: Apply Childs projections + Jacobi to merge over-complete
  basis elements, then 6 per-Cᵢ polynomial identities via
  `linear_combination * hcubic'` with CAS-derived multipliers (e.g.
  `41p²/5760 - 29p/7200 - 169/144000` for C₁), then `module` closes.

### τ⁵-scaled corollary + B2.5 algebraic backbone

- `BCH.sym_cubic_linear_part_τ5_plus_E5_τ5_eq_R5_τ5`: τ⁵-scaled form.

- `BCH.suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic` ⭐⭐:

  ```
  suzuki5_bch ℝ A B p τ - τ • (A + B) - τ⁵ • suzuki5_R5 A B p =
    (suzuki5_bch - τ•V - (τ³·c)·E_3 - (τ⁵·γ5)·E_5
                - sym_cubic_poly(4X, Y) - sym_quintic_poly(4X, Y))
    + (sym_cubic_poly(4X, Y) -
       sym_cubic_poly_linear_part_smul_V V (4pτ) ((1-4p)τ)
         (4(pτ)³ • E_3) (((1-4p)τ)³ • E_3))
    + sym_quintic_poly(4X, Y)
  ```

  where `X = strangBlock_log A B p τ`, `Y = strangBlock_log A B (1-4p) τ`,
  `c = suzuki5_bch_cubic_coeff` (= 0 under IsSuzukiCubic),
  `γ5 = suzuki5_bch_quintic_coeff = 4p⁵+(1-4p)⁵`. Zero new axioms.

  Proof: applies hcubic to zero the τ³·c·E_3 term, then substitutes
  the τ⁵-scaled matching identity via `← hmatch`, then `abel`.

## Goal of this session — B2.5

**Convert `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le` from axiom-derived to
a real theorem proof.** This will discharge the `suzuki5_R5_identification_axiom`
(P1), reducing Lean-BCH's axiom count from 2 to 1 (just P3 = B1.c remains).

The axiom statement (in `BCH/Suzuki5Quintic.lean` HeadlineTheorem section):

```lean
private axiom suzuki5_R5_identification_axiom
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, ‖τ‖ < δ →
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖
        ≤ K * ‖τ‖ ^ 6
```

## Strategy (mechanical, no more symbolic ingenuity)

Apply triangle inequality to the algebraic decomposition:

```
‖suzuki5_bch - τ•V - τ⁵•R₅‖ ≤ ‖T₁‖ + ‖T₂‖ + ‖T₃‖
```

where:

- **T₁** = R_b1c (B1.c residual after hcubic τ³ vanishing) — bounded by
  `BCH.norm_suzuki5_bch_sub_smul_sub_quintic_le` (already in
  `BCH/Palindromic.lean`, gives O(σ_p⁷ + σ_q⁷ + σ_total⁷)).

- **T₂** = `sym_cubic_poly(4X, Y) - L_leading_τ⁵`. Bounded via:
  - `BCH.norm_sym_cubic_poly_sub_linear_part_le` (B2.2.e residual on full L).
  - L_extra bound: `‖L - L_leading_τ⁵‖` via bilinearity of L in (δa, δb)
    and `BCH.norm_strangBlock_log_sub_target_le` (B1.a cubic bound on
    R_p := strangBlock_log_p − target_p giving 10⁷·σ_p⁵ tail).

- **T₃** = `sym_quintic_poly(4X, Y)`. Bounded by
  `BCH.norm_symmetric_bch_quintic_poly_le` applied with `(a, b) = (4X, Y)`,
  giving `(‖4X‖ + ‖Y‖)⁵`.

### Step 1: Bound `‖sym_cubic_poly(4X, Y) - L_leading_τ⁵‖` (the only "new" bound)

Add a helper lemma (in `BCH/Palindromic.lean`):

```lean
include 𝕂 in
theorem norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le (A B : 𝔸) (p τ : 𝕂)
    (hp : ‖(p * τ) • A‖ + ‖(p * τ) • B‖ < 1 / 4)
    (h1m4p : ‖((1 - 4 * p) * τ) • A‖ + ‖((1 - 4 * p) * τ) • B‖ < 1 / 4) :
    ‖symmetric_bch_cubic_poly 𝕂
        ((4 : 𝕂) • strangBlock_log 𝕂 A B p τ)
        (strangBlock_log 𝕂 A B (1 - 4 * p) τ) -
      sym_cubic_poly_linear_part_smul_V (A + B) (4 * p * τ) ((1 - 4 * p) * τ)
        ((4 * (p * τ) ^ 3) • symmetric_bch_cubic_poly 𝕂 A B)
        (((1 - 4 * p) * τ) ^ 3 • symmetric_bch_cubic_poly 𝕂 A B)‖ ≤
      <explicit polynomial bound in p, τ, ‖A‖, ‖B‖>
```

**Proof structure**:

1. Set `δa := (4 : 𝕂) • strangBlock_log p − (4pτ) • V`, `δb := strangBlock_log (1-4p) − ((1-4p)τ) • V`.
2. By definition, `(4 : 𝕂) • strangBlock_log p = (4pτ) • V + δa` and same for δb.
3. Apply `BCH.norm_sym_cubic_poly_sub_linear_part_le`:
   `‖sym_cubic_poly(α•V+δa, β•V+δb) - sym_cubic_poly_linear_part_smul_V V α β δa δb‖
    ≤ (3/2)·N·D² + (1/2)·D³`
   with N = ‖(4pτ)•V‖+‖((1-4p)τ)•V‖, D = ‖δa‖+‖δb‖.
4. By bilinearity of `sym_cubic_poly_linear_part_smul_V` in (δa, δb):
   `L − L_leading_τ⁵ = sym_cubic_poly_linear_part_smul_V V α β
        (δa − 4(pτ)³•E_3) (δb − ((1-4p)τ)³•E_3)`.
5. Bound `‖δa − 4(pτ)³•E_3‖ ≤ 4·10⁷·σ_p⁵` via `BCH.norm_strangBlock_log_sub_target_le`.
6. Triangle inequality: `‖sym_cubic_poly - L_leading_τ⁵‖ ≤ ‖sym_cubic_poly - L‖ + ‖L − L_leading_τ⁵‖`.

### Step 2: Convert the existing theorem from axiom-derived to proven

Replace:

```lean
theorem norm_suzuki5_bch_sub_smul_sub_R5_le
    (A B : 𝔸) (p : ℝ) (hcubic : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ τ : ℝ, ‖τ‖ < δ →
      ‖suzuki5_bch ℝ A B p τ - τ • (A + B) - τ ^ 5 • suzuki5_R5 A B p‖
        ≤ K * ‖τ‖ ^ 6 :=
  suzuki5_R5_identification_axiom A B p hcubic
```

with a real proof. **Template**: mirror
`BCH.suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (in Palindromic.lean,
~30 lines). Key elements:

- Set normalization constants `pn := ‖p‖+1`, `qn := ‖1-4p‖+1`,
  `s := ‖A‖+‖B‖+1`.
- Choose `δ := 1/(huge)` to ensure all per-block regimes (`hp`, `h1m4p`,
  `hreg`, `hZ1`, `hZ2`) hold; the existing M4b template gives a working
  construction.
- Choose `K := <polynomial in pn, qn, s>` to absorb all three bounds.
- Apply `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic` to rewrite the goal.
- Triangle inequality via `norm_add_le`.
- Bound each term by its corresponding upstream theorem.
- `linarith` or `nlinarith` to close.

Extract the body to a private auxiliary theorem
`norm_suzuki5_bch_sub_smul_sub_R5_le_aux` (mirroring the M4b template) to
keep kernel `whnf` within heartbeat budget.

### Step 3: Delete the private axiom

Once the theorem proof closes, delete:

```lean
private axiom suzuki5_R5_identification_axiom ...
```

and verify `#print axioms norm_suzuki5_bch_sub_smul_sub_R5_le` returns
only `[propext, Classical.choice, Quot.sound]` plus the transitive
dependency on `BCH.symmetric_bch_quintic_sub_poly_axiom` (P3, the B1.c
axiom — out of scope for this session).

### Step 4: Verify Lean-Trotter compatibility

After P1 axiom removal, Lean-Trotter at `5a2c03e` (or the tip of `main`)
which has `bch_w4Deriv_quintic_level2` as a theorem pinned against
Lean-BCH's `norm_suzuki5_bch_sub_smul_sub_R5_le` should still compile
(the public API signature is unchanged).

## Files to modify

- `BCH/Palindromic.lean`: add `norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le`
  (and any helper lemmas for the bilinearity-of-L bound).
- `BCH/Suzuki5Quintic.lean`: replace axiom + axiom-derived theorem with
  the real proof. Possibly extract aux body.
- `CLAUDE.md`: update status to reflect P1 axiom removal (1 axiom remaining).

## Verification

After each step, run `lake build BCH.Suzuki5Quintic` to verify. After
the final step, verify axiom dependency:

```lean
import BCH.Suzuki5Quintic

#print axioms BCH.norm_suzuki5_bch_sub_smul_sub_R5_le
```

Should output: `[propext, Classical.choice, Quot.sound,
BCH.symmetric_bch_quintic_sub_poly_axiom]`.

## Reference: similar existential-bound templates in the codebase

- `BCH.suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (Palindromic.lean ~3838):
  exact same pattern but for τ⁵ instead of τ⁶. **Use as scaffolding.**
- `BCH.norm_strangBlock_log_linear` (Palindromic.lean): the η-pattern
  bound `η + η³ + 10⁷·η⁵ ≤ 40002·η` for η ≤ 1/4 — useful for absorbing
  per-block argument norms.

## Key existing theorems used in the assembly

| Theorem | Purpose |
|---------|---------|
| `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic` | The structural identity (this session 10's last addition) |
| `norm_suzuki5_bch_sub_smul_sub_quintic_le` | T₁ bound (B1.c + B2.1 σ⁷) |
| `norm_sym_cubic_poly_sub_linear_part_le` | B2.2.e residual bound (Q + C) |
| `norm_strangBlock_log_sub_target_le` | B1.a per-block cubic bound (10⁷·σ⁵) |
| `norm_symmetric_bch_quintic_poly_le` | T₃ bound `(‖a‖+‖b‖)⁵` |
| `norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le` | T₂ bound (NEW, this session) |
| `commBr_smul_left_eq` / `commBr_smul_right_eq` | Bilinearity of L_leading |
| `norm_three_commBr_le` | 3-fold commutator bound `4·‖X‖·‖Y‖·‖Z‖` |

## Estimated effort

~100-200 lines of Lean. Step 1 (T₂ bound helper) is the trickier part
(~50 lines). Steps 2-3 are scaffolding (~50 lines). Step 4 is verification.

Total: 1-2 days. After this session, **Lean-BCH has only 1 scoped axiom
remaining** (P3 = B1.c quintic Taylor bridge, with its own Tier 1/2/3
discharge roadmap documented in `BCH/SymmetricQuintic.lean`).

## Optional follow-up (out of scope)

- Discharge P3 (B1.c) — Tier 1/2/3 roadmap in `BCH/SymmetricQuintic.lean`
  module header. ~3 weeks of Lean work.
- Lean-Trotter axiom 3 (`bch_uniform_integrated`) — out of scope here.
