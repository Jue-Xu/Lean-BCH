# Lean-BCH next session — B2.5 P1 axiom discharge (assembly + regime derivation)

## Context

Continuing Priority B (discharge `suzuki5_R5_identification_axiom`).
Session 11 closed the **T₂ bound** for the τ⁶ assembly along with all
supporting infrastructure. What remains is **(a) regime-hypothesis
derivation** and **(b) the final triangle-inequality assembly**.

## State at start of this session

- Lean-BCH `trotter-5factor-palindromic` @ tip. 0 sorries, **2 scoped
  private axioms**: `suzuki5_R5_identification_axiom` (P1) and
  `symmetric_bch_quintic_sub_poly_axiom` (P3, B1.c).
- All session 10 closures + **session 11 T₂ bound + helpers**.

## Session 11 closures (all zero new axioms, in `BCH/Palindromic.lean`)

### Foundation helpers

- `BCH.commBr_sub_right_eq` (private): `[X, Y₁ - Y₂] = [X, Y₁] - [X, Y₂]`.
- `BCH.sym_cubic_poly_linear_part_smul_V_sub_eq`: bilinearity of `L`,
  ```
  L(V, α, β, δa1, δb1) - L(V, α, β, δa2, δb2) = L(V, α, β, δa1-δa2, δb1-δb2).
  ```
- `BCH.norm_sym_cubic_poly_linear_part_smul_V_le`: scalar bound on `L`,
  ```
  ‖L(V, α, β, δa, δb)‖ ≤ (1/6)·‖α + 2β‖·‖V‖²·(‖β‖·‖δa‖ + ‖α‖·‖δb‖).
  ```
- `BCH.strangBlock_residue_eq_smul_X_sub_target`: per-block residue
  identity,
  ```
  (4 : 𝕂) • X - (4*p*τ) • (A+B) - (4*(p*τ)^3) • E_3 =
    (4 : 𝕂) • (X - strangBlock_log_target 𝕂 A B p τ).
  ```

### B2.5 assembly under regime hypotheses ⭐⭐ (in `BCH/Suzuki5Quintic.lean`)

- `BCH.norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime` (private):
  given the 6 regime hypotheses + `IsSuzukiCubic p`, produces an explicit
  polynomial bound on `‖suzuki5_bch − τ•V − τ⁵•R₅‖`. Combines T₁, T₂, T₃
  via `suzuki5_bch_sub_R5_decomp_of_IsSuzukiCubic` + triangle inequality.

  Bound shape: `poly_T1 + poly_T2 + 2·N⁴·D` where N = sum of basic norms,
  D = sum of per-block residual norms. Zero new axioms.

### B2.5 T₂ main bound ⭐⭐

- `BCH.norm_sym_cubic_poly_at_strangBlock_sub_L_leading_τ5_le`: the τ⁶
  assembly's **T₂ bound**. Closed-form polynomial bound:
  ```
  ‖sym_cubic_poly(4X, Y) - L_leading_τ⁵‖ ≤
    (3/2)·N·D² + (1/2)·D³ +
    (1/6)·‖4pτ + 2(1-4p)τ‖·‖A+B‖² ·
      (‖(1-4p)τ‖·4·10⁷·σ_p⁵ + ‖4pτ‖·10⁷·σ_q⁵)
  ```
  where `N = ‖(4pτ)•(A+B)‖ + ‖((1-4p)τ)•(A+B)‖`,
  `D = ‖4X − (4pτ)•(A+B)‖ + ‖Y − ((1-4p)τ)•(A+B)‖`,
  `σ_p = ‖(pτ)•A‖+‖(pτ)•B‖`, `σ_q = ‖((1-4p)τ)•A‖+‖((1-4p)τ)•B‖`.

  For the τ⁶ assembly, this bound is `O(τ⁷)`: with α, β = O(τ),
  N = O(τ), D = O(τ³), σ_p, σ_q = O(τ), the QC term is `O(τ·τ⁶) = O(τ⁷)`
  and the L_extra term is `O(τ·τ²·τ⁵) = O(τ⁸)` (dominated by QC).

## Goal of this session

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

## Strategy

### Step 1: Regime-hypothesis derivation (~150-200 lines)

Choose δ small enough that ‖τ‖ < δ implies all 6 regime hypotheses:
- `hp`, `h1m4p`: `‖(c·τ)•A‖ + ‖(c·τ)•B‖ < 1/4` for c ∈ {p, 1-4p}.
- `hreg`: `‖4·X‖ + ‖Y‖ < 1/8` (tighter than 1/4 to support hZ2).
- `hR`: `suzuki5ArgNormBound A B p τ < log(5/4) ≈ 0.223` (tighter for hZ1).
- `hZ1`: `‖suzuki5_bch ℝ A B p τ‖ < log 2`.
- `hZ2`: inner bch's norm < log 2.

Recommended δ choice: `δ = 1/(10⁹ * pn * qn * s)` where
`pn = ‖p‖+1, qn = ‖1-4p‖+1, s = ‖A‖+‖B‖+1`.

#### Sub-step 1a: Easy regimes (hp, h1m4p, hreg, hR)
Mirror the M4b template's `suzuki5_bch_M4b_RHS_le_t5_aux` regime
derivation (Palindromic.lean ~3303). Key lemmas:
- `norm_smul_le` for η_p, η_q ≤ pn·s·|τ|, qn·s·|τ|.
- `norm_strangBlock_log_linear` for ‖X‖ ≤ 40002·η_p (already proved).
- `suzuki5ArgNormBound` definition unfolds to a polynomial in p, A, B norms.

#### Sub-step 1b: hZ1 derivation
From R < log(5/4):
1. `norm_suzuki5Product_sub_one_le`: `‖suzuki5Product - 1‖ ≤ exp(R) - 1`.
2. exp(R) - 1 ≤ exp(log(5/4)) - 1 = 1/4 (with strict inequality since R is strict).
3. `norm_logOnePlus_le`: `‖logOnePlus(x)‖ ≤ ‖x‖/(1-‖x‖)` for ‖x‖ < 1.
4. With ‖x‖ ≤ 1/4 < 1: `‖suzuki5_bch‖ = ‖logOnePlus(suzuki5Product - 1)‖ ≤ (1/4)/(3/4) = 1/3 < log 2 ≈ 0.693`. ✓

#### Sub-step 1c: hZ2 derivation
With ‖4X‖ + ‖Y‖ < 1/8, the inner bch arg sum is `2‖X‖ + ‖Y‖ < 1/8`.
1. Apply `norm_bch_sub_add_le`: `‖bch(½(4X), Y) - (½(4X) + Y)‖ ≤ 3·s²/(2-eˢ)` with s = ‖½(4X)‖+‖Y‖.
2. For s < 1/8: `3·(1/8)²/(2-e^(1/8)) ≈ 0.054`.
3. `‖bch_inner‖ ≤ ‖½(4X)+Y‖ + 0.054 ≤ 1/8 + 0.054 ≈ 0.18`.
4. Outer bch arg sum: `‖bch_inner‖ + ‖½(4X)‖ ≤ 0.18 + 1/8 ≈ 0.305 < log 2 ≈ 0.693`. ✓

### Step 2: Triangle-inequality assembly — **DONE in session 11**

The assembly helper `norm_suzuki5_bch_sub_smul_sub_R5_le_under_regime`
in `BCH/Suzuki5Quintic.lean` closes this step. Just needs:
1. The 6 regime hypotheses derived in step 1 above.
2. `IsSuzukiCubic p`.
3. Plug them in.

### Step 3: Polynomial bookkeeping (~100 lines)

Bound each of T₁, T₂, T₃ by a polynomial in pn, qn, s, |τ|, and
absorb into K·|τ|⁶. Mirror the `suzuki5_bch_M4b_RHS_le_t5_aux`
template (Palindromic.lean ~3303).

For ‖τ‖ ≤ 1 (which holds since δ < 1/(10⁹·pn·qn·s) ≤ 1):
- T₁ ≤ huge·pn⁷·qn⁷·s⁷·|τ|⁷ ≤ huge·pn⁶·qn⁶·s⁶·|τ|⁶
- T₂ ≤ huge·pn¹¹·qn¹¹·s¹¹·|τ|⁷ (dominated by QC bound)
- T₃ ≤ huge·pn⁴·qn⁴·s⁴·|τ|⁷ (dominated by N⁴·D)

K = sum of the leading polynomial coefficients.

### Step 4: Delete the axiom + verify

Once the theorem proves, delete:
```lean
private axiom suzuki5_R5_identification_axiom ...
```
and verify `#print axioms norm_suzuki5_bch_sub_smul_sub_R5_le` returns
only `[propext, Classical.choice, Quot.sound,
BCH.symmetric_bch_quintic_sub_poly_axiom]` (only P3 = B1.c remains).

## Files to modify

- `BCH/Suzuki5Quintic.lean`: replace `norm_suzuki5_bch_sub_smul_sub_R5_le`'s
  body with the real proof. Possibly extract aux body to private lemma.
- `BCH/Palindromic.lean`: optionally add private aux lemmas for regime
  derivation (or inline in the public theorem).
- `CLAUDE.md`: update status to reflect P1 axiom removal.

## Reference: similar existential-bound templates

- `BCH.suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (Palindromic.lean ~3838):
  exact same pattern but for τ⁵ instead of τ⁶. **Use as scaffolding.**
  Key technique: `set pn := ‖p‖+1, qn := ‖1-4p‖+1, s := ‖A‖+‖B‖+1`,
  then `δ := 1/(5*pn*qn*s)`, derive hp, h1m4p inline.

- `BCH.norm_strangBlock_log_linear` (Palindromic.lean ~3267): the
  η-pattern bound `η + η³ + 10⁷·η⁵ ≤ 40002·η` for η ≤ 1/4.

## Estimated effort

~300-400 lines of Lean. Step 1 (regime derivation) is the trickiest part.

## Optional follow-up (out of scope)

- Discharge P3 (B1.c) — Tier 1/2/3 roadmap in
  `BCH/SymmetricQuintic.lean` module header.
- Lean-Trotter axiom 3 (`bch_uniform_integrated`).
