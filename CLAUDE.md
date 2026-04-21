# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status: H1, H2, M1, quintic BCH, symmetric E₃-extraction complete; 1 sorry remains (symmetric quintic remainder)

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

### `norm_symmetric_bch_cubic_sub_poly_le` (line ~3669)
- **Statement:** `‖sym_bch_cubic(a,b) - sym_E₃(a,b)‖ ≤ 4000·s⁵` where
  `sym_E₃(a,b) = -(1/24)·[a,[a,b]] + (1/12)·[b,[b,a]]` is the cubic-polynomial
  part of the symmetric BCH expansion (definition `symmetric_bch_cubic_poly`).
- **Downstream consumer:** `norm_symmetric_bch_cubic_sub_smul_le` small-s case
  — now uses this theorem + `symmetric_bch_cubic_poly_smul` (homogeneity, ✓)
  to close `‖E₃(ca,cb) - c³E₃(a,b)‖ ≤ 10000|c|³s⁵`.
- **Proof plan (not yet formalized, ~200 lines):**
  1. Apply `norm_bch_quintic_remainder_le` to `(½a, b)` → bound on inner BCH.
  2. Apply `norm_bch_quintic_remainder_le` to `(bch(½a,b), ½a)` → bound on outer BCH.
  3. Combine; extract the degree-3 part (= `symmetric_bch_cubic_poly`) via the
     algebraic identity `sym_E₃ = C₃(½a,b) + (1/16)[[a,b],a] + C₃(½a+b, ½a)`
     (which simplifies to the closed-form `-(1/24)[a,[a,b]] + (1/12)[b,[b,a]]`
     as verified algebraically).
  4. Bound the residual degree-4+ terms via norm-grouping analogous to the
     `pieceB'` analysis in `norm_bch_quintic_remainder_le`. Degree-4 contributions
     cancel as a ring identity by the oddness of the symmetric BCH.
- **Depends on:** `bch_cubic_term_smul` (✓), `symmetric_bch_cubic_neg` (✓),
  `norm_bch_quintic_remainder_le` (✓).

## File Structure

```
BCH/
├── LogSeries.lean    ← log(1+x) series definition, summability, exp∘log = id
└── Basic.lean        ← exp bounds, BCH definition, H1, H2, Lie bracket bridge
```
