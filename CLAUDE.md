# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status: H1, H2, M1 complete; 2 sorry's remain (quintic BCH + symmetric quintic)

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

### `norm_bch_quintic_remainder_le` (line ~2296)
- **Statement:** `‖bch(a,b)-(a+b)-½[a,b]-C₃-C₄‖ ≤ 3000s⁵/(2-eˢ)`
- **Approach:** Decompose pieceB' using quartic_identity, then bound the degree-4+
  terms via norm grouping. The key groups:
  1. Pure quintic terms: `G₁+G₂, aF₂+F₁b, ½a²E₂+½E₁b², E₁E₂` — each `O(s⁵)`
  2. Cross terms: `-½(zT₄+T₄z)` where `T₄ = S-R₃` — `O(s·s⁴) = O(s⁵)`
  3. Degree-4 group: `{-½P² + ⅓(z²P+zPz+Pz²) + pure_deg4 - ¼z⁴ - C₄}`
     — collectively `O(s⁵)` since bch(ta,tb) = tZ₁+t²Z₂+t³Z₃+t⁴Z₄+O(t⁵)
     and C₄ is exactly Z₄. The degree-4 terms are NOT zero as a ring identity
     but their NORM is `O(s⁵)` via the BCH expansion structure.
  4. Higher-P terms: `⅓(zP²+PzP+P²z+P³), -¼(y⁴ terms)` — `O(s²·s³) = O(s⁵)`
- **Infrastructure:** All quintic log/exp bounds already proved.

### `norm_symmetric_bch_cubic_sub_smul_le` (line ~2819)
- **Statement:** `‖E₃(ca,cb) - c³E₃(a,b)‖ ≤ 10000|c|³s⁵`
- **Depends on:** quintic BCH + oddness (`symmetric_bch_cubic_neg`, already proved).

## File Structure

```
BCH/
├── LogSeries.lean    ← log(1+x) series definition, summability, exp∘log = id
└── Basic.lean        ← exp bounds, BCH definition, H1, H2, Lie bracket bridge
```
