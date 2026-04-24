# Lean-BCH — Baker-Campbell-Hausdorff in Lean 4

## Status: **All three BCH files (Basic, Palindromic, LogSeries) are sorry-free (2026-04-24).** Basic: H1, H2, M1, quintic BCH, symmetric quartic identity, alt-form, decomposition equality, all six triangle-inequality bounds (R₁, R₂, T3, T4, and the T5/T6 ring-identity bounds with the `(96)⁻¹·[b,DC_a]` cancellation), and the downstream `norm_symmetric_bch_cubic_sub_smul_le` all complete. Palindromic: M1–M4b closed, telescoping bound, exp-Lipschitz `norm_exp_add_sub_exp_le`, **M6 Trotter h4 theorem** `norm_s4Func_sub_exp_le_of_IsSuzukiCubic` — `‖s4Func(t/n, n) - exp(t•(A+B))‖ = O(|t|⁵·s⁵/n⁴)` under IsSuzukiCubic — and **M4b RHS quintic corollary** `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (∃ δ, K, ∀ τ < δ, RHS ≤ K·‖τ‖⁵), which is the payoff lemma for downstream Lean-Trotter.

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

None across all three files (verified 2026-04-24). The repository is fully
sorry-free. The most recent closure was the M4b RHS quintic corollary
`suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (commit `9ffaab4`), proving
the existence of `δ > 0` and `K ≥ 0` such that `suzuki5_bch_M4b_RHS A B p τ
≤ K·‖τ‖⁵` whenever `‖τ‖ < δ`. Strategy: choose `δ = 1/(5·pn·qn·s)` with
`pn = ‖p‖+1`, `qn = ‖1-4p‖+1`, `s = ‖A‖+‖B‖+1`; bound each of the four
unfolded terms separately via `pow_le_pow_left₀`, the new helper
`norm_strangBlock_log_linear` (η + η³ + 10⁷·η⁵ ≤ 40002·η for η ≤ 1/4),
and `gcongr`. Body extracted to private `suzuki5_bch_M4b_RHS_le_t5_aux`
to keep kernel `whnf` within heartbeat budget (16M).

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
├── LogSeries.lean    ← log(1+x) series definition, summability, exp∘log = id
├── Basic.lean        ← exp bounds, BCH definition, H1, H2, Lie bracket bridge
└── Palindromic.lean  ← Suzuki-5 palindromic product, M1–M4b, M6 Trotter h4
```
