# Lean-BCH

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 formalization of the **Baker-Campbell-Hausdorff (BCH) formula** for complete normed algebras, with applications to product formula error analysis.

## Main Results

All theorems are proved for a general complete normed algebra `𝔸` over `ℝ` or `ℂ`, with **0 sorry's**.

### Structural BCH theorem
$$e^{\mathrm{bch}(A,B)} = e^A \cdot e^B \qquad \text{for } \|A\|+\|B\| < \ln 2$$

### Commutator extraction (H1)
$$\left\| \mathrm{bch}(A,B) - (A+B) - \tfrac{1}{2}[A,B] \right\| \le \frac{10\, s^3}{2 - e^s}, \qquad s = \|A\|+\|B\|$$

where $[A,B] = AB - BA$ is the Lie bracket. This shows the leading non-commutative correction is $\frac{1}{2}[A,B]$, with a cubic remainder.

### Symmetric BCH / Strang splitting (H2)
$$\left\| \mathrm{bch}\bigl(\mathrm{bch}(\tfrac{A}{2}, B),\, \tfrac{A}{2}\bigr) - (A+B) \right\| \le 300\, s^3, \qquad s = \|A\|+\|B\| < \tfrac{1}{4}$$

The commutator $[A/2, B]$ from the two BCH applications **cancels**, leaving only a cubic remainder. This is the key property making the Strang splitting a second-order integrator.

### Supporting results
- `exp_logOnePlus`: $\exp(\log(1+x)) = 1+x$ for $\|x\| < 1$ (ODE/constancy argument)
- `logOnePlus_exp_sub_one`: $\log(1+\exp(a)-1) = a$ for $\|a\| < \ln 2$ (chain-of-neighborhoods)
- `norm_bch_sub_add_le`: $\|\mathrm{bch}(A,B) - (A+B)\| \le 3s^2/(2-e^s)$ (quadratic bound)
- Lie bracket bridge: all results restated with Mathlib's `⁅·,·⁆` notation

## Relation to Lean-Trotter

This project provides the **BCH infrastructure** for the [Lean-Trotter](https://github.com/Jue-Xu/Lean-Trotter) formalization of the Lie–Trotter product formula.

| Formula | Order | BCH result used | Project |
|---------|-------|-----------------|---------|
| Lie–Trotter: $(e^{A/n} e^{B/n})^n \to e^{A+B}$ | 1st | Direct exp bounds | [Lean-Trotter](https://github.com/Jue-Xu/Lean-Trotter) |
| Strang: $(e^{A/2n} e^{B/n} e^{A/2n})^n \to e^{A+B}$ | 2nd | **H2** (symmetric BCH, cubic error) | Lean-BCH |
| Suzuki S₄ | 4th | **H1** (commutator extraction) + higher-order BCH | Future work |

The Lean-Trotter project currently proves the first-order Lie–Trotter formula and second-order Strang splitting using direct exp bounds. The BCH approach here gives a cleaner route to higher-order splittings: the commutator extraction (H1) identifies the $[A,B]/2$ correction, and the symmetric BCH (H2) shows its cancellation in the Strang splitting. The fourth-order Suzuki integrator S₄ would require knowing the exact third-order BCH coefficient to verify the error cancellation in the S₄ composition.

## File Structure

```
BCH/
├── LogSeries.lean    ← log(1+x) series, summability, exp∘log identity (575 lines)
└── Basic.lean        ← BCH definition, all bounds, H1, H2, Lie bridge (1385 lines)
```

Total: ~1960 lines, 0 sorry's.

## Building

Requires [Lean 4](https://leanprover.github.io/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake update
lake exe cache get
lake build
```

## License

Apache 2.0
