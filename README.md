# Lean-BCH

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 formalization of the **Baker-Campbell-Hausdorff (BCH) formula** for complete normed algebras.

**Truncated BCH to order 3:**

$$e^A \cdot e^B = e^{A + B + \frac{[A,B]}{2} + R_3}, \qquad \|R_3\| \le C(\|A\|^2\|B\| + \|A\|\|B\|^2)\, e^{\|A\|+\|B\|}$$

where $[A,B] = AB - BA$ is the ring commutator.

## Status

**Work in progress.**

## Goals

1. **Truncated BCH bounds** — Prove the first few terms of the BCH expansion with explicit error bounds in a general Banach algebra setting. Not the full infinite series (which involves Bernoulli numbers and iterated commutators), but enough for applications.

2. **Symmetric BCH** — Prove $e^{A/2} e^B e^{A/2} = e^{A+B+c_3[A,[A,B]]+O(\|A\|^3\|B\|)}$ with explicit $c_3$.

3. **Bridge Lie algebra ↔ exp** — Connect Mathlib's algebraic Lie bracket `⁅·,·⁆` (`Mathlib.Algebra.Lie`) to the analytic exponential (`Mathlib.Analysis.Normed.Algebra.Exponential`).

## Applications

- [Lean-Trotter](https://github.com/Jue-Xu/Lean-Trotter): Fourth-order Suzuki formula (requires the symmetric BCH to show third-order error cancellation)
- Lie group integrators, Magnus expansion, Zassenhaus formula

## Building

Requires [Lean 4](https://leanprover.github.io/) (v4.29.0-rc8) and [Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake update
lake exe cache get
lake build
```

## License

Apache 2.0
