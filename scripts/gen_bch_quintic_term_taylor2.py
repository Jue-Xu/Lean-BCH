#!/usr/bin/env python3
"""
Generate Lean code for the second-order Taylor expansion of bch_quintic_term:

    bch_quintic_term(x + V, y) - bch_quintic_term(x, y)
       = bch_quintic_term_lin_diff(x, V, y) + bch_quintic_term_taylor2_remainder(x, V, y)

where:
* lin_diff(x, V, y) = Σ_w c_w · Σ_{i ∈ x-positions of w} word_with_V_at_i(x, V, y, w)
  — the directional derivative, 75 terms in {x, V, y}.
* taylor2_remainder(x, V, y) = sum of all terms with ≥ 2 V's after the substitution
  — 105 terms in {x, V, y}, broken down as k=2 (70), k=3 (30), k=4 (5).

These match identities support discharging the τ⁷ axiom via second-order
Taylor remainder bounds at specialized (x, V, y) = (½a+b, V_j, ½a) instances.
"""

import sympy as sp
from collections import defaultdict
from itertools import combinations
import sys


# ---- BCH computation in {a, b} polynomial ring ----

def ncpoly_zero(): return defaultdict(lambda: sp.Integer(0))
def ncpoly_from_scalar(c):
    r = ncpoly_zero(); c = sp.sympify(c)
    if c != 0: r[()] = c
    return r
def ncpoly_a(): r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r
def ncpoly_b(): r = ncpoly_zero(); r[(1,)] = sp.Integer(1); return r
def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items(): r[w] = r[w] + c
    for w, c in q.items(): r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0: return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0), {w: c * v for w, v in p.items()})
def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_truncate(p, mx):
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in p.items() if len(w) <= mx})
def ncpoly_exp(x, mx):
    r = ncpoly_from_scalar(1); xp = ncpoly_from_scalar(1)
    for k in range(1, mx+1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), mx)
        r = ncpoly_add(r, ncpoly_scale(xp, sp.Rational(1, sp.factorial(k))))
    return r
def ncpoly_log_one_plus(x, mx):
    r = ncpoly_zero(); xp = ncpoly_from_scalar(1)
    for k in range(1, mx+1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), mx)
        sign = sp.Integer(1) if k%2==1 else sp.Integer(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign/sp.Integer(k)))
    return r
def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in p.items() if len(w) == k})
def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


# ---- Taylor expansion in {x=0, V=1, y=2} alphabet ----

def substitute_at(w, positions, replacement_atom):
    result = list(w)
    for i in positions:
        result[i] = replacement_atom
    return tuple(result)

def word_in_xVy(w_in_xy):
    """Map atom 0(x) -> 0, atom 1(y) -> 2."""
    return tuple(0 if a == 0 else 2 for a in w_in_xy)

def lin_diff_poly(bch_poly):
    """Σ_w c_w · Σ_{i: w[i]=0} word_with_V_at_i (one V per term)."""
    result = ncpoly_zero()
    for w, c in bch_poly.items():
        if c == 0: continue
        w_xVy = word_in_xVy(w)
        x_positions = [i for i, a in enumerate(w) if a == 0]
        for i in x_positions:
            new_w = substitute_at(w_xVy, [i], 1)
            result[new_w] = result[new_w] + c
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in result.items() if c != 0})

def taylor2_remainder_poly(bch_poly):
    """For each word, sum substituting V at each subset of x-positions of size ≥ 2."""
    result = ncpoly_zero()
    for w, c in bch_poly.items():
        if c == 0: continue
        w_xVy = word_in_xVy(w)
        x_positions = [i for i, a in enumerate(w) if a == 0]
        for k in range(2, len(x_positions) + 1):
            for S in combinations(x_positions, k):
                new_w = substitute_at(w_xVy, S, 1)
                result[new_w] = result[new_w] + c
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in result.items() if c != 0})


# ---- Lean emission ----

def word_lean(w):
    """Map atom 0(x)→'x', 1(V)→'V', 2(y)→'y' to Lean letter symbols."""
    return ' * '.join(['x', 'V', 'y'][a] for a in w)

def emit_def(name, items, lcm, doc):
    """Emit a Lean noncomputable def with explicit polynomial form."""
    print(f"/-- {doc} -/")
    print(f"noncomputable def {name} (𝕂 : Type*) [RCLike 𝕂]")
    print(f"    {{𝔸 : Type*}} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (x V y : 𝔸) : 𝔸 :=")
    first = True
    for w, c in sorted(items, key=lambda kv: kv[0]):
        n = int(sp.nsimplify(c * lcm))
        prefix = "    " if first else "  + "
        print(f"{prefix}({n} / {lcm} : 𝕂) • ({word_lean(w)})")
        first = False
    print()


def main():
    a, b = ncpoly_a(), ncpoly_b()
    bch_to_5 = bch_series(a, b, 5)
    bch_5 = extract_degree(bch_to_5, 5)

    lin = lin_diff_poly(bch_5)
    sec = taylor2_remainder_poly(bch_5)

    def lcm_of(p):
        nz = [(w, c) for w, c in p.items() if c != 0]
        if not nz: return 1
        L = 1
        for _, c in nz: L = sp.lcm(L, sp.denom(sp.nsimplify(c)))
        return int(L)

    lin_items = [(w, c) for w, c in lin.items() if c != 0]
    sec_items = [(w, c) for w, c in sec.items() if c != 0]
    lin_lcm = lcm_of(lin)
    sec_lcm = lcm_of(sec)

    sys.stderr.write(f"# lin_diff: {len(lin_items)} terms, LCM = {lin_lcm}\n")
    sys.stderr.write(f"# taylor2_remainder: {len(sec_items)} terms, LCM = {sec_lcm}\n")

    emit_def(
        "bch_quintic_term_lin_diff",
        lin_items, lin_lcm,
        "First-order directional difference of `bch_quintic_term` in its first "
        "argument: Σ_w c_w · Σ_{i ∈ x-positions of w} word_with_V_at_i. 75 terms in {x, V, y}."
    )

    emit_def(
        "bch_quintic_term_taylor2_remainder",
        sec_items, sec_lcm,
        "Second-order Taylor remainder of `bch_quintic_term` in its first argument: "
        "sum over each word in bch_quintic_term of substitutions placing V at ≥ 2 "
        "of the word's x-positions. 105 terms in {x, V, y} (k=2: 70, k=3: 30, k=4: 5)."
    )

    # The matching identity statement.
    print("/-- **Second-order Taylor matching identity for `bch_quintic_term`**:")
    print()
    print("    bch_quintic_term(x + V, y) - bch_quintic_term(x, y)")
    print("       = bch_quintic_term_lin_diff(x, V, y)")
    print("         + bch_quintic_term_taylor2_remainder(x, V, y).")
    print()
    print("The decomposition isolates the linear-in-V part (`lin_diff`, sum over")
    print("single-V substitutions at each x-position of each bch_quintic_term word)")
    print("from the higher-order-in-V remainder (`taylor2_remainder`, sum over")
    print("multi-V substitutions). Every term of `taylor2_remainder` has at least")
    print("2 factors of V, enabling a `‖.‖ ≤ K·M³·‖V‖²` bound. -/")
    print("theorem bch_quintic_term_taylor2_decomp (𝕂 : Type*) [RCLike 𝕂]")
    print("    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] (x V y : 𝔸) :")
    print("    bch_quintic_term 𝕂 (x + V) y - bch_quintic_term 𝕂 x y =")
    print("      bch_quintic_term_lin_diff 𝕂 x V y +")
    print("      bch_quintic_term_taylor2_remainder 𝕂 x V y := by")
    print("  unfold bch_quintic_term bch_quintic_term_lin_diff bch_quintic_term_taylor2_remainder")
    print("  unfold bch_quintic_group_1 bch_quintic_group_4 bch_quintic_group_6 bch_quintic_group_24")
    print("  simp only [neg_mul, mul_neg, neg_neg, neg_smul, smul_neg,")
    print("             smul_sub, smul_add, smul_smul, mul_smul_comm, smul_mul_assoc,")
    print("             mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc, sub_neg_eq_add]")
    print("  match_scalars <;> ring")


if __name__ == "__main__":
    main()
