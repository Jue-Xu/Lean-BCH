#!/usr/bin/env python3
"""
Verify the conjectured `symmetric_bch_septic_extended_hdecomp` algebraic
identity at polynomial level (degrees 0..9). The deg-9 analog of
`symmetric_bch_quintic_extended_hdecomp`.

Identity (LHS = RHS in the BCH algebra 𝕂⟨a, b⟩, modulo deg-10+):

LHS := sym_bch_cubic(a, b) − sym_cubic_poly(a, b) − sym_quintic_poly(a, b)
       − sym_septic_poly(a, b)

RHS := one of two candidate decompositions:

  CANDIDATE 1 — mirror of the 13-piece quintic hdecomp with one-degree-higher
  pieces (21 pieces total). Reuses quintic structure verbatim and adds:
  * 4 new septic-cancellation pieces (Phase B-septic: T₇ + T₈ + ½·[C₆,a'] - septic_correction)
  * 4 new octic-cancellation pieces (Phase C-septic: ½·[C₇,a'] + C₈(a',b) + C₈(a'+b,a') + (C₇(z,a') - C₇(a'+b,a')))
  * Replace R₁_sept (deg-7 R) with R₁_nonic (deg-9 R)
  * Replace R₂_sept with R₂_nonic

Where:
  a' := ½·a
  z  := bch(a', b)
  R₁_nonic = z − (a' + b) − ½·[a', b] − C₃(a',b) − C₄(a',b) − C₅(a',b) − C₆(a',b)
             − C₇(a',b) − C₈(a',b)
  R₂_nonic = bch(z, a') − (z + a') − ½·[z, a'] − C₃(z,a') − C₄(z,a') − C₅(z,a')
             − C₆(z,a') − C₇(z,a') − C₈(z,a')

Both sides should agree EXACTLY (as polynomials in a, b) up to degree 9.

Dependencies: sympy
Usage:        python3 verify_septic_extended_hdecomp.py
"""

import sympy as sp
from collections import defaultdict
from typing import Dict, Tuple


NCPoly = Dict[Tuple[int, ...], sp.Expr]


def ncpoly_zero(): return defaultdict(lambda: sp.Integer(0))
def ncpoly_from_scalar(c):
    r = ncpoly_zero(); c = sp.sympify(c)
    if c != 0: r[()] = c
    return r
def ncpoly_a():
    r = ncpoly_zero(); r[(0,)] = sp.Integer(1); return r
def ncpoly_b():
    r = ncpoly_zero(); r[(1,)] = sp.Integer(1); return r
def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items(): r[w] = r[w] + c
    for w, c in q.items(): r[w] = r[w] + c
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_scale(p, c):
    c = sp.sympify(c)
    if c == 0: return ncpoly_zero()
    return defaultdict(lambda: sp.Integer(0), {w: c * v for w, v in p.items()})
def ncpoly_sub(p, q): return ncpoly_add(p, ncpoly_scale(q, -1))
def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] = r[wp + wq] + cp * cq
    return defaultdict(lambda: sp.Integer(0), {w: c for w, c in r.items() if c != 0})
def ncpoly_truncate(p, max_degree):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= max_degree})
def ncpoly_exp(x, max_degree):
    r = ncpoly_from_scalar(1); xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        r = ncpoly_add(r, ncpoly_scale(xp, sp.Rational(1, sp.factorial(k))))
    return r
def ncpoly_log_one_plus(x, max_degree):
    r = ncpoly_zero(); xp = ncpoly_from_scalar(1)
    for k in range(1, max_degree + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), max_degree)
        sign = sp.Integer(1) if k % 2 == 1 else sp.Integer(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign / sp.Integer(k)))
    return r
def extract_degree(p, k):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) == k})
def truncate_to_degree(p, k_max):
    return defaultdict(lambda: sp.Integer(0),
                       {w: c for w, c in p.items() if len(w) <= k_max})
def bch_series(x, y, mx):
    ex = ncpoly_exp(x, mx); ey = ncpoly_exp(y, mx)
    pd = ncpoly_truncate(ncpoly_mul(ex, ey), mx)
    m1 = defaultdict(lambda: sp.Integer(0), {w: c for w, c in pd.items() if w != ()})
    return ncpoly_log_one_plus(m1, mx)


def commutator(p, q):
    return ncpoly_sub(ncpoly_mul(p, q), ncpoly_mul(q, p))


def half(p):
    return ncpoly_scale(p, sp.Rational(1, 2))


def main():
    MAX = 9  # work up to degree 9
    a = ncpoly_a(); b = ncpoly_b()
    half_a = ncpoly_scale(a, sp.Rational(1, 2))
    half_a_plus_b = ncpoly_add(half_a, b)

    # z = bch(½a, b)
    z = bch_series(half_a, b, MAX)
    # bch(z, ½a) = sym_bch_cubic (the 3-factor symmetric BCH).
    sym_bch = bch_series(z, half_a, MAX)
    # sym_bch_cubic(a, b) − (a + b) = sym_E₃ + sym_E₅ + sym_E₇ + sym_E₉ + ...
    sym_bch_minus_ab = ncpoly_sub(sym_bch, ncpoly_add(a, b))

    # sym_E_k = the degree-k contribution.
    sym_E3 = extract_degree(sym_bch_minus_ab, 3)
    sym_E5 = extract_degree(sym_bch_minus_ab, 5)
    sym_E7 = extract_degree(sym_bch_minus_ab, 7)
    sym_E9 = extract_degree(sym_bch_minus_ab, 9)
    # Even degrees should vanish (palindromic):
    for k in [2, 4, 6, 8]:
        d = extract_degree(sym_bch_minus_ab, k)
        nz = sum(1 for c in d.values() if c != 0)
        assert nz == 0, f"sym_E_{k} should be 0, got {nz} non-zero terms"
    print(f"# Palindromic: sym_E_2 = sym_E_4 = sym_E_6 = sym_E_8 = 0 ✓")
    print(f"# sym_E_3: {sum(1 for c in sym_E3.values() if c != 0)} non-zero deg-3 words")
    print(f"# sym_E_5: {sum(1 for c in sym_E5.values() if c != 0)} non-zero deg-5 words")
    print(f"# sym_E_7: {sum(1 for c in sym_E7.values() if c != 0)} non-zero deg-7 words")
    print(f"# sym_E_9: {sum(1 for c in sym_E9.values() if c != 0)} non-zero deg-9 words")

    # LHS = sym_bch_cubic − (a+b) − sym_E_3 − sym_E_5 − sym_E_7 (the deg-9+ residual).
    LHS = ncpoly_sub(sym_bch_minus_ab, sym_E3)
    LHS = ncpoly_sub(LHS, sym_E5)
    LHS = ncpoly_sub(LHS, sym_E7)
    LHS = truncate_to_degree(LHS, MAX)

    print(f"# LHS = sym_bch - (a+b) - sym_E_3 - sym_E_5 - sym_E_7")
    print(f"#   has {sum(1 for c in LHS.values() if c != 0)} non-zero terms (should all be deg-9)")
    nz_by_deg = defaultdict(int)
    for w, c in LHS.items():
        if c != 0: nz_by_deg[len(w)] += 1
    print(f"#   per-degree: {dict(nz_by_deg)}")

    # NOW the proposed RHS pieces.
    # C_k(x, y) = deg-k part of bch(x, y).
    def C(k, x, y): return extract_degree(bch_series(x, y, k), k)

    # R₁_nonic = z - (a' + b) - ½[a',b] - C_3 - C_4 - C_5 - C_6 - C_7 - C_8 (all at a',b).
    R1_nonic = ncpoly_sub(z, half_a_plus_b)
    R1_nonic = ncpoly_sub(R1_nonic, half(commutator(half_a, b)))
    for k in range(3, 9):
        R1_nonic = ncpoly_sub(R1_nonic, C(k, half_a, b))
    R1_nonic = truncate_to_degree(R1_nonic, MAX)

    # R₂_nonic = bch(z, a') - (z + a') - ½[z, a'] - C_3 - ... - C_8 (all at z, a').
    bch_outer = bch_series(z, half_a, MAX)
    R2_nonic = ncpoly_sub(bch_outer, ncpoly_add(z, half_a))
    R2_nonic = ncpoly_sub(R2_nonic, half(commutator(z, half_a)))
    for k in range(3, 9):
        # C_k uses z (a complicated series) directly. Need to recompute.
        Ck_outer = extract_degree(bch_series(z, half_a, MAX), k)
        R2_nonic = ncpoly_sub(R2_nonic, Ck_outer)
    R2_nonic = truncate_to_degree(R2_nonic, MAX)

    # DC_a = a·[a,b] - [a,b]·a
    DC_a = commutator(a, commutator(a, b))

    # symmetric_bch_quintic_correction_poly (the existing 25-term poly).
    # By definition, sym_E_5 - C_5(half_a, b) - C_5(half_a+b, half_a).
    quintic_correction = ncpoly_sub(sym_E5, C(5, half_a, b))
    quintic_correction = ncpoly_sub(quintic_correction, C(5, half_a_plus_b, half_a))

    # symmetric_bch_septic_correction_poly (the existing 117-term poly).
    septic_correction = ncpoly_sub(sym_E7, C(7, half_a, b))
    septic_correction = ncpoly_sub(septic_correction, C(7, half_a_plus_b, half_a))

    # 17-piece septic extended hdecomp (CONJECTURED).
    pieces = []

    # Group A: nonic-related (3 pieces)
    pieces.append(("R₁_nonic", R1_nonic))
    pieces.append(("R₂_nonic", R2_nonic))
    pieces.append(("½·[R₁_nonic, a']", half(commutator(R1_nonic, half_a))))

    # Group B-octic: C₈ extras (2 pieces, NEW for septic)
    pieces.append(("½·[C₈(a',b), a']", half(commutator(C(8, half_a, b), half_a))))
    pieces.append(("C₈(z,a') - C₈(a'+b, a')",
                   ncpoly_sub(extract_degree(bch_series(z, half_a, MAX), 8),
                              C(8, half_a_plus_b, half_a))))

    # Group C-quintic: Phase B deg-5 cancellation group (4 pieces, retained from quintic)
    C3_z = extract_degree(bch_series(z, half_a, MAX), 3)
    C3_outer = C(3, half_a_plus_b, half_a)
    pieces.append(("C₃(z,a') - C₃(a'+b,a') + (1/96)·[b, DC_a]",
                   ncpoly_add(ncpoly_sub(C3_z, C3_outer),
                              ncpoly_scale(commutator(b, DC_a), sp.Rational(1, 96)))))
    C4_z = extract_degree(bch_series(z, half_a, MAX), 4)
    C4_outer = C(4, half_a_plus_b, half_a)
    pieces.append(("C₄(z,a') - C₄(a'+b, a')",
                   ncpoly_sub(C4_z, C4_outer)))
    pieces.append(("½·[C₄(a',b), a']",
                   half(commutator(C(4, half_a, b), half_a))))
    pieces.append(("-quintic_correction", ncpoly_scale(quintic_correction, -1)))

    # Group D-quintic: Phase C deg-6 cancellation group (4 pieces, retained)
    pieces.append(("½·[C₅(a',b), a']",
                   half(commutator(C(5, half_a, b), half_a))))
    pieces.append(("C₆(a',b)", C(6, half_a, b)))
    pieces.append(("C₆(a'+b, a')", C(6, half_a_plus_b, half_a)))
    C5_z = extract_degree(bch_series(z, half_a, MAX), 5)
    C5_outer = C(5, half_a_plus_b, half_a)
    pieces.append(("C₅(z,a') - C₅(a'+b, a')", ncpoly_sub(C5_z, C5_outer)))

    # Group E-septic: Phase B deg-7 cancellation group (4 pieces, NEW)
    C5_z_partial = extract_degree(bch_series(z, half_a, MAX), 5)  # already used
    C6_z = extract_degree(bch_series(z, half_a, MAX), 6)
    C6_outer = C(6, half_a_plus_b, half_a)
    pieces.append(("C₇(z,a') - C₇(a'+b, a')",
                   ncpoly_sub(extract_degree(bch_series(z, half_a, MAX), 7),
                              C(7, half_a_plus_b, half_a))))
    pieces.append(("½·[C₆(a',b), a']",
                   half(commutator(C(6, half_a, b), half_a))))
    pieces.append(("-septic_correction", ncpoly_scale(septic_correction, -1)))

    # Group F-septic: Phase C deg-8 cancellation group (4 pieces, NEW)
    pieces.append(("½·[C₇(a',b), a']",
                   half(commutator(C(7, half_a, b), half_a))))
    pieces.append(("C₈(a',b)", C(8, half_a, b)))
    pieces.append(("C₈(a'+b, a')", C(8, half_a_plus_b, half_a)))
    pieces.append(("C₆(z,a') - C₆(a'+b, a')",
                   ncpoly_sub(C6_z, C6_outer)))

    # Sum all pieces.
    RHS = ncpoly_zero()
    for name, piece in pieces:
        RHS = ncpoly_add(RHS, piece)
    RHS = truncate_to_degree(RHS, MAX)

    print(f"\n# CONJECTURED RHS = sum of {len(pieces)} pieces")
    nz_by_deg = defaultdict(int)
    for w, c in RHS.items():
        if c != 0: nz_by_deg[len(w)] += 1
    print(f"#   per-degree: {dict(nz_by_deg)}")

    # Compare LHS vs RHS.
    diff = ncpoly_sub(LHS, RHS)
    diff = truncate_to_degree(diff, MAX)
    nz_diff = sum(1 for c in diff.values() if c != 0)
    print(f"\n# LHS - RHS has {nz_diff} non-zero terms (should be 0).")
    if nz_diff == 0:
        print("# ✓ Identity verified at polynomial level (degrees 0..9).")
    else:
        diff_by_deg = defaultdict(int)
        for w, c in diff.items():
            if c != 0: diff_by_deg[len(w)] += 1
        print(f"# Failed: residue per degree: {dict(diff_by_deg)}")
        # Show a few example residue terms.
        cnt = 0
        for w, c in sorted(diff.items()):
            if c != 0:
                print(f"#   {w}: {c}")
                cnt += 1
                if cnt > 10: break


if __name__ == "__main__":
    main()
