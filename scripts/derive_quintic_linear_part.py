"""Derive the closed form for the linear-in-delta part of
symmetric_bch_quintic_poly(alpha*V + da, beta*V + db).

symmetric_bch_quintic_poly = E_5 is a Lie polynomial. So substituting
a -> alpha*V + da, b -> beta*V + db and extracting the linear-in-(da, db)
part yields a Lie element of multi-degree (4, 1) in (V, da or db).

For deg-(4, 1) of the free Lie algebra on 2 generators, dim = 1 by Witt,
basis = ad_V^4(d) = [V, [V, [V, [V, d]]]].

So the linear part has closed form:
    L = c_a(alpha, beta) * ad_V^4(da) + c_b(alpha, beta) * ad_V^4(db).

This script:
1. Defines the 30 5-letter words and coefficients of E_5 (from BCH/SymmetricQuintic.lean::symmetric_bch_quintic_poly).
2. Substitutes a -> alpha*V + da, b -> beta*V + db.
3. Extracts the linear-in-(da, db) part (sum of 30 * 5 = 150 sub-terms).
4. Groups by pattern V^i * d_letter * V^{4-i} for i in {0, 1, 2, 3, 4}.
5. Verifies the Lie-structure: pattern coefficients are in ratio (1, -4, 6, -4, 1).
6. Outputs c_a, c_b as polynomials in (alpha, beta).
"""

from collections import defaultdict
from fractions import Fraction
from itertools import product

# E_5 coefficients (numerator over 5760) and 5-letter words, from
# BCH/SymmetricQuintic.lean:74-105.
E5_TERMS = [
    (7,    "aaaab"),
    (-28,  "aaaba"),
    (-28,  "aaabb"),
    (42,   "aabaa"),
    (72,   "aabab"),
    (12,   "aabba"),
    (32,   "aabbb"),
    (-28,  "abaaa"),
    (-48,  "abaab"),
    (-48,  "ababa"),
    (-48,  "ababb"),
    (12,   "abbaa"),
    (-48,  "abbab"),
    (32,   "abbba"),
    (-8,   "abbbb"),
    (7,    "baaaa"),
    (32,   "baaab"),
    (-48,  "baaba"),
    (-48,  "baabb"),
    (72,   "babaa"),
    (192,  "babab"),
    (-48,  "babba"),
    (32,   "babbb"),
    (-28,  "bbaaa"),
    (-48,  "bbaab"),
    (-48,  "bbaba"),
    (-48,  "bbabb"),
    (32,   "bbbaa"),
    (32,   "bbbab"),
    (-8,   "bbbba"),
]
DENOM = 5760


def compute_linear_part():
    """For each (word, position) pair where w[i] is a letter ell in {a, b}:
    - At position i, the V-part is replaced by d_ell (delta_a or delta_b).
    - The other 4 positions contribute V with coefficient alpha (if 'a') or beta (if 'b').
    - The overall coefficient is k_w * (product of scalars).

    Return: dict mapping (i, ell, pattern_alphas, pattern_betas) -> Fraction coefficient.

    But we need the LIE structure of the result. Since the result is a Lie polynomial
    in (V, d_a, d_b) of degree (4, 1), it equals c_a * ad_V^4(da) + c_b * ad_V^4(db).

    Strategy: collect coefficients of the 5 patterns
        P_0 = V * V * V * V * d
        P_1 = V * V * V * d * V
        P_2 = V * V * d * V * V
        P_3 = V * d * V * V * V
        P_4 = d * V * V * V * V
    for each of d in {da, db}. For Lie polynomial, these must be in ratio (1, -4, 6, -4, 1) * c.

    Each pattern coefficient is a polynomial in (alpha, beta).
    """
    # For each delta-letter (a or b), collect P_0..P_4 coefficients as polys in (alpha, beta).
    # Polynomial representation: Counter mapping (alpha_exp, beta_exp) -> coefficient.
    # We need: linear_d['a'][i] for i in 0..4 is a dict.

    linear_d = {'a': [defaultdict(Fraction) for _ in range(5)],
                'b': [defaultdict(Fraction) for _ in range(5)]}

    for k_w, word in E5_TERMS:
        k_w = Fraction(k_w, DENOM)
        for i in range(5):  # position of the delta-letter
            ell = word[i]
            # The other 4 positions get V with coefficient alpha (if 'a') or beta (if 'b').
            # Count alphas and betas in positions != i:
            n_alpha = sum(1 for j in range(5) if j != i and word[j] == 'a')
            n_beta = sum(1 for j in range(5) if j != i and word[j] == 'b')
            assert n_alpha + n_beta == 4
            # Pattern index: i (the position where delta sits, in 0..4).
            # Pattern: V^i * delta * V^{4-i}.
            # Note: position i means delta is at index i in the 5-letter word, so to its left there are i V's and to its right 4-i V's.
            # So pattern P_i = V^i * delta * V^(4-i), where my P_0..P_4 indices were:
            #   P_0 = V^0 * delta * V^4 = delta * V^4
            #   P_1 = V^1 * delta * V^3
            #   ...
            #   P_4 = V^4 * delta = V^4 * delta * V^0
            # Wait, let me re-check. In my earlier code I wrote
            #   P_0 = V*V*V*V*d (i.e., 4 V's then d)
            #   P_4 = d*V*V*V*V (i.e., d then 4 V's)
            # Hmm, my reading was inconsistent. Let me set:
            # pattern index p_idx = i, meaning "delta is at slot i" in the 5-letter sequence.
            # So i=0 -> d * V * V * V * V (delta first); i=4 -> V * V * V * V * d (delta last).
            linear_d[ell][i][(n_alpha, n_beta)] += k_w

    return linear_d


def poly_str(poly):
    """Format a polynomial Counter as a readable string."""
    if not poly:
        return "0"
    terms = []
    for (a_exp, b_exp), c in sorted(poly.items()):
        if c == 0:
            continue
        s = ""
        if c == 1 and (a_exp + b_exp > 0):
            pass
        elif c == -1 and (a_exp + b_exp > 0):
            s = "-"
        else:
            s = f"({c})"
        if a_exp > 0:
            s += f" alpha^{a_exp}" if a_exp > 1 else " alpha"
        if b_exp > 0:
            s += f" beta^{b_exp}" if b_exp > 1 else " beta"
        terms.append(s.strip())
    return " + ".join(terms) if terms else "0"


def verify_lie_structure(linear_d):
    """Verify that the pattern coefficients are in ratio (1, -4, 6, -4, 1).

    ad_V^4(delta) = sum_{k=0}^{4} (-1)^k C(4,k) V^{4-k} * delta * V^k
                  = V^4 * delta - 4 V^3 * delta * V + 6 V^2 * delta * V^2 - 4 V * delta * V^3 + delta * V^4

    Pattern p_idx i:
    - i=0: delta at slot 0 -> delta * V^4. Coefficient in ad_V^4: 1
    - i=1: delta at slot 1 -> V * delta * V^3. Coefficient: -4
    - i=2: delta at slot 2 -> V^2 * delta * V^2. Coefficient: 6
    - i=3: delta at slot 3 -> V^3 * delta * V. Coefficient: -4
    - i=4: delta at slot 4 -> V^4 * delta. Coefficient: 1

    So if L = c * ad_V^4(delta), then L's pattern coefficients are c * (1, -4, 6, -4, 1).
    """
    expected_ratios = [1, -4, 6, -4, 1]

    for ell in ['a', 'b']:
        print(f"\n=== Linear-in-delta_{ell} pattern coefficients ===")
        for i, pattern in enumerate(linear_d[ell]):
            print(f"  P_{i} = V^{i} * d_{ell} * V^{4-i}: {dict(pattern)}")

        # Try to extract c from pattern P_0: c = poly equal to pattern[0] / 1 = pattern[0].
        c_poly = dict(linear_d[ell][0])
        # Verify pattern[1] / -4 = c, pattern[2] / 6 = c, ...
        print(f"\n  Inferred c_{ell}(alpha, beta) from P_0: {poly_str(c_poly)}")

        for i in range(1, 5):
            r = expected_ratios[i]
            pattern_i = linear_d[ell][i]
            # Should be c * r.
            for (a_exp, b_exp), c in c_poly.items():
                expected = c * r
                actual = pattern_i.get((a_exp, b_exp), Fraction(0))
                if actual != expected:
                    print(f"  MISMATCH at P_{i}, (alpha^{a_exp} beta^{b_exp}): expected {expected}, got {actual}")
            # And check no extra terms in pattern_i:
            for (a_exp, b_exp), c in pattern_i.items():
                if (a_exp, b_exp) not in c_poly:
                    print(f"  EXTRA at P_{i}, (alpha^{a_exp} beta^{b_exp}) = {c}")


def derive_strangblock_form():
    """Specialize at alpha = 4*p*tau, beta = (1-4p)*tau, gamma = 4*(p*tau)^3,
    delta = ((1-4p)*tau)^3. The closed form is:

      L = (1/5760) * P(alpha, beta) * (alpha * delta - beta * gamma) *
            ad_V^4(E_3)

    where P(alpha, beta) = 7*alpha^3 + 28*alpha^2*beta + 32*alpha*beta^2 + 8*beta^3.

    Substituting strangBlock scalars and simplifying with sympy.
    """
    try:
        from sympy import symbols, expand, simplify, factor, collect, Poly, Rational, S
    except ImportError:
        print("\n(sympy not available, skipping strangBlock simplification)")
        return

    p, tau = symbols('p tau', commutative=True)
    alpha = 4 * p * tau
    beta = (1 - 4 * p) * tau
    gamma = 4 * (p * tau) ** 3
    delta = ((1 - 4 * p) * tau) ** 3

    P = 7 * alpha**3 + 28 * alpha**2 * beta + 32 * alpha * beta**2 + 8 * beta**3
    K = alpha * delta - beta * gamma  # coefficient of ad_V^4(E_3) (because c_a = -beta*P, c_b = alpha*P, so the substitution gives (alpha*delta - beta*gamma)*P/5760 * ad_V^4(E_3))

    full = Rational(1, 5760) * P * K
    full_simplified = expand(full)
    full_factored = factor(full_simplified)

    print("\n" + "=" * 70)
    print("StrangBlock specialization (alpha=4pτ, beta=(1-4p)τ, γ=4(pτ)³, δ=((1-4p)τ)³)")
    print("=" * 70)
    print(f"\n  P(α, β) * (αδ - βγ) / 5760 = {full_simplified}")
    print(f"\n  Factored: {full_factored}")

    # Try to express as constant * p * (1-4p) * (1-2p) * (1-5p) * (1-3p) * (poly_2) * tau^7
    candidate = p * (1 - 4*p) * (1 - 2*p) * (1 - 5*p) * (1 - 3*p) * (12 * p**2 - 6 * p - 1) * tau**7
    ratio = expand(full / candidate)
    print(f"\n  Ratio  full / (p(1-4p)(1-2p)(1-5p)(1-3p)(12p²-6p-1)·τ⁷) = {ratio}")

    candidate_neg = -Rational(1, 180) * p * (1 - 4*p) * (1 - 2*p) * (1 - 5*p) * (1 - 3*p) * (12 * p**2 - 6 * p - 1) * tau**7
    diff = expand(full - candidate_neg)
    print(f"\n  Diff  full - (-(1/180)·p(1-4p)(1-2p)(1-5p)(1-3p)(12p²-6p-1)·τ⁷) = {diff}")


def main():
    linear_d = compute_linear_part()

    print("=" * 70)
    print("Verifying Lie structure of L-piece for E_5(αV+δa, βV+δb)")
    print("=" * 70)

    verify_lie_structure(linear_d)

    # Output the final c_a, c_b as multiplied by 5760 to clear denominators.
    print("\n" + "=" * 70)
    print("Final closed form (after factoring ad_V^4):")
    print("=" * 70)

    for ell in ['a', 'b']:
        c_poly = dict(linear_d[ell][0])
        print(f"\n  c_{ell}(alpha, beta) = {poly_str(c_poly)}")
        print(f"  c_{ell} * 5760 (cleared):")
        for (a_exp, b_exp), c in sorted(c_poly.items()):
            num = int(c * DENOM)
            print(f"    alpha^{a_exp} * beta^{b_exp}: {num} / {DENOM}  =  {c}")

    derive_strangblock_form()


if __name__ == "__main__":
    main()
