#!/usr/bin/env python3
"""
Compute the LinResidual polynomial:
  LinResidual := (C₅((a'+b)+V₂, a') - C₅(a'+b, a')) - ΔC₅_lin_explicit

with a' = a/2 and V₂ = (a'·b - b·a')/2 = (a·b - b·a)/4.

LinResidual should be a degree-7+ polynomial in (a, b) (degrees 7, 8, 9 from
V₂² , V₂³, V₂⁴ contributions).

Verify also that the deg-6 part of (C₅((a'+b)+V₂, a') - C₅(a'+b, a')) equals
ΔC₅_lin_explicit (i.e., the LinResidual has no deg-6 component).

Output:
- The 36 deg-6 coefficients (should match ΔC₅_lin_explicit).
- The deg-7+ residual coefficients (the QCuQ4 form).
"""
from sympy import symbols, Rational, expand, Symbol, Poly, simplify
from itertools import product

# Free non-commutative algebra over (a, b) using string keys.
# We represent polynomials as dicts: word_string -> coefficient.

def empty():
    return {}

def add_word(p, word, coef):
    if coef == 0:
        return
    if word in p:
        p[word] += coef
        if p[word] == 0:
            del p[word]
    else:
        p[word] = coef

def add(p1, p2):
    result = dict(p1)
    for w, c in p2.items():
        add_word(result, w, c)
    return result

def sub(p1, p2):
    result = dict(p1)
    for w, c in p2.items():
        add_word(result, w, -c)
    return result

def scalar_mul(p, c):
    if c == 0:
        return {}
    return {w: c * coef for w, coef in p.items()}

def mul(p1, p2):
    """Non-commutative product."""
    result = {}
    for w1, c1 in p1.items():
        for w2, c2 in p2.items():
            new_word = w1 + w2
            add_word(result, new_word, c1 * c2)
    return result

def power(p, n):
    if n == 0:
        return {'': Rational(1)}
    result = p
    for _ in range(n - 1):
        result = mul(result, p)
    return result

# Atoms: a, b
a = {'a': Rational(1)}
b = {'b': Rational(1)}

# a' = a/2
ap = scalar_mul(a, Rational(1, 2))

# V₂ = (a'·b - b·a') / 2 = (a·b - b·a) / 4
V2 = scalar_mul(sub(mul(ap, b), mul(b, ap)), Rational(1, 2))
# Verify: V2 = (1/4)(ab - ba)
V2_check = scalar_mul(sub(mul(a, b), mul(b, a)), Rational(1, 4))
assert V2 == V2_check, f"V2 mismatch: {V2} vs {V2_check}"
if __name__ == '__main__':
    print(f"V₂ = {V2}")

# x = a' + b
x = add(ap, b)
if __name__ == '__main__':
    print(f"x = a'+b = {x}")

# y = a'
y = ap

# bch_quintic_term has 30 distinct 5-letter words on {p, q} where p=first arg, q=second arg.
# Coefficients have common denominator 720.
# From bch_quintic_term definition: -bch_quintic_group_1 + 4·group_4 - 6·group_6 + 24·group_24, all / 720.

# Group 1: aaaab, abbbb, baaaa, bbbba (coef 1 each, but with - sign in bch_quintic_term)
# Group 4: aaaba, aaabb, aabbb, abaaa, abbba, baaab, babbb, bbaaa, bbbaa, bbbab (coef 1 each, with +4)
# Group 6: aabaa, aabab, aabba, abaab, ababb, abbaa, abbab, baaba, baabb, babaa, babba, bbaab, bbaba, bbabb (with -6)
# Group 24: ababa, babab (with +24)

# Each word w in {p, q}^5 has its "first-arg" letter. p=first arg, q=second.
# For bch_quintic_term(z₁, a'), we substitute p ← z₁, q ← a' (=y).

# bch_quintic_term coefficients (numerator, after / 720)
bqt_coefs = {
    # Group 1 (with -1 sign in bqt definition)
    'ppppq': -1, 'pqqqq': -1, 'qpppp': -1, 'qqqqp': -1,
    # Group 4 (with +4 sign)
    'pppqp': 4, 'pppqq': 4, 'ppqqq': 4, 'pqppp': 4, 'pqqqp': 4,
    'qpppq': 4, 'qpqqq': 4, 'qqppp': 4, 'qqqpp': 4, 'qqqpq': 4,
    # Group 6 (with -6 sign)
    'ppqpp': -6, 'ppqpq': -6, 'ppqqp': -6,
    'pqppq': -6, 'pqpqq': -6, 'pqqpp': -6, 'pqqpq': -6,
    'qppqp': -6, 'qppqq': -6, 'qpqpp': -6, 'qpqqp': -6,
    'qqppq': -6, 'qqpqp': -6, 'qqpqq': -6,
    # Group 24 (with +24 sign)
    'pqpqp': 24, 'qpqpq': 24,
}

def word_to_poly_at(word, p_poly, q_poly):
    """Convert a 5-letter word in {p, q} to a polynomial in (a, b)."""
    result = {'': Rational(1)}
    for letter in word:
        if letter == 'p':
            result = mul(result, p_poly)
        elif letter == 'q':
            result = mul(result, q_poly)
        else:
            raise ValueError(letter)
    return result

# Compute bch_quintic_term(z₁, a') where z₁ = (a'+b) + V₂.
z1 = add(x, V2)

C5_z1 = empty()
for word, num in bqt_coefs.items():
    poly = word_to_poly_at(word, z1, y)
    C5_z1 = add(C5_z1, scalar_mul(poly, Rational(num, 720)))

# Compute bch_quintic_term(a'+b, a').
C5_x = empty()
for word, num in bqt_coefs.items():
    poly = word_to_poly_at(word, x, y)
    C5_x = add(C5_x, scalar_mul(poly, Rational(num, 720)))

# Diff
diff = sub(C5_z1, C5_x)

if __name__ == '__main__':
    print(f"\nC5_z1 - C5_x has {len(diff)} non-zero monomials.")

# ΔC₅_lin_explicit (from the axiom statement, denom 46080)
DeltaC5_coefs = {
    'aaaabb': Rational(-14, 46080),
    'aaabab': Rational(46, 46080),
    'aaabba': Rational(10, 46080),
    'aaabbb': Rational(28, 46080),
    'aababb': Rational(-54, 46080),
    'aabaab': None,  # placeholder, careful: order in axiom is aabab, not aabba
}

# Actually let me re-read the axiom carefully - the words are 6-letter:
DeltaC5 = {}
DeltaC5_data = """
  -14 a a a a b b
   46 a a a b a b
   10 a a a b b a
   28 a a a b b b
  -54 a a b a a b
  -30 a a b a b a
  -52 a a b a b b
  -12 a a b b a b
  -20 a a b b b a
   -8 a a b b b b
   36 a b a a a b
  -32 a b a a b b
   30 a b a b a a
  128 a b a b a b
   40 a b a b b a
   32 a b a b b b
  -10 a b b a a a
  -32 a b b a a b
  -40 a b b a b a
  -48 a b b a b b
   20 a b b b a a
   32 a b b b a b
  -36 b a a a b a
   54 b a a b a a
   32 b a a b b a
  -46 b a b a a a
 -128 b a b a b a
   12 b a b b a a
  -32 b a b b b a
   14 b b a a a a
   32 b b a a b a
   52 b b a b a a
   48 b b a b b a
  -28 b b b a a a
  -32 b b b a b a
    8 b b b b a a
"""
for line in DeltaC5_data.strip().split('\n'):
    parts = line.split()
    num = int(parts[0])
    word = ''.join(parts[1:])
    DeltaC5[word] = Rational(num, 46080)

if __name__ == '__main__':
    print(f"\nΔC₅_lin_explicit has {len(DeltaC5)} monomials, total |coef|={sum(abs(c) for c in DeltaC5.values())}")

# LinResidual = diff - DeltaC5
LinResidual = sub(diff, DeltaC5)

# Filter by degree (length of word).
by_degree = {}
for word, coef in LinResidual.items():
    deg = len(word)
    by_degree.setdefault(deg, []).append((word, coef))

if __name__ == '__main__':
    print(f"\nLinResidual has {len(LinResidual)} non-zero monomials.")

    for deg in sorted(by_degree.keys()):
        terms = by_degree[deg]
        print(f"\nDegree {deg}: {len(terms)} terms")
        if deg == 6:
            # Should be empty (cancellation should occur).
            print(f"  Total |coef|={sum(abs(c) for _, c in terms)}")
            if terms:
                print("  WARNING: deg-6 should cancel but didn't!")
                for w, c in terms[:5]:
                    print(f"    {w}: {c}")
        else:
            total = sum(abs(c) for _, c in terms)
            print(f"  Total |coef|={total}")

    # Output the non-zero deg-7+ terms (this is what we need for Lean).
    print("\n=== Deg-7+ residual (LinResidual after deg-6 cancellation) ===")
    for deg in sorted(by_degree.keys()):
        if deg < 7:
            continue
        terms = by_degree[deg]
        if not terms:
            continue
        print(f"\n# Degree {deg} ({len(terms)} terms):")
        # Find common denominator
        from math import gcd
        from functools import reduce
        denoms = [c.q for _, c in terms]
        common_denom = reduce(lambda a, b: a * b // gcd(a, b), denoms, 1)
        print(f"  Common denominator: {common_denom}")
        for w, c in sorted(terms):
            num = c * common_denom
            print(f"  ({num} / {common_denom}) * {' * '.join(w)}")
