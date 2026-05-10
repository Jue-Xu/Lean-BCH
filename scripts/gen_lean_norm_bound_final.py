#!/usr/bin/env python3
"""
Generate the Lean proof body for `norm_C5_LinResidual_polynomial_le`.

Uses:
- 205 per-term smul norm bounds (each ~5-10 lines).
- A `set` chain of intermediate sums (205 lines).
- 204 triangle inequality applications.
- Final linarith.

Output: 3 chunks of Lean code: term bounds, sum chain, final linarith.
"""
import sys
sys.path.insert(0, '/Users/jue/Documents/Claude/Projects/Lean-BCH/scripts')
from compute_C5_diff_LinResidual import LinResidual

DENOMS_BY_DEG = {7: 92160, 8: 184320, 9: 368640}

terms_in_order = []
for deg in [7, 8, 9]:
    denom = DENOMS_BY_DEG[deg]
    deg_terms = [(w, c) for w, c in LinResidual.items() if len(w) == deg]
    deg_terms.sort()
    for word, coef in deg_terms:
        num = coef * denom
        if num == 0:
            continue
        terms_in_order.append((word, int(num), denom, deg))

n = len(terms_in_order)

def word_to_lean(word):
    return ' * '.join(word)

def term_lean(num, denom, word):
    return f"({num} / {denom} : 𝕂) • ({word_to_lean(word)})"

# Generate per-term bound proofs.
# For each term, prove: ‖(num/denom : 𝕂) • word‖ ≤ |num|/denom * s^7 (with s ≤ 1, d_word ≥ 7).

# To bound ‖word‖ ≤ s^d:
# Use a chain of `norm_mul_le` + bounds on `‖a‖, ‖b‖`.

# The chain for a d-letter word: d-1 applications of `norm_mul_le`.
# After expansion: ‖letter_1‖ * ‖letter_2‖ * ... * ‖letter_d‖.
# Each ‖letter‖ ≤ s, so product ≤ s^d.

# To bound coefficient norm:
# ‖(num/denom : 𝕂)‖ = |num|/denom.
# Achieved via `RCLike.norm_ofNat` for naturals and `norm_neg` for negatives.

# Generate the proof for each term.

def generate_per_term(idx, word, num, denom, deg):
    """Generate the Lean proof body for a single term bound."""
    abs_num = abs(num)
    word_str = word_to_lean(word)
    term_expr = term_lean(num, denom, word)

    lines = []
    lines.append(f"  -- Term {idx}: word = {word}, deg = {deg}")

    # First, generate the per-word norm bound.
    # ‖letter1 * letter2 * ... * letter_d‖ ≤ s^d.
    # Build the chain: at each step, factor off the rightmost letter.
    # Word has d letters. We build: ((... ((l1 * l2) * l3) ...) * l_d).

    # The chain is:
    # ‖l1 * ... * l_d‖
    #   ≤ ‖l1 * ... * l_{d-1}‖ * ‖l_d‖   (norm_mul_le, peel off l_d)
    #   ≤ (...) ≤ ... ≤ ‖l1‖ * ‖l2‖ * ... * ‖l_d‖
    #   ≤ s * s * ... * s
    #   = s^d

    # Print the chain.
    lines.append(f"  have hword{idx} : ‖{word_str}‖ ≤ s ^ {deg} := by")

    # Chain of norm_mul_le calls. Building the chain:
    # For a word "abcdefg" of length 7:
    # ‖abcdefg‖ = ‖abcdef * g‖ ≤ ‖abcdef‖ * ‖g‖
    #           ≤ (‖abcde‖ * ‖f‖) * ‖g‖
    #           ≤ ((‖abcd‖ * ‖e‖) * ‖f‖) * ‖g‖
    #           ≤ (((‖abc‖ * ‖d‖) * ‖e‖) * ‖f‖) * ‖g‖
    #           ≤ ((((‖ab‖ * ‖c‖) * ‖d‖) * ‖e‖) * ‖f‖) * ‖g‖
    #           ≤ (((((‖a‖ * ‖b‖) * ‖c‖) * ‖d‖) * ‖e‖) * ‖f‖) * ‖g‖
    #           ≤ s * s * s * s * s * s * s
    #           = s^7

    # But the actual structure is left-associated by default:
    # a * b * c * d * e * f * g = ((((((a * b) * c) * d) * e) * f) * g
    # ‖((((((a * b) * c) * d) * e) * f) * g)‖
    #   ≤ ‖((((((a * b) * c) * d) * e) * f)‖ * ‖g‖    (norm_mul_le)
    #   ≤ (‖((((((a * b) * c) * d) * e)‖ * ‖f‖) * ‖g‖    (gcongr + norm_mul_le)
    #   ≤ ...

    # Build the calc:
    # First step: full word product.

    # Generate steps:
    #   ‖word‖ = ‖prefix * last_letter‖ ≤ ‖prefix‖ * ‖last_letter‖.

    # For brevity, let's use `calc` with explicit terms.
    # But that's 7-1 = 6 lines for a 7-letter word. With 205 terms, that's 1230+ lines.

    # Alternative: use a single tactic combining `norm_mul_le` chain + ha/hb.
    # Let's try `gcongr` with `norm_mul_le` lemma:

    # Actually, the cleanest: use a single calc with explicit chain.

    # Build the calc for the word.
    # Words are like "aaababa", processed left-to-right.
    # left-associated product: ((((((a * a) * a) * b) * a) * b) * a)

    # Compute the chain step by step.
    letters = list(word)
    d = len(letters)

    # Generate the calc steps.
    # Step 0: starting from `‖a*b*...‖`.
    # Step k: peel off the rightmost letter (k=1 to d-1).

    # The accumulator builds up the LHS at each step.
    # accumulator after step 0: ‖product of all d letters‖
    # accumulator after step 1: ‖prefix of d-1‖ * ‖last‖
    # ...

    # Easier: just write out all d-1 norm_mul_le steps.

    # Build the prefix expressions.
    # word = "aabab", d=5
    # after step 1: ‖a*a*b*a‖ * ‖b‖ ≤ s^5
    # after step 2: ‖a*a*b‖ * ‖a‖ * ‖b‖ ≤ s^5
    # ...
    # final: ‖a‖ * ‖a‖ * ‖b‖ * ‖a‖ * ‖b‖ ≤ s^5 ≤ s * s * s * s * s = s^5

    # In Lean code:
    # calc ‖a*a*b*a*b‖
    #   ≤ ‖a*a*b*a‖ * ‖b‖ := norm_mul_le _ _
    #   _ ≤ (‖a*a*b‖ * ‖a‖) * ‖b‖ := by gcongr; exact norm_mul_le _ _
    #   _ ≤ ((‖a*a‖ * ‖b‖) * ‖a‖) * ‖b‖ := by gcongr; exact norm_mul_le _ _
    #   _ ≤ (((‖a‖ * ‖a‖) * ‖b‖) * ‖a‖) * ‖b‖ := by gcongr; exact norm_mul_le _ _
    #   _ ≤ (((s * s) * s) * s) * s := by gcongr <;> first | exact ha | exact hb
    #   _ = s^5 := by ring

    # Generate the calc steps:
    # First line: "calc ‖<all letters>‖"
    full_word = ' * '.join(letters)
    lines.append(f"    calc ‖{full_word}‖")

    # d-1 norm_mul_le steps
    # Build prefix (of length d-1) at first step
    for k in range(1, d):
        # At step k, peel the (d-k+1)th letter from the right.
        # After k steps, the LHS becomes nested.

        prefix = ' * '.join(letters[:d-k])
        peeled = letters[d-k]

        # Need to build the expression with k pairs of parens.
        # Step 1: ‖prefix * peeled‖ ≤ ‖prefix‖ * ‖peeled‖
        # Step 2: ‖smaller_prefix * letter‖ ≤ ‖smaller_prefix‖ * ‖letter‖
        # We build the LHS recursively.

        # Build the RHS: at step k, we have norms of (d-k) things multiplied.
        # Each ‖letter‖ + outer norm.

        if k == 1:
            # First step: split into prefix and peeled.
            prefix_norm = f"‖{prefix}‖"
            rhs = f"{prefix_norm} * ‖{peeled}‖"
            lines.append(f"      ≤ {rhs} := norm_mul_le _ _")
        else:
            # Step k: split prefix into (prefix-1) * peeled.
            new_prefix = ' * '.join(letters[:d-k])
            # Build the LHS-side expression at this step.
            # After step k-1, RHS is `‖smaller_prefix‖ * ‖peeled_{k-1}‖ * ‖peeled_{k-2}‖ * ...`.
            # At step k: we replace ‖smaller_prefix‖ with `‖next_prefix‖ * ‖next_peeled‖`.

            # Build the RHS expression as a left-associated product:
            # After step k: `((((‖prefix_at_step_k‖ * ‖peeled_k‖) * ‖peeled_{k-1}‖) ...) * ‖peeled_1‖)`
            # peeled letters in reverse order from end of word.

            peeled_norms = [f"‖{letters[d-i]}‖" for i in range(1, k+1)]  # in order: peeled_1, peeled_2, ..., peeled_k
            # Wait, peeled_1 is the last letter, peeled_2 is letters[d-2], etc.
            # In reverse: peeled_k = letters[d-k]

            # Actually our chain is:
            # step 1: peel letters[d-1] -> ‖letters[0..d-1]‖ * ‖letters[d-1]‖
            # step 2: peel letters[d-2] from prefix -> (‖letters[0..d-2]‖ * ‖letters[d-2]‖) * ‖letters[d-1]‖
            # ...
            # step k: ((((‖letters[0..d-k]‖ * ‖letters[d-k]‖) * ‖letters[d-k+1]‖) * ...) * ‖letters[d-1]‖)

            # Build this RHS:
            inner_prefix_norm = f"‖{new_prefix}‖"

            # Build the full RHS expression with parentheses.
            # Outer-most: ‖prefix‖ * ‖peeled_k‖
            # But wait, at step k, the RHS should be:
            # (‖letters[0..d-k]‖ * ‖letters[d-k]‖) inside, then * ‖letters[d-k+1]‖, etc.

            # Let me just build it as a list of `‖letter‖` strings, one per peeled letter.
            # The first one is the prefix norm.
            # Then concatenate with " * " between them.

            # We have k peeled letters: indices [d-k, d-k+1, ..., d-1]
            # Plus the prefix `letters[0..d-k]`.

            # The structure (after step k):
            # ‖letters[0..d-k]‖ * ‖letters[d-k]‖   ←— this is at step k=1's RHS
            # ((‖letters[0..d-k-1]‖ * ‖letters[d-k-1]‖) * ‖letters[d-k]‖)   ←— at step k=2's RHS
            # etc.

            # Actually we want this format (parens to group):
            # ((... * ‖letters[d-2]‖) * ‖letters[d-1]‖)

            # Let's build it bottom-up.

            # Components: prefix_norm, then peeled_letters in order.
            # Build the full expression with explicit parens.

            new_rhs_inner = inner_prefix_norm + " * " + f"‖{letters[d-k]}‖"
            new_rhs_inner_paren = f"({new_rhs_inner})"

            # Now multiply by the previously-peeled letters (in reverse).
            for i in range(k-1, 0, -1):
                next_letter = letters[d-i]
                new_rhs_inner_paren = f"({new_rhs_inner_paren} * ‖{next_letter}‖)"
            # remove outermost paren
            if new_rhs_inner_paren.startswith("(") and new_rhs_inner_paren.endswith(")"):
                rhs = new_rhs_inner_paren[1:-1]
            else:
                rhs = new_rhs_inner_paren

            lines.append(f"      _ ≤ {rhs} := by gcongr; exact norm_mul_le _ _")

    # Final step: bound each ‖letter‖ by s.
    # After d-1 steps, RHS is ‖letter1‖ * ‖letter2‖ * ... * ‖letter_d‖.
    # Each ‖letter‖ ≤ s.

    # Build the RHS at the next step: replace each ‖letter‖ with s.
    # The RHS is left-associated: ((... ((‖l1‖ * ‖l2‖) * ‖l3‖) ...) * ‖l_d‖).

    # After all d-1 norm_mul_le, RHS is left-assoc product of d ‖letter_i‖'s.
    # Replace each with s: left-assoc product of d s's.
    # = s^d

    # The all-letters norm expression:
    all_letter_norms = " * ".join(f"‖{l}‖" for l in letters)

    # The all-s expression:
    all_s = " * ".join("s" for _ in letters)

    lines.append(f"      _ ≤ {all_s} := by gcongr <;> first | exact ha | exact hb")
    lines.append(f"      _ = s ^ {deg} := by ring")

    # Now generate the per-term smul bound.
    lines.append(f"  have hcoef{idx} : ‖({num} / {denom} : 𝕂)‖ ≤ {abs_num} / {denom} := by")
    if num >= 0:
        lines.append(f"    rw [show (({num} : 𝕂) / {denom}) = ((↑{abs_num} : 𝕂) / ↑{denom}) from by norm_cast]")
    else:
        lines.append(f"    rw [show (({num} : 𝕂) / {denom}) = -((↑{abs_num} : 𝕂) / ↑{denom}) from by push_cast; ring]")
        lines.append(f"    rw [norm_neg]")
    lines.append(f"    rw [norm_div, RCLike.norm_natCast, RCLike.norm_natCast]")

    lines.append(f"  have hT{idx} : ‖{term_expr}‖ ≤ ({abs_num} / {denom}) * s ^ {deg} := by")
    lines.append(f"    calc ‖{term_expr}‖")
    lines.append(f"        ≤ ‖({num} / {denom} : 𝕂)‖ * ‖{word_str}‖ := norm_smul_le _ _")
    lines.append(f"      _ ≤ ({abs_num} / {denom}) * (s ^ {deg}) := mul_le_mul hcoef{idx} hword{idx} (norm_nonneg _) (by positivity)")

    return '\n'.join(lines)

# Output the full proof
# Approach:
#  1. `set tt_i := <term_i>` for i=1..n.
#  2. Per-term bound: `have hT_i : ‖tt_i‖ ≤ K_i * s^7`. (~10 lines each)
#  3. n-1 triangle bounds: `have htri_i : ‖tt_1 + ... + tt_i‖ ≤ ‖tt_1 + ... + tt_{i-1}‖ + ‖tt_i‖`.
#  4. Final linarith with all hypotheses.

# Generate the term `set` declarations.
print("  -- Step 1: name each term via `set`.")
for i, (word, num, denom, deg) in enumerate(terms_in_order):
    expr = term_lean(num, denom, word)
    print(f"  set tt{i+1} : 𝔸 := {expr} with htt{i+1}_def")

# Generate per-term bounds (each ~10 lines).
print()
print("  -- Step 2: per-term smul norm bounds (each via norm_smul_le + word norm bound).")
for idx, (word, num, denom, deg) in enumerate(terms_in_order):
    print(generate_per_term(idx + 1, word, num, denom, deg))

# Generate the n-1 triangle inequality bounds.
print()
print("  -- Step 3: n-1 triangle inequality bounds.")
prev_expr = "tt1"
for i in range(1, n):
    new_expr = f"({prev_expr}) + tt{i+1}"
    print(f"  have htri{i+1} : ‖{new_expr}‖ ≤ ‖{prev_expr}‖ + ‖tt{i+1}‖ := norm_add_le _ _")
    prev_expr = new_expr

# Final linarith with all hypotheses.
print()
print(f"  -- Step 4: final linarith.")
print(f"  unfold C5_LinResidual_polynomial")

# Build the goal expression: ‖prev_expr‖ ≤ 1 * s^7.
# This is the cumulative sum which equals C5_LinResidual_polynomial.
# We need linarith to combine all per-term bounds (hT_i) + all triangle bounds (htri_i)
# to derive: ‖final_expr‖ ≤ K_total · s^7.

# Build a comprehensive linarith hint list.
hints = []
hints.append("hs7_nn")
for i in range(1, n+1):
    hints.append(f"hT{i}")
for i in range(2, n+1):
    hints.append(f"htri{i}")
hints_str = ", ".join(hints)

print(f"  show ‖tt1{''.join(' + tt' + str(i+1) for i in range(1, n))}‖ ≤ s ^ 7")
print(f"  linarith [{hints_str}]")
