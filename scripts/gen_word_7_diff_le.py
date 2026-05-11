#!/usr/bin/env python3
"""Generate `word_7_diff_le` (7-letter product Lipschitz) as the deg-7
analog of `word_5_diff_le` in BCH/SymmetricQuintic.lean.
"""

n = 7  # word length

# Unicode subscripts (₁..₇)
SUBS = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉']

def sub(i):
    """Return Unicode subscript for digit i."""
    return SUBS[i]

def gen():
    lines = []
    lines.append(f"-- **{n}-letter product Lipschitz**: `‖x₁x₂x₃x₄x₅x₆x₇ − y₁y₂y₃y₄y₅y₆y₇‖ ≤ N⁶·Σᵢ ‖xᵢ−yᵢ‖`")
    lines.append(f"-- when `‖xᵢ‖, ‖yᵢ‖ ≤ N`. Telescoping identity + triangle inequality.")
    lines.append(f"set_option maxHeartbeats 1600000 in")
    lines.append(f"private lemma word_7_diff_le (x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : 𝔸) (N : ℝ)")
    # Build hyps
    hyps_x = ' '.join(f"(hx{sub(i)} : ‖x{sub(i)}‖ ≤ N)" for i in range(1, n+1))
    hyps_y = ' '.join(f"(hy{sub(i)} : ‖y{sub(i)}‖ ≤ N)" for i in range(1, n+1))
    lines.append(f"    {hyps_x}")
    lines.append(f"    {hyps_y}")
    lines.append(f"    (hN_nn : 0 ≤ N) :")
    # Body
    x_prod = ' * '.join(f"x{sub(i)}" for i in range(1, n+1))
    y_prod = ' * '.join(f"y{sub(i)}" for i in range(1, n+1))
    diff_sum = ' + '.join(f"‖x{sub(i)} - y{sub(i)}‖" for i in range(1, n+1))
    lines.append(f"    ‖{x_prod} - {y_prod}‖ ≤")
    lines.append(f"      N ^ {n-1} * ({diff_sum}) := by")
    # Proof: telescoping identity.
    lines.append(f"  -- Telescoping identity.")
    lines.append(f"  have hid : {x_prod} - {y_prod} =")
    tele_terms = []
    for i in range(1, n+1):
        parts = []
        for j in range(1, n+1):
            if j < i:
                parts.append(f"y{sub(j)}")
            elif j == i:
                parts.append(f"(x{sub(j)} - y{sub(j)})")
            else:
                parts.append(f"x{sub(j)}")
        tele_terms.append(' * '.join(parts))
    lines.append("      " + " +\n      ".join(tele_terms) + " := by noncomm_ring")
    lines.append(f"  rw [hid]")
    lines.append(f"  have hN_pow_nn : (0 : ℝ) ≤ N ^ {n-1} := pow_nonneg hN_nn {n-1}")
    for i in range(1, n+1):
        lines.append(f"  have hd{sub(i)}_nn : 0 ≤ ‖x{sub(i)} - y{sub(i)}‖ := norm_nonneg _")

    # Per-term bound.
    for i in range(1, n+1):
        # Bound term i: y₁..yᵢ₋₁ · (xᵢ-yᵢ) · xᵢ₊₁..xₙ.
        term_expr = tele_terms[i-1]
        # Decomposed by triangle: bound first/last separately.
        # Build a nested calc.
        # Actually, just write the calc explicitly.
        # ‖term_expr‖ ≤ ‖y₁‖·...·‖yᵢ₋₁‖·‖xᵢ-yᵢ‖·‖xᵢ₊₁‖·...·‖xₙ‖
        # ≤ N^(i-1)·‖xᵢ-yᵢ‖·N^(n-i) = N^(n-1)·‖xᵢ-yᵢ‖
        norm_parts = []
        for j in range(1, n+1):
            if j < i:
                norm_parts.append(f"‖y{sub(j)}‖")
            elif j == i:
                norm_parts.append(f"‖x{sub(j)} - y{sub(j)}‖")
            else:
                norm_parts.append(f"‖x{sub(j)}‖")
        norm_bound = ' * '.join(norm_parts)
        N_parts = []
        for j in range(1, n+1):
            if j == i:
                N_parts.append(f"‖x{sub(j)} - y{sub(j)}‖")
            else:
                N_parts.append("N")
        N_bound = ' * '.join(N_parts)
        lines.append(f"  have ht{sub(i)} : ‖{term_expr}‖ ≤ N ^ {n-1} * ‖x{sub(i)} - y{sub(i)}‖ := by")
        lines.append(f"    calc ‖{term_expr}‖")
        lines.append(f"        ≤ {norm_bound} := by")
        # Step-down via norm_mul_le chain.
        # Build the inner calc.
        # For term y₁·y₂·...·(xᵢ-yᵢ)·xᵢ₊₁·...·xₙ, we step down from norm of the whole product to product of norms.
        # The product associates left: (((y₁·y₂)·...)·...)·xₙ. norm_mul_le steps strip the last factor each time.
        # We need n-1 steps.
        # Each step: ‖A·B‖ ≤ ‖A‖·‖B‖.
        # Inner calc chain:
        # First step: norm_mul_le _ _ on the full product.
        # We need to produce a series of `gcongr; exact norm_mul_le _ _` steps.
        # Generate the chain from inner-most outward.
        # Actually the existing pattern stratifies: build the nested expression first, then apply norm_mul_le from the outermost.
        # ‖A * B * C * D * E * F * G‖
        #   ≤ ‖A * B * C * D * E * F‖ * ‖G‖ := norm_mul_le _ _
        #   _ ≤ ‖A * B * C * D * E‖ * ‖F‖ * ‖G‖ := by gcongr; exact norm_mul_le _ _
        #   ...
        # Need n-1 = 6 calc steps.
        # Build expressions: full term reduces from rightmost.
        # Build the substituted form for each level (strip last factor).
        # Get the factor list (n=7 factors).
        factor_list = []
        for j in range(1, n+1):
            if j < i:
                factor_list.append(f"y{sub(j)}")
            elif j == i:
                factor_list.append(f"(x{sub(j)} - y{sub(j)})")
            else:
                factor_list.append(f"x{sub(j)}")
        # Generate the inner calc:
        # Level 0 (start): ‖factor_list[0] * factor_list[1] * ... * factor_list[n-1]‖
        # Level k: ‖factor_list[0] * ... * factor_list[n-1-k-1]‖ * ‖factor_list[n-1-k]‖ * ... * ‖factor_list[n-1]‖
        # Wait, this needs careful indexing. Let me just generate it.
        # For each step, strip the LAST mul:
        # ‖A1*A2*...*An‖ ≤ ‖A1*A2*...*A(n-1)‖ * ‖An‖
        # Substituting back, this becomes a chain.
        # First write the first step:
        # ≤ ‖A1*A2*...*A(n-1)‖ * ‖An‖ := norm_mul_le _ _
        # Then we need to apply norm_mul_le to the n-1-letter product.
        # _ ≤ ‖A1*A2*...*A(n-2)‖ * ‖A(n-1)‖ * ‖An‖ := by gcongr; exact norm_mul_le _ _
        # ...
        # _ ≤ ‖A1‖ * ‖A2‖ * ... * ‖An‖ := by gcongr; exact norm_mul_le _ _
        #
        # That's 6 steps for n=7.
        calc_lines = []
        for k in range(n-1):
            # At step k, the LHS has (n-k) factors as norms on the left, and (k) factors as norms on the right.
            # Each factor strip: take the first (n-k) factors, strip last to bring it out.
            left_factors_count = n - k - 1  # number of factors in the product norm
            # First level uses norm_mul_le _ _, others use gcongr + norm_mul_le.
            left_block_factors = factor_list[:left_factors_count + 1]  # all but the stripped
            inside_mul = ' * '.join(left_block_factors[:-1])
            stripped_factor = left_block_factors[-1]
            # The RHS expression at this step: ‖A1*...*A(left_factors_count)‖ * ‖A(left_factors_count+1)‖ * ... * ‖An‖
            rhs_parts = ['‖' + ' * '.join(left_block_factors[:-1]) + '‖']
            for j in range(left_factors_count, n):
                rhs_parts.append('‖' + factor_list[j] + '‖')
            rhs_expr = ' * '.join(rhs_parts)
            if k == 0:
                calc_lines.append(f"          calc _ ≤ {rhs_expr} := norm_mul_le _ _")
            else:
                calc_lines.append(f"            _ ≤ {rhs_expr} := by")
                calc_lines.append(f"                gcongr; exact norm_mul_le _ _")
        lines.extend(calc_lines)
        # Final bound using N: each ‖xᵢ‖ or ‖yⱼ‖ ≤ N.
        N_str = ' * '.join(N_parts)
        lines.append(f"      _ ≤ {N_str} := by gcongr")
        lines.append(f"      _ = N ^ {n-1} * ‖x{sub(i)} - y{sub(i)}‖ := by ring")

    # Sum the n bounds.
    lines.append(f"  -- Sum the {n} bounds.")
    # The total sum of the {n} bounds is N^(n-1) · (Σᵢ ‖xᵢ-yᵢ‖).
    sum_expr = ' +\n        '.join(tele_terms)
    lines.append(f"  calc ‖{sum_expr}‖")
    # Triangle inequality through the sum.
    # For n=7, we have 6 norm_add_le steps + 7 bound terms.
    # Use linarith at the end.
    norms_sum_parts = ' + '.join(f"‖{t}‖" for t in tele_terms)
    lines.append(f"      ≤ {norms_sum_parts} := by")
    # Add the chain of norm_add_le via have's, then close with linarith.
    # Each successive: ‖a + b‖ ≤ ‖a‖ + ‖b‖.
    # Generate (n-1) norm_add_le applications.
    for k in range(n-1):
        # At step k, we have a sum of (n-k) terms. We strip the last one.
        # Sum is: tele_terms[0] + tele_terms[1] + ... + tele_terms[n-k-1]
        # = (tele_terms[0] + ... + tele_terms[n-k-2]) + tele_terms[n-k-1]
        left_sum = " + ".join(tele_terms[:n-k-1])
        right_term = tele_terms[n-k-1]
        lines.append(f"        have := norm_add_le")
        lines.append(f"              ({left_sum})")
        lines.append(f"              ({right_term})")
    lines.append("        linarith")
    bounds_sum = " + ".join(f"N ^ {n-1} * ‖x{sub(i)} - y{sub(i)}‖" for i in range(1, n+1))
    lines.append(f"    _ ≤ {bounds_sum} := by")
    bound_ids = ', '.join(f'ht{sub(i)}' for i in range(1, n+1))
    lines.append(f"        linarith [{bound_ids}]")
    lines.append(f"    _ = N ^ {n-1} * ({diff_sum}) := by ring")
    return '\n'.join(lines)


print(gen())
