# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected`: μ = √(2+√2)

Located in: `RequestProject/SAWPaperChain.lean`

## Proof Chain Summary

The corrected proof chain uses **diagonal bridges** (PaperBridge, matching the paper's convention) rather than x-coordinate bridges (which give FALSE bounds).

### Fully Proved (no sorry)

1. **Core definitions** (SAW.lean): hexGraph, SAW, saw_count, connective_constant, xc, λ, j
2. **Algebraic identities** (SAW.lean): pair_cancellation, triplet_cancellation
3. **Finiteness** (SAW.lean): SAW is Fintype for each n, saw_count_pos
4. **Submultiplicativity** (SAWSubmult.lean): c_{n+m} ≤ c_n · c_m
5. **Fekete's lemma** (SAWMain.lean): connective_constant_is_limit', connective_constant_pos'
6. **Bridge decay** (SAWPaperChain.lean): paper_bridge_partition T x ≤ (x/xc)^T / xc
   - Uses partial sum bounds directly (NO circular dependency on hammersley_welsh_injection)
7. **HW summability** (SAWPaperChain.lean): hw_summable_corrected
   - Proved from paper_bridge_decomp_injection + paper_bridge_decay
   - No circular dependency
8. **Abstract infrastructure**: bridge_bound_of_strip_identity, bridge_lower_bound,
   prod_one_add_geometric_converges, strip_identity_limit, monotone_bounded_converges
9. **Embedding & directions**: correctHexEmbed, hex directions, interior_cancellation
10. **Boundary positivity**: boundary_cos_pos
11. **Paper bridge infrastructure**: paper_bridge_length_ge, paperBridge_toSAW_sigma_injective,
    paper_bridge_partial_sum_le, paper_bridge_upper_bound

### Remaining Sorry's (3 on critical path)

1. **`B_paper_le_one_direct`** (SAWStripIdentityCorrect.lean)
   - The fundamental gap: B_paper(T, L, xc) ≤ 1
   - Requires: parafermionic observable vertex relation → discrete Stokes → boundary evaluation
   - All algebraic ingredients proved (pair/triplet cancellation, boundary_cos_pos)
   - Missing: combinatorial grouping of walks into pairs/triplets at each vertex

2. **`paper_bridge_lower_bound`** (SAWPaperChain.lean)
   - ∃ c > 0, paper_bridge_partition T xc ≥ c/T
   - Depends on B_paper_le_one_direct
   - Abstract quadratic recurrence infrastructure exists (bridge_lower_bound in SAW.lean)
   - Needs: connecting the strip identity to the infinite-strip limit + quadratic recurrence

3. **`paper_bridge_decomp_injection`** (SAWPaperChain.lean)
   - ∑ c_n x^n ≤ 2·(∑_S ∏ B_{T+1})²
   - Independent of B_paper_le_one_direct
   - Requires: formalizing the full Hammersley-Welsh bridge decomposition algorithm
   - The algorithm: for half-plane walks, induction on width; for general walks, split at min diagonal

### Superseded / False Theorems

- `origin_bridge_upper_bound` (SAWBridgeFix.lean): **FALSE** for x-coordinate bridges
- `origin_bridge_lower_bound`, `Z_xc_diverges`, `hammersley_welsh_injection` (SAWBridgeFix.lean): superseded by corrected chain
- `bridge_decomposition_injection_proof` (SAWHWDecomp.lean): superseded by paper_bridge_decomp_injection
- `bridge_decomp_injection_from_algorithm` (SAWHWAlgorithm.lean): superseded
