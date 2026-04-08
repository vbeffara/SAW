# Summary of changes
## Summary of changes

### Progress on the critical path

The main theorem `connective_constant_eq` (μ = √(2+√2)) in `SAWFinal.lean` now depends on **3 sorry's** (previously 4+ on the critical path):

1. `B_paper_le_one_direct` — Lemma 2 of the paper (parafermionic observable argument)
2. `paper_bridge_lower_bound` — bridge lower bound c/T (depends on #1)
3. `paper_bridge_decomp_injection` — Hammersley-Welsh bridge decomposition (independent of #1)

### New proofs (this session)

1. **`paper_bridge_finite_sum_le`** (SAWPaperChain.lean): For any finite set of bridges across all widths, the total weight is bounded by Z(xc). Uses the injection from bridges to SAWs (bridges of different widths have different endpoints, hence are different SAWs).

2. **`paper_bridge_summable`** (SAWPaperChain.lean): Each individual bridge partition function is summable (partial sums bounded by 1/xc via the paper bridge upper bound).

3. **`paper_bridge_sum_le_Z`** (SAWPaperChain.lean): The sum of bridge partition functions over T < N is bounded by Z(xc). Uses ε-approximation of summable tsums combined with `paper_bridge_finite_sum_le`. This was previously `sorry` (via a failing `grind +suggestions` that caused timeouts).

4. **`boundary_weight_re_nonneg`** (SAWObservableProof2.lean): For every hex edge (v,w), the real part of the boundary weight `dir(v,w) · exp(-iσθ(v,w))` is non-negative. Proved by case-splitting on all 6 edge types of the hexagonal lattice. This is the key geometric ingredient needed for B_paper ≤ 1.

5. **`right_boundary_weight_eq`** and **`starting_dir_factor_eq`** (SAWObservableProof2.lean): Right boundary edges have weight exactly 1, and the starting mid-edge has direction factor -1.

### Cleanup

- **SAWBridgeFix.lean**: Removed 4 superseded sorry'd theorems (`origin_bridge_upper_bound` [was FALSE for x-coordinate bridges], `origin_bridge_lower_bound`, `Z_xc_diverges`, `hammersley_welsh_injection`). These were superseded by the corrected paper-bridge versions in SAWDiagProof.lean and SAWPaperChain.lean. The file now has 0 sorry's.

- **SAWObservableProof2.lean**: New file with proved infrastructure for the parafermionic observable proof (boundary weight properties). Note: the "vertex relation" as a factored form (∑_w dir·exp = 0) was found to be FALSE — the correct vertex relation involves the full observable with walk-level pairing, due to the extra xc factor in the triplet cancellation.

### Blueprint updates

- Added newly proved lemmas: `paper_bridge_summable`, `paper_bridge_finite_sum_le`, `paper_bridge_sum_le_Z`, `boundary_weight_re_nonneg`
- Updated main theorem status to reflect the 3 remaining sorry's with detailed descriptions
- Updated PROOF_STATUS.md with current status

### Remaining fundamental gaps

The 3 remaining sorry's represent deep mathematical results:

- **B_paper_le_one_direct** requires formalizing the full parafermionic observable proof: defining F(z), proving the vertex relation via walk-level pair/triplet grouping, the discrete Stokes theorem (interior cancellation), and boundary evaluation. Infrastructure has been built (algebraic identities, boundary weight properties, embedding), but the walk-level combinatorial pairing remains.

- **paper_bridge_lower_bound** depends on B_paper_le_one_direct plus the strip identity passage to the infinite strip and the quadratic recurrence argument (which is already formalized abstractly in SAWDecomp.lean).

- **paper_bridge_decomp_injection** is the Hammersley-Welsh bridge decomposition — a purely combinatorial result independent of the observable. It requires formalizing the bridge decomposition algorithm and its injectivity.