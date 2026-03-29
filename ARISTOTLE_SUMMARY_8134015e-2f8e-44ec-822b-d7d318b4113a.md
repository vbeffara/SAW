# Summary of changes
## Summary of Hammersley-Welsh formalization progress

### New file: `RequestProject/SAWStripIdentity.lean`

Created a new file establishing the key infrastructure connecting bridge partition functions to SAW counts. This is essential for proving Z(xc) = ∞ (the lower bound on the connective constant).

**Fully proved lemmas** (no sorry, verified with `#print axioms`):
- `pathCastStart` / `pathCastStart_length` — utility for rewriting a path's start vertex while preserving length
- `bridgeToSAW` — converts an origin bridge of width T to a SAW from hexOrigin of the same length
- `bridgeToSAW_injective` — the conversion is injective (different bridges give different SAWs)
- `bridge_filter_card_le` — for any finite set of origin bridges, the number with length exactly n is at most saw_count(n)
- `origin_bridge_finite_sum_le_Z` — any finite partial sum of bridge weights ≤ Z(x), proved by grouping bridges by length and using the injection
- `origin_bridge_partition_le_Z` — B_T^x ≤ Z(x) whenever Z(x) is summable, via `Real.tsum_le_of_sum_le`

**Theorem with 1 remaining sorry:**
- `Z_xc_diverges_from_lower_bound` — Z(xc) diverges assuming `origin_bridge_lower_bound`. The logical structure is complete: it reduces to showing that the sequence T ↦ B_{T+1} is summable (given Z summable), which requires the disjoint injection argument (bridges of different widths T₁ ≠ T₂ end at different x-coordinates, hence give different SAWs, so ∑_T B_T ≤ Z(xc)).

### Blueprint updates (`blueprint/src/content.tex`)

Added a new subsection "Bridge-to-SAW injection" with blueprint entries for all 7 new lemmas, including `\lean{}`, `\leanok`, `\uses{}`, and proof status annotations. Updated the "Remaining sorry gaps" section to include the new disjoint bridge summability gap.

### Remaining sorry gaps for Hammersley-Welsh

The key remaining sorries in the Hammersley-Welsh argument are:

1. **`strip_identity_concrete`** (SAWFiniteStrip.lean) — The concrete strip identity 1 = c_α·A + B + c_ε·E. Requires formalizing the telescopic cancellation of the vertex relation summed over the strip domain.

2. **`origin_bridge_upper_bound`** (SAWBridgeFix.lean) — B_T^{xc} ≤ 1. Follows from the strip identity.

3. **`origin_bridge_lower_bound`** (SAWBridgeFix.lean) — B_T^{xc} ≥ c/T. Follows from the strip identity combined with the quadratic recurrence (already proved in SAWDecomp.lean).

4. **`bridge_decomposition_injection_proof`** (SAWHWDecomp.lean) — The core Hammersley-Welsh counting inequality: ∑ c_n x^n ≤ 2·(∑_S ∏ B_{T+1})². Requires formalizing the recursive bridge extraction algorithm, its injectivity, and the weight bound.

5. **Disjoint bridge summability** in `Z_xc_diverges_from_lower_bound` (SAWStripIdentity.lean) — ∑_T B_T ≤ Z(xc) via disjoint injection.

Items 1-3 form one independent chain (the strip identity → bridge bounds → lower bound). Item 4 is independent (the Hammersley-Welsh decomposition → upper bound). Item 5 is a small gap that follows from the disjoint injection already established conceptually.