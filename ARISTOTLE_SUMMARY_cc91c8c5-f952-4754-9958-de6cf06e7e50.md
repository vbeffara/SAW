# Summary of changes
## Progress on Hammersley-Welsh formalization

### Newly proved lemmas (in `RequestProject/SAWFiniteStrip.lean`)

I focused on the Hammersley-Welsh upper bound infrastructure, specifically the bridge partition bound chain. The following lemmas were proved (7 total):

1. **`finite_strip_finite`** — The set of vertices in the finite strip S_{T,L} is finite (bounded integer coordinates × Bool).

2. **`strip_saw_length_bound`** — A SAW in the finite strip has length bounded by the number of strip vertices (pigeonhole: SAW visits each vertex at most once).

3. **`B_TL_summable`** — Partition functions B_{T,L} on finite strips are summable. This was a key missing piece: the proof shows `StripSAW_B T L` is a finite type (walk lengths bounded by strip size, each length has finitely many SAWs), hence any function on it is summable.

4. **`originBridgeToStripB_len`** — The origin-bridge-to-strip map preserves walk length.

5. **`originBridgeToStripB_injective`** — The origin-bridge-to-strip map is injective (distinct bridges give distinct strip SAW elements).

6. **`origin_bridge_partial_sum_le_one`** — For any finite set F of origin bridges of width T: ∑_{b∈F} x_c^{ℓ(b)} ≤ 1. Proved by choosing L large enough that all bridges fit in S_{T,L}, mapping them injectively to StripSAW_B, and bounding by B_{T,L} ≤ 1 (from the strip identity).

7. **`origin_bridge_upper_bound_from_strip`** — B_T^{x_c} ≤ 1 for all T ≥ 1. Proved from partial sum bounds via `Real.tsum_le_of_sum_le`.

### Code cleanup

- Fixed circular dependencies in `SAWFiniteStrip.lean`: the old `origin_bridge_partial_sum_le_one` used both `origin_bridge_upper_bound` and `origin_bridge_lower_bound` (both sorry'd), creating a circular chain. The new proof properly flows from the strip identity through `B_TL_le_one`.
- Added `xc_lt_one'` locally in SAWFiniteStrip.lean.
- Added `import Mathlib` to SAWFiniteStrip.lean for better subagent access.

### Blueprint updates (`blueprint/src/content.tex`)

- Updated `finite_strip_finite` with correct Lean reference and proof description.
- Added new `strip_saw_length` lemma entry.
- Updated `partition_summable` with proof description (Finite type argument).
- Added `bridge_strip_inj` lemma entry for the injection.
- Updated `bridge_partial_sum` to reflect the corrected proof chain (no longer circular).
- Updated "Remaining sorry gaps" section with newly proved items and current status.

### Remaining sorry gaps for the main theorem

The two key remaining gaps are:

1. **`strip_identity_concrete`** (SAWFiniteStrip.lean) — Lemma 2 of the paper: 1 = c_α·A_{T,L} + B_{T,L} + c_ε·E_{T,L}. This requires formalizing the summation of the vertex relation over all strip vertices, interior edge cancellation, and boundary winding computation. The algebraic identities (pair/triplet cancellation) are fully proved.

2. **`bridge_decomposition_injection_proof`** (SAWHWDecomp.lean) — The core Hammersley-Welsh counting inequality. Requires formalizing the recursive half-plane walk decomposition into bridges, splitting at the first max-x vertex, injectivity, and weight accounting.

Both were attempted with the theorem proving subagent but are too complex for direct automation — they require substantial decomposition into helper lemmas.

All files build successfully (`lean build` passes for `RequestProject.SAWFinal`).