# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_direct` in `SAWMainNew.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo root sorries** (from the parafermionic observable
argument and submultiplicativity).

## Cancellation Identity (Lemma 1) — Status

The cancellation identity (Lemma 1) from Section 2 of Duminil-Copin & Smirnov (2012) 
states that for every interior vertex v:
  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0

### Fully Proved (sorry-free)

**Algebraic Cancellations:**
- `pair_cancellation` (SAW.lean): j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- `triplet_cancellation` (SAW.lean): 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0

**Direction Vectors:**
- `midEdgeDir_j_relation`: d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
- `false_vertex_j_relation`, `true_vertex_j_relation`

**Triplet Extension & Cancellation:**
- `freshVertexSum_triplet_part_zero` (SAWVertexRelationProof.lean):
  The triplet part of the vertex sum = 0.
  Complete bijection between fresh outgoing extensions and incoming roots.
- `fresh_triplet_cancel` (SAWPathVertexRelation.lean): Each triplet sums to 0.
- `triplet_contribution_at_vertex`, `pair_contribution_at_vertex`

**Walk Partition Operations:**
- Extension/retraction bijection for 0-v-edge ↔ 1-v-edge trails
- Trail classification by v-edge count (0 or 2 incoming, 1 or 3 outgoing)
- `strip_trail_finite`, `fresh_trail_finite`: finiteness of strip trails

**Winding Reversal (NEW):**
- `hexWalkWinding_reverse_walk` (SAWPairWinding.lean): 
  For a hex trail of length ≥ 2, hexWalkWinding(walk.reverse.support) = -hexWalkWinding(walk.support).
  This is the key building block for the pair cancellation.
- Helper lemmas: `hex_embed_sub_ne_zero'`, `hex_turn_neg'`, `HexTrailList`, 
  `walk_support_is_hex_trail_list'`, `hexWalkWinding_reverse_list'`

**Pair Involution Infrastructure (NEW):**
- `pairInvol` (SAWPairCancellation.lean): Construction of the loop-reversed walk
  for FreshIncomingPair walks.
- `pairInvol_length`: Paired walk has the same length as the original.
- `mkPairedWalk_is_trail`, `mkPairedWalk_fresh`, `mkPairedWalk_in_strip`,
  `mkPairedWalk_two_v_edges`, `mkPairedWalk_length` (SAWPairInvolution.lean)
- `v_not_in_inner_support`: The inner walk doesn't revisit v.

### Remaining Gaps

**Pair Cancellation:**
- `pair_contrib_cancels` (SAWPairCancellation.lean): The winding relation between
  paired walks (showing ΔW = ±8π/3) is not yet established. This requires:
  - A loop winding theorem (Gauss-Bonnet for discrete hex lattice curves)
  - Connecting the winding reversal to the overall winding difference
- `freshVertexSum_pair_part_zero` (SAWVertexRelationProof.lean):
  The pair part of the vertex sum = 0. Depends on pair_contrib_cancels.

**Downstream:**
- `fresh_vertex_relation` (SAWVertexRelationProof.lean): Follows from
  triplet part (proved) + pair part (gap).
- `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean): Follows from
  vertex relation + discrete Stokes summation.

## New Files

- `SAWWindingReverse.lean`: Re-exports winding reversal results
- `SAWPairCancellation.lean`: Pair involution and cancellation infrastructure
- `SAWPairWinding.lean`: Winding reversal lemmas (all sorry-free)
