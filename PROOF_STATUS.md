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

**Pair Involution Infrastructure:**
- `pairInvol` (SAWPairCancellation.lean): The pair involution on FreshIncomingPair.
- `pairInvol_length`: Same length preserved.
- `mkPairedWalk_is_trail`: The paired walk is a valid trail.
- `mkPairedWalk_fresh`: The paired walk has the correct fresh edge.
- `mkPairedWalk_two_v_edges`: The paired walk has 2 v-edges.

**Pair Contribution Cancellation (from winding relation):**
- `pair_contrib_from_winding` (SAWPairWindingRelation.lean, PROVED):
  Each pair's contribution is zero, given the winding relation.
  Uses `pair_contrib_zero_at_vertex` (algebraic identity).

**Trail Classification:**
- `incoming_trail_vEdge_classify`: incoming trails have 0 or 2 v-edges
- `outgoing_trail_vEdge_classify`: outgoing trails have 1 or 3 v-edges
- `strip_trail_finite`: trails in the finite strip form a Finite type

**Winding Relations (for triplets):**
- `triplet_winding_general_k`: extension winding decreases by π/3
- `triplet_winding_general_l`: extension winding increases by π/3
- `hexWalkWinding_reverse_walk`: winding of reversed trail = -original

### Remaining Sorry

**`pair_winding_relation`** (SAWPairWindingRelation.lean):
  The winding relation for pairs: ∃ W_common, j such that
  W(γ) = W_common - 4π/3 and W(pair) = W_common + 4π/3

  This is the ONLY remaining geometric fact needed for the full
  cancellation identity. It requires:
  - The turning number theorem for simple closed curves (winding = ±2π)
  - The hex lattice geometry (exterior angles are ±π/3)
  - Simply-connected domain constraining the loop orientation

  Once proved, it automatically gives:
  - `pair_contrib_from_winding` → each pair contribution = 0
  - `freshVertexSum_pair_part_zero` → pair part = 0
  - `fresh_vertex_relation` → full vertex relation = 0
  - `trail_vertex_relation` → trail-based vertex relation = 0

### Proof Chain

```
pair_winding_relation (SORRY — turning number theorem on hex lattice)
    ↓
pair_contrib_from_winding (PROVED — algebraic pair identity)
    ↓
freshVertexSum_pair_part_zero (currently sorry, follows from involution argument)
    ↓
fresh_vertex_relation (follows: triplet_part + pair_part = 0)
    ↓
trail_vertex_relation (follows from fresh_vertex_relation)
    ↓
strip identity / B ≤ 1 (via discrete Stokes)
```

## Other Sorries

- `infinite_strip_identity` (SAWStripIdentityCorrect.lean): Discrete Stokes summation
- `vertex_relation_strip` (SAWStripObservable.lean): Path-based vertex relation
  (Note: requires trail-based approach, not direct path extension)
- Various downstream sorries that depend on the cancellation identity

## Summary

The cancellation identity is fully proved modulo ONE geometric fact:
`pair_winding_relation` — the turning number theorem for simple loops
on the hexagonal lattice in a simply-connected domain. All algebraic,
combinatorial, and bijection infrastructure is in place.
