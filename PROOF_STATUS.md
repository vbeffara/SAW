# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_direct` in `SAWMainNew.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo one sorry** (`infinite_strip_identity` in SAWRecurrenceProof.lean).

The Hammersley-Welsh bound is fully proved (sorry-free), and the
convergence proof `hw_summable_direct` now uses it via `hw_summable_corrected`.

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

**Pair Involution Infrastructure (ALL sorry-free):**
- `mkPairedWalk_is_trail`: the loop-reversed walk is a trail
- `mkPairedWalk_length`: paired walk has the same length
- `mkPairedWalk_in_strip`: paired walk stays in strip
- `mkPairedWalk_fresh`: paired walk has correct fresh edge
- `mkPairedWalk_two_v_edges`: paired walk has 2 v-edges
- `pairInvol`: the pair involution operation
- `pairInvol_length`: paired walk has same length as original

**Pair Involution Helpers (sorry-free, SAWPairInvolutionHelpers.lean):**
- `v_not_in_paired_suffix`: v doesn't appear in the loop-reversed suffix
- `v_count_one_in_prefix`: v appears exactly once in the prefix
- `v_count_one_in_pairInvolWalk`: v appears exactly once in the paired walk
- `pairInvolWalk_support_eq`: paired walk support decomposes correctly
- `mkPairedWalk_support'`: support = prefix.support ++ inner.reverse.support
- `list_append_cancel_at_unique'`: list splitting at unique element
- `v_not_in_inner_rev_support`: v ∉ inner.reverse.support
- `prefix_support_ne_nil`: prefix support is nonempty
- `prefix_support_getLast`: prefix support ends at v

**Pair Involution Injectivity (sorry-free, SAWPairInvolutionProof.lean):**
- `pairSigmaInvol_injective`: **NOW PROVED** — the pairing map is injective
  Proof via support splitting: equal paired walks imply equal prefix and inner
  supports (by `list_append_cancel_at_unique'`), hence equal k indices
  (by `hexNeighbors3_injective`) and equal original walks (by Walk.ext_support).
- `inner_rev_support_head`: inner reverse support starts with hexNeighbors3 v k
- `pairInvolWalk_support_structure`: paired walk support decomposition
- `paired_walk_determines_k`: equal paired walks → equal k indices
- `paired_walk_determines_original`: equal paired walks (same k) → equal originals

**Pair Algebraic Cancellation:**
- `pair_contrib_cancels`: each pair's contribution to vertex sum = 0
  (uses pair_winding_relation)

**Vertex Sum Structure (SAWPairInvolutionProof.lean):**
- `freshVertexSum_pair_part_zero_proved`: The pair part of the vertex sum = 0.
  Uses the pairing map as a bijection on the sigma type.
  Proved from pair_contrib_cancels + pairSigmaInvol_injective.
- `fresh_vertex_relation`: **Lemma 1** — freshVertexSum T L v = 0.
  Proved from freshVertexSum_triplet_part_zero + freshVertexSum_pair_part_zero_proved.

**Trail Classification:**
- `strip_trail_finite`: strip trails form a finite type
- `incoming_trail_vEdge_classify`: incoming trails have 0 or 2 v-edges
- `outgoing_trail_vEdge_classify`: outgoing trails have 1 or 3 v-edges
- `fresh_incoming_vEdgeCount_classify`: fresh incoming trails: 0 or 2 v-edges
- `fresh_outgoing_vEdgeCount_one`: fresh outgoing trails have exactly 1 v-edge

**Winding Infrastructure:**
- `hex_turn_value`: all hex trail turns are ±π/3
- `arg_neg_j`, `arg_neg_conj_j`: arg(-j) = -π/3, arg(-conj(j)) = π/3
- `hexWalkWinding_reverse_walk`: winding of reversed trail = -original
- `hexWalkWinding_extend`: winding extends additively

### Remaining Sorry (1 for cancellation identity)

1. **`pair_winding_relation`** (SAWPairCancellation.lean):
   The winding relation for pairs: ∃ W_common, j such that
   W(γ) = W_common - 4π/3 and W(pair) = W_common + 4π/3

   This requires formalizing the discrete turning number theorem
   for simple closed curves on the hexagonal lattice.

### Proof Chain

```
pair_winding_relation (SORRY — turning number theorem on hex lattice)
    ↓
pair_contrib_cancels (PROVED — algebraic pair identity + winding)
    ↓
pairSigmaInvol_injective (PROVED ✓)    pairSigmaContrib_cancel (PROVED)
    ↓                                  ↓
freshVertexSum_pair_part_zero_proved (PROVED — S = -S argument)
    ↓
fresh_vertex_relation (PROVED — triplet + pair = 0)
```

## Main Theorem Chain

```
infinite_strip_identity (SORRY — discrete Stokes + vertex relation)
    ↓
paper_bridge_recurrence_derived (PROVED)
    ↓
Z_xc_diverges_direct (PROVED)           hw_summable_direct (PROVED ✓)
    ↓                                    ↓
connective_constant_eq_direct (PROVED — main theorem)
```

## Summary

The main theorem `μ = √(2+√2)` has been reduced to a SINGLE sorry:
`infinite_strip_identity`, which is the parafermionic observable identity
for the infinite strip (Lemma 2 of the paper).

The cancellation identity (Lemma 1) has been reduced to a SINGLE sorry:
`pair_winding_relation`, which requires the discrete turning number theorem.

Previous sorry `pairSigmaInvol_injective` has been ELIMINATED.
Previous sorry `hw_summable_direct` / `saw_count_exp_bound` have been ELIMINATED.
