# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_direct` in `SAWMainNew.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo one sorry** (`infinite_strip_identity` in SAWRecurrenceProof.lean).

The Hammersley-Welsh bound is fully proved (sorry-free), and the
convergence proof `hw_summable_direct` now uses it via `hw_summable_corrected`.

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
- `pairSigmaInvol_injective`: the pairing map is injective

**Pair Algebraic Cancellation (SAWPairCancellation.lean):**
- `pair_contrib_cancels`: each pair's contribution to vertex sum = 0
  (proved from `pair_exp_cancellation`, factoring out xc^ℓ)

**Vertex Sum Structure (SAWPairInvolutionProof.lean):**
- `freshVertexSum_pair_part_zero_proved`: The pair part of the vertex sum = 0.
  Uses the pairing map as a bijection on the sigma type.
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

1. **`pair_exp_cancellation`** (SAWPairCancellation.lean):
   The phase-weighted direction vectors of a paired walk sum to zero:
   d_k · exp(-iσ W_γ) + d_exit · exp(-iσ W_paired) = 0
   
   This encapsulates the discrete turning number theorem for simple
   closed trails on the hexagonal lattice:
   - The suffix loop [v, exit_nbr, ..., k_nbr, v] has turning number ±1
   - The sign is determined by the exit direction relative to k
   - Combined with σ = 5/8, this gives exp(-iσ ΔW) = -(d_exit/d_k)

   This is a correctly stated version that handles both cyclic and
   anticyclic orderings of the exit direction. The legacy
   `pair_winding_relation` (also sorry'd) is no longer in the
   critical chain for `pair_contrib_cancels`.

### Proof Chain

```
pair_exp_cancellation (SORRY — turning number theorem on hex lattice)
    ↓
pair_contrib_cancels (PROVED — factors out xc^ℓ + uses exp constraint)
    ↓
pairSigmaContrib_cancel (PROVED)
    ↓
pairSigmaInvol_injective (PROVED ✓)
    ↓
freshVertexSum_pair_part_zero_proved (PROVED — S = -S argument)
    ↓
fresh_vertex_relation (PROVED — triplet + pair = 0)
```

## Remaining Sorries (total: 9 sorry statements across the project)

### Critical path (main theorem):
1. **`infinite_strip_identity`** (SAWRecurrenceProof.lean): The parafermionic
   observable identity for the infinite strip. This is the ONLY sorry that
   affects the main theorem `connective_constant_eq_direct`.

### Cancellation identity chain:
2. **`pair_exp_cancellation`** (SAWPairCancellation.lean): The discrete
   turning number theorem for hex lattice loops. This is the ONLY sorry
   that affects the cancellation identity `fresh_vertex_relation`.

### Legacy / redundant:
3. **`pair_winding_relation`** (SAWPairCancellation.lean): Legacy statement
   of the pair winding relation. No longer used by `pair_contrib_cancels`
   (which now uses `pair_exp_cancellation` instead).
4. **`freshVertexSum_pair_part_zero_proof`** (SAWPairCancellation.lean):
   Redundant with `freshVertexSum_pair_part_zero_proved` in
   SAWPairInvolutionProof.lean. Not used by any other lemma.

### Alternative formulations (not in critical chain):
5. **`trail_vertex_relation`** (SAWCancellationIdentity.lean): Alternative
   trail-based vertex relation using `trailVertexSum` instead of `freshVertexSum`.
6. **`B_paper_le_one_strip`** (SAWStripIdentityCorrect.lean): Bridge bound
   for finite strip (alternative proof path, not used by main theorem).
7. **`vertex_relation_strip`** (SAWStripObservable.lean): Strip vertex
   relation using `stripVertexSum` definition.
8. **`triplet_part_zero`** (SAWTrailVertexRelation.lean): Triplet part of
   StripTrail vertex sum (uses different decomposition than FreshTrail).
9. **`pair_part_zero`** (SAWTrailVertexRelation.lean): Pair part of
   StripTrail vertex sum.

## Summary

The main theorem `μ = √(2+√2)` depends on a **single sorry**:
`infinite_strip_identity`, which is the parafermionic observable identity
for the infinite strip (Lemma 2 of the paper). This requires the full
discrete Stokes argument connecting the vertex relation to the strip
partition functions.

The cancellation identity `fresh_vertex_relation` (Lemma 1) depends on
a **single sorry**: `pair_exp_cancellation`, which requires the discrete
turning number theorem for simple closed trails on the hexagonal lattice.

The Hammersley-Welsh bound is **fully proved** (sorry-free).
