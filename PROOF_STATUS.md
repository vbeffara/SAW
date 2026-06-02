# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_direct` in `SAWMainNew.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 4 root sorries** (2 from the parafermionic observable
argument, 2 from submultiplicativity).

## Root Sorries

### Sorry #1: `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean)
**Statement:** `B_paper T L xc ≤ 1` for T ≥ 1, L ≥ 1.

Follows from Lemma 2 of Duminil-Copin & Smirnov (2012): the strip identity
`1 = c_α · A + B + c_ε · E` with A, E ≥ 0 implies B ≤ 1.

### Vertex Relation (Lemma 1) — Status

The cancellation identity (Lemma 1) has been formalized with a corrected
observable model using `FreshTrail` (edge freshness) in multiple files.

**Proved sorry-free:**
- `freshVertexSum_triplet_part_zero` (SAWVertexRelationProof.lean):
  The triplet part of the vertex sum = 0.
  This includes:
  - Complete bijection between fresh outgoing extensions and incoming roots
  - Extension map injective and surjective
  - Outgoing extension sum rewrite via bijection
  - Each root's triplet contribution is zero
- `freshVertexSum_decompose`: The observable decomposes by v-edge count
  into triplet part (IncomingRoot + OutgoingExt) and pair part (IncomingPair).
- `fresh_vertex_relation`: The vertex relation reduces to triplet + pair parts
  (proved assuming the pair part vanishes).

**Remaining sorry:**
- `freshVertexSum_pair_part_zero` (SAWVertexRelationProof.lean):
  The pair cancellation part = 0. This requires showing that walks from
  paperStart to n_ji that pass through v (using 2 v-edges) cancel in the
  direction-weighted sum. The algebraic pair identity (`pair_cancellation`)
  is proved, but the combinatorial bijection pairing these walks is the
  remaining gap.

### Sorry #2: `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** `1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc`

The parafermionic observable identity for the infinite strip.

### Sorry #3-4: `saw_count_exp_bound` and `hw_summable_direct` (SAWMainNew.lean)
Submultiplicativity-based bounds, independent of the observable.

## Parafermionic Observable and Cancellation Identity

### Fully Proved (sorry-free)

#### Core algebraic identities (SAW.lean)
- `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0

#### Direction vectors (SAWObservable.lean, SAWObservableDef.lean)
- `midEdgeDir_j_relation`: d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
- `false_vertex_j_relation` / `true_vertex_j_relation`
- `midEdgeDir_zero_ne_zero`: d₀ ≠ 0 at every vertex

#### Hex lattice neighbor structure (SAWCancellationProof.lean)
- `hexNeighbors3_complete`: every neighbor is one of the three listed
- `hexNeighbors3_injective`: the three neighbors are distinct
- `j_cube_eq_one'`: j³ = 1
- `j_sum_zero'`: 1 + j + j² = 0
- `j_sq_eq_conj'`: j² = conj(j)

#### Vertex relation structure (SAWCancellationProof.lean)
- `vertex_relation_from_reduced`: F₀ + j·F₁ + j̄·F₂ = 0 → full relation = 0
- `reduced_from_vertex_relation`: full relation = 0 → reduced form
- `vertexContrib_triplet_zero`: single triplet contribution = 0
- `vertexContrib_pair_zero`: single pair contribution = 0
- `sum_zero_of_partition_cancel`: abstract partition → total = 0

#### Walk partition operations (SAWCancellationFull.lean, SAWWalkPartitionComplete.lean)
- `extend_zero_v_edges`: 0-v-edge root → 1-v-edge extension
- `outgoing_1_v_edge_retract`: 1-v-edge extension → 0-v-edge root
- `extend_vEdgeCount_one`: extension has exactly 1 v-edge
- `extend_is_trail` / `extend_is_path`: extension preserves trail/path
- `extend_injective`: different roots give different extensions
- `retract_extend_gives_j`: retraction recovers root index
- `path_vEdgeCount_zero_or_one`: paths have 0 or 1 v-edges

#### Vertex relation from walk partition (SAWCancellationLemma1.lean)
- `triplet_contrib_zero_at_vertex`: any triplet at any vertex = 0
- `pair_contrib_zero_at_vertex`: any pair at any vertex = 0
- `vertex_relation_from_triplets`: triplet-organized walks sum to 0
- `vertex_relation_combined`: triplets + pairs sum to 0

#### Winding computations (SAWObservableDef.lean, SAWWindingGeneral.lean)
- `arg_neg_j`: arg(-j) = -π/3
- `arg_neg_conj_j`: arg(-conj(j)) = π/3
- `triplet_winding_ext1` / `triplet_winding_ext2`: winding ±π/3 for extensions
- `triplet_winding_general_k` / `triplet_winding_general_l`: general winding
- `hexWalkWinding_extend`: winding decomposition for list append
- `turning_angle_clockwise` / `turning_angle_counterclockwise`: ∓π/3
- `direction_ratio_clockwise` / `direction_ratio_counterclockwise`: ratio = -j/-j̄
- `neg_midEdgeDir_ratio_k` / `neg_midEdgeDir_ratio_l`: direction ratios

#### Trail structure (SAWTrailStructure.lean)
- `hex_trail_revisit_is_endpoint`: revisit → endpoint on hex lattice
- `hex_edges_incident_le_three`: ≤ 3 incident edges per vertex
- `right_boundary_trail_is_path`: boundary trails are vertex-SAWs

#### Trail-based observable and classification (SAWCancellationIdentity.lean)
- `StripTrail`: trail from paperStart to a mid-edge in the finite strip
- `trailObs`: the trail-based parafermionic observable F(z)
- `strip_trail_length_bound`: trails have bounded length in finite strip
- `strip_trail_finite`: strip trails form a finite type
- `tripletExtendStrip`: triplet extension operation in the strip
- `tripletExtendStrip_len`: extension has length ℓ+1
- `tripletExtendStrip_vEdge`: extension has exactly 1 v-edge
- `incoming_trail_vEdge_classify`: incoming trails: 0 or 2 v-edges
- `outgoing_trail_vEdge_classify`: outgoing trails: 1 or 3 v-edges
- `strip_triplet_zero` / `strip_pair_zero`: each group contributes zero

#### Fresh trail observable (SAWPathVertexRelation.lean)
- `FreshTrail`: trail with edge freshness (prevents self-crossing at mid-edges)
- `freshObs` / `freshVertexSum`: fresh observable and vertex sum
- `freshExtend`: extension operation for fresh trails
- `freshExtend_len` / `freshExtend_winding_k` / `freshExtend_winding_l`
- `fresh_triplet_cancel`: each fresh triplet sums to zero

#### Fresh trail vertex relation infrastructure (SAWVertexRelationProof.lean)
- `fresh_incoming_vEdgeCount_classify`: fresh incoming → 0 or 2 v-edges
- `fresh_outgoing_vEdgeCount_one`: fresh outgoing → exactly 1 v-edge
- `fresh_incoming_decompose` / `fresh_outgoing_decompose`: sum decomposition
- `freshExtensionMap` / `freshExtensionMap_injective`: extension bijection
- `fresh_outgoing_surj`: every outgoing ext from some root
- `sigmaExtMap_inj` / `sigmaExtMap_surj`: sigma extension bijection
- `outExt_sum_split`: outgoing sum splits by root index
- `rootTripletContrib_zero`: each root's triplet = 0
- **`freshVertexSum_triplet_part_zero`**: triplet part of vertex sum = 0

#### Concrete path-based observable (SAWStripObservable.lean)
- `StripPathToMidEdge`: vertex-SAW from paperStart to a mid-edge
- `stripPathObs`: the observable as tsum over vertex-SAWs
- `starting_path_unique`: trivial walk is unique walk from a to a
- `starting_path_weight` / `walkWeight_zero_one'`: F(a) = xc

#### Boundary evaluation (SAWVertexRelation.lean, SAWDiscreteStokes.lean)
- `left_boundary_contrib_re`: Re((-1)·e^{-iσπ}) = c_α
- `boundary_cos_pos`: boundary phases positive
- `interior_midedge_cancels`: opposite directions cancel
- `starting_direction`: starting mid-edge direction = -1

### Remaining Sorries (Cancellation Identity Chain)

1. **`freshVertexSum_pair_part_zero`** (SAWVertexRelationProof.lean, line 413):
   The pair part of the fresh vertex sum vanishes. Requires showing that walks
   passing through v (IncomingPair: 2 v-edges) cancel in the direction-weighted
   sum. All algebraic ingredients proved; remaining gap is the combinatorial
   walk partition for 2-v-edge walks.

2. **`trail_vertex_relation`** (SAWCancellationIdentity.lean, line 315):
   Depends on the above through `fresh_vertex_relation`.

3. **`vertex_relation_strip`** (SAWStripObservable.lean, line 172):
   Same vertex relation for path-based observable.

4. **`triplet_part_zero` / `pair_part_zero`** (SAWTrailVertexRelation.lean):
   Older formulation of the same vertex relation.

All these sorries reduce to the same core problem: the combinatorial walk
partition argument for the cancellation identity.

## Proof Architecture

```
pair_cancellation + triplet_cancellation (PROVED)
  → vertexContrib_triplet_zero + vertexContrib_pair_zero (PROVED)
  → trail/fresh trail classification (PROVED)
  → freshVertexSum_triplet_part_zero (PROVED)
  → freshVertexSum_pair_part_zero (SORRY — walk partition for 2-v-edge walks)
    → fresh_vertex_relation (PROVED modulo pair part)
    → discrete Stokes → B_paper_le_one_strip (SORRY)
    → discrete Stokes → infinite_strip_identity (SORRY)
```
