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

### New: Cancellation Identity Key Lemmas (PROVED)

The following key lemmas for the cancellation identity (Lemma 1) have been
formalized and proved sorry-free in `SAWCancellationProved.lean` and
`SAWWindingLemma.lean`:

- `direction_ratio_clockwise` — at any hex vertex, the ratio of direction
  vectors for the clockwise extension equals -j (cube root of unity)
- `direction_ratio_counterclockwise` — same for counterclockwise, equals -conj(j)
- `turning_angle_clockwise` — turning angle at v for clockwise extension is -π/3
- `turning_angle_counterclockwise` — turning angle for counterclockwise is +π/3
- `hexWalkWinding_snoc` — appending a vertex adds the turning angle to the winding
- `extension_winding_cw` — winding of the clockwise extension = root winding - π/3
- `extension_winding_ccw` — winding of counterclockwise extension = root winding + π/3
- `strip_trail_triplet_vanishes` — each triplet's contribution to the vertex
  relation sum is zero (combines winding, length, and algebraic cancellation)
- `triplet_algebraic_zero` — the algebraic triplet identity for all vertices

These establish the GEOMETRIC part of the cancellation identity: the winding
relation ±π/3 for extensions at any vertex, for any neighbor index j.
Combined with the algebraic triplet cancellation (already proved), each
triplet of walks contributes zero to the vertex relation sum.

The remaining gap is the COMBINATORIAL part: showing that every trail to
v's mid-edges belongs to exactly one cancelling group (triplet or pair).

### Sorry #2: `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** `1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc`

The parafermionic observable identity for the infinite strip.

### Sorry #3-4: `saw_count_exp_bound` and `hw_summable_direct` (SAWMainNew.lean)
Submultiplicativity-based bounds, independent of the observable.

## Parafermionic Observable and Cancellation Identity

### Proved (sorry-free)

#### Core algebraic identities (SAW.lean)
- `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0

#### Direction vectors (SAWObservable.lean, SAWObservableDef.lean)
- `midEdgeDir_j_relation`: d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
- `false_vertex_j_relation` / `true_vertex_j_relation`

#### Vertex relation structure (SAWCancellationProof.lean, SAWObservableFormal.lean)
- `vertexContrib_triplet_zero`: single triplet contribution = 0
- `vertexContrib_pair_zero`: single pair contribution = 0
- `vertex_relation_from_reduced`: F₀ + j·F₁ + j̄·F₂ = 0 → full relation
- `sum_zero_of_partition_cancel`: abstract partition → total sum = 0

#### Walk partition operations (SAWWalkPartitionComplete.lean, SAWCancellationFull.lean)
- `extend_zero_v_edges` / `outgoing_1_v_edge_retract`: extension/retraction maps
- `extend_vEdgeCount_one`: extension has exactly 1 v-edge
- `extend_is_trail` / `extend_is_path`: extension preserves trail/path
- `extend_injective`: different roots give different extensions
- `path_vEdgeCount_le_one`: vertex-SAWs have ≤ 1 v-edge

#### Vertex relation from walk partition (SAWCancellationLemma1.lean)
- `vertex_relation_from_triplets`: triplet-organized walks sum to 0
- `vertex_relation_combined`: triplets + pairs sum to 0
- `triplet_contrib_zero_at_vertex`: any triplet at any vertex = 0
- `pair_contrib_zero_at_vertex`: any pair at any vertex = 0

#### Trail structure (SAWTrailStructure.lean)
- `hex_trail_revisit_is_endpoint`: revisit → endpoint on hex lattice
- `right_boundary_trail_is_path`: boundary trails are vertex-SAWs

#### Boundary evaluation (SAWVertexRelation.lean, SAWDiscreteStokes.lean)
- `left_boundary_contrib_re`: Re((-1)·e^{-iσπ}) = c_α
- `boundary_cos_pos`: all boundary phases positive
- `interior_midedge_cancels`: opposite directions cancel

#### Trail-based observable and classification (SAWCancellationIdentity.lean — NEW)
- `StripTrail`: trail from paperStart to a mid-edge in the finite strip
- `trailObs`: the trail-based parafermionic observable F(z)
- `strip_trail_length_bound`: trails have bounded length in finite strip
- `strip_trail_finite`: strip trails form a finite type
- `tripletExtendStrip`: triplet extension operation in the strip
- `tripletExtendStrip_len`: extension has length ℓ+1
- `tripletExtendStrip_vEdge`: extension has exactly 1 v-edge
- `three_vEdges_implies_two_visits`: 3 v-edges → vertex visited ≥ 2 times
- `trail_vEdge_le_two_interior`: interior vertices have ≤ 2 v-edges
- `incoming_trail_vEdge_classify`: incoming trails: 0 or 2 v-edges
- `vEdgeCount_odd_at_endpoint`: parity of v-edges at endpoint
- `outgoing_trail_vEdge_classify`: outgoing trails: 1 or 3 v-edges
- `strip_triplet_zero`: each triplet contributes zero
- `strip_pair_zero`: each pair contributes zero

#### Concrete observable infrastructure (SAWStripObservable.lean)
- `StripPathToMidEdge`: vertex-SAW from paperStart to a mid-edge in the strip
- `stripPathObs`: the observable F(z) as a tsum over vertex-SAWs
- `starting_path_unique`: the trivial walk is the unique walk from a to a
- `starting_path_weight`: weight of the trivial walk = walkWeight 0 1 xc sigma
- `walkWeight_zero_one'`: walkWeight 0 1 xc sigma = xc

#### Triplet extension in the strip (SAWTripletInStrip.lean)
- `extension_in_strip`: extending a trail in the strip stays in strip
- `extension_adds_one_v_edge`: extension produces exactly 1 v-edge
- `zero_v_edges_implies_fresh'`: 0 v-edges → edge is fresh for extension
- `extension_is_trail`: extension preserves trail property

### Remaining gaps

1. **`trail_vertex_relation`** (SAWCancellationIdentity.lean): The vertex
   relation for the trail-based observable. All algebraic and classification
   ingredients are proved. The remaining gap is the combinatorial walk
   partition bijection — showing every trail belongs to exactly one
   cancelling group (triplet or pair).

2. **Discrete Stokes summation**: Summing vertex relations over all strip
   vertices, showing interior mid-edges cancel pairwise.

3. **Boundary evaluation for the strip**: Connecting boundary observable
   values to partition functions A, B, E.

4. **Limiting argument**: L → ∞ for the infinite strip identity.

## Proof Architecture

```
pair_cancellation + triplet_cancellation (PROVED)
  → vertexContrib_triplet_zero + vertexContrib_pair_zero (PROVED)
  → trail classification (incoming: 0/2, outgoing: 1/3) (PROVED)
  → trail_vertex_relation (sorry — walk partition bijection)
    → discrete Stokes → B_paper_le_one_strip (sorry #1)
    → discrete Stokes → infinite_strip_identity (sorry #2)
```
