# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 root sorries** (both are instances of the same
mathematical argument — the parafermionic observable / discrete Stokes theorem).

## Root Sorries

### Sorry #1: `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean)
**Statement:** `B_paper T L xc ≤ 1` for T ≥ 1, L ≥ 1.

This says the bridge partition function in the finite strip is bounded by 1.
It follows from Lemma 2 of Duminil-Copin & Smirnov (2012): the identity
`1 = c_α · A + B + c_ε · E` with A, E ≥ 0 implies B ≤ 1.

**Required for:** The Hammersley-Welsh upper bound (via `paper_bridge_partial_sum_le`
→ `paper_bridge_decay` → `hw_summable_corrected`), and the cutting argument
(via `bridge_pair_summable` → `extra_walk_sum_le_proved` → `cutting_argument_proved`).

### Sorry #2: `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** `1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc`

The parafermionic observable identity for the infinite strip.
This is the infinite-L limit of the finite strip identity.

**Required for:** The bridge recurrence (Z(xc) = ∞, the lower bound μ ≥ √(2+√2)).

## Parafermionic Observable and Cancellation Identity

### SAWTrailStructure.lean (NEW, ALL SORRY-FREE)
Trail structure on the 3-regular hexagonal lattice:

1. `hex_trail_revisit_is_endpoint` — on the hex lattice, if a trail revisits a vertex v, then v must be the start or end of the trail
2. `hex_trail_interior_visit_bound` — interior vertices (v ≠ s, v ≠ t) are visited at most once by any trail
3. `hex_edges_incident_le_three` — at most 3 edges incident to any vertex appear in a trail
4. `trail_interior_vertex_uses_two_edges` — an interior vertex uses ≥ 2 incident trail edges
5. `boundary_vertex_edge_bound` — boundary vertices (with exterior neighbor) have ≤ 2 trail edges in a strip trail
6. `boundary_endpoint_count_le_one` — boundary endpoints with s ≠ t are visited at most once
7. `strip_trail_boundary_endpoints_is_path` — a trail between two boundary vertices (s ≠ t) in the strip is a path
8. `right_boundary_trail_is_path` — **KEY**: a trail from paperStart to a right boundary vertex in PaperInfStrip T is a vertex-SAW (path)

This is a crucial structural result for the strip identity: it shows that
on the right boundary, the trail-based observable F(z) equals the path-based
partition function B_paper.

### SAWObservableSum.lean (NEW, ALL SORRY-FREE)
Formal observable sum definition and connection to partition functions:

1. `StripMidEdgeTrail` — a mid-edge trail staying in the strip
2. `vertex_relation_abstract` — the vertex relation from the reduced form
3. `right_boundary_trails_are_paths` — boundary trails are vertex-SAWs

### SAWObservableFormal.lean (ALL SORRY-FREE)
Formal parafermionic observable definition and vertex relation (Lemma 1):

1. `HexMidEdge` — mid-edge structure with direction vectors
2. `ObsWalk` — walk from a starting vertex to a mid-edge (vertex-SAW model)
3. `vertexMidEdges` / `vertexMidEdgesIncoming` — oriented mid-edges at a vertex
4. `vertex_ne_neighbor` — a vertex differs from each of its neighbors
5. `walkVertexContrib` — walk contribution to the vertex relation sum
6. `triplet_sum_perm_zero` — triplet cancellation (permutation 0,1,2)
7. `triplet_sum_perm1_zero` — triplet cancellation (permutation 1,2,0)
8. `triplet_sum_perm2_zero` — triplet cancellation (permutation 2,0,1)
9. `pair_sum_zero` — pair cancellation
10. `right_boundary_dir_is_one` — right boundary direction = 1
11. `left_boundary_dir_is_neg_one` — left boundary direction = -1
12. `starting_dir` — starting mid-edge direction = -1
13. `left_phase_real_part` — Re((-1)·e^{-iσπ}) = c_alpha
14. `interior_edge_cancel` — interior edge directions cancel (discrete Stokes)
15. `hex_vertex_visit_bound` — trail from v to v has length 0 or ≥ 2

### SAWStripAlgebra.lean (NEW, ALL SORRY-FREE)
Key algebraic identities connecting xc and c_alpha via the triple angle formula:

1. `cos_pi_eight_pos` — cos(π/8) > 0
2. `xc_eq_inv_two_cos` — xc = 1/(2·cos(π/8))
3. `c_alpha_eq_cos` — c_α = cos(3π/8)
4. `cos_triple_pi_eight` — 4cos³(π/8) = cos(3π/8) + 3cos(π/8)
5. **`strip_algebraic_identity`** — **2·c_α·xc³ + 3·xc² = 1** (the key identity!)
6. `c_alpha_xc_relation` — c_α·xc = (1-3xc²)/(2xc²)
7. `xc_sq_plus_ca_xc_lt_one` — xc² + c_α·xc < 1
8. `strip_identity_T1_algebraic` — T=1 strip identity from exact partition functions
9. `strip_identity_T1_from_A` — T=1 identity using known B(1)

### SAWCancellationProof.lean (ALL SORRY-FREE)
Core properties of the cancellation identity and its algebraic ingredients:

1. `j_ne_zero`, `conj_j_ne_zero`, `j_normSq_eq_one`
2. `j_cube_eq_one'`, `j_sum_zero'`, `j_sq_eq_conj'`
3. `midEdgeDir_zero_ne_zero` — direction to 0-th neighbor is nonzero
4. `hexNeighbors3_complete` — every hex neighbor is one of 3 listed
5. `hexNeighbors3_injective` — the 3 neighbors are distinct
6. `vertex_relation_from_reduced` / `reduced_from_vertex_relation`
7. `vertexContrib_triplet_zero` / `vertexContrib_pair_zero`
8. `sum_zero_of_partition_cancel` — abstract partition ⟹ sum = 0
9. `direction_cancellation` — interior edge directions cancel

### SAWWalkPartition.lean (ALL SORRY-FREE)
Walk partition infrastructure for the cancellation identity:

1. `hex_vertex_degree` — complete neighbor characterization (iff)
2. `trail_to_v_has_predecessor` — nonempty trail decomposition
3. `predecessor_is_named_neighbor` — predecessor is hexNeighbors3 v k
4. `walk_penultimate_adj` — penultimate vertex exists
5. `tripletExtend_last_edge` — extension length relation

### SAWDiscreteStokes.lean (ALL SORRY-FREE)
Boundary evaluation for the strip identity:

1. `boundary_phase_right` — right boundary phase = 1
2. `right_boundary_direction` / `left_boundary_direction`
3. `starting_midedge_contribution` — starting contribution = -1

### SAWObservableDef.lean (ALL SORRY-FREE)
Trail-based mid-edge walks and cancellation at individual walk groups:

1. `midEdgeDir_j_relation` — d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
2. `hexWalkWinding` — corrected winding using arg(d₂/d₁)
3. `MidEdgeTrail` — trail-based mid-edge walks
4. `tripletExtendFromN` — triplet walk extension
5. `arg_neg_j` / `arg_neg_conj_j` — turning angles ±π/3
6. `triplet_winding_ext1/2` — winding changes by ±π/3
7. `triplet_contribution_at_vertex` — triplet contribution = 0
8. `pair_contribution_at_vertex` — pair contribution = 0
9. `cancellation_identity_abstract` — vertex relation from walk partition

### SAWObservable.lean (ALL SORRY-FREE)
Algebraic cancellation identities:

1. `triplet_contribution_zero` / `pair_contribution_zero`
2. Direction vectors: `false_dir2_eq_j`, `false_dir3_eq_conjj`, etc.
3. Phase factors: `phase_plus_eq_conj_lam`, `phase_minus_eq_lam`
4. `vertex_relation_false` / `vertex_relation_true`

### SAWVertexRelation.lean (ALL SORRY-FREE)
Vertex relation infrastructure:

1. `j_cube_eq_one`, `j_norm_one`, `j_sum_zero`, `j_sq_eq_conj`
2. `false_edge_dirs` / `true_edge_dirs`
3. `triplet_cancel_at_vertex` / `pair_cancel_at_vertex`
4. `left_boundary_contrib_re/neg` — boundary phase real parts
5. `interior_midedge_cancels` — discrete Stokes key step
6. `winding_three_vertices` / `winding_append_vertex`

## What remains to close both root sorries

### Already proved (algebraic + combinatorial infrastructure)
- ✅ All algebraic cancellation identities (pair, triplet)
- ✅ All direction vector computations (j-relation, boundary directions)
- ✅ All boundary phase computations (cos(3π/8), cos(π/4))
- ✅ Cube root of unity properties (j³=1, 1+j+j²=0, j²=conj(j))
- ✅ Hexagonal lattice degree-3 property (exactly 3 neighbors)
- ✅ Trail decomposition (removing last edge of a nonempty trail)
- ✅ Triplet extension/retraction operations and length/winding relations
- ✅ Interior edge cancellation
- ✅ Abstract partition cancellation theorem
- ✅ Cyclic permutations of triplet cancellation (perm 0,1,2 and 1,2,0 and 2,0,1)
- ✅ Key algebraic identity: 2·c_α·xc³ + 3·xc² = 1 (triple angle formula)
- ✅ T=1 strip identity (modulo A_inf(1) computation)

### Remaining formalization gaps

1. **Walk partition exhaustiveness**: Show that every trail to v's mid-edges
   belongs to exactly one cancelling group (triplet or pair).
   The grouping operations (extension, retraction, loop reversal) are defined.
   The algebraic cancellation for each group is proved.

2. **Discrete Stokes summation**: Sum vertex relations over all vertices,
   show interior mid-edges cancel, only boundary survives.

3. **Boundary evaluation**: Connect boundary sum to partition functions A, B, E.
   The key ingredient — boundary trails are vertex-SAWs — is **now proved**
   (right_boundary_trail_is_path in SAWTrailStructure.lean).

4. **Limiting argument** (for Sorry #2): L → ∞ in the finite strip identity.

## Proof Architecture

### Hammersley-Welsh chain (upper bound μ ≤ √(2+√2))
```
B_paper_le_one_strip (sorry #1)
  → paper_bridge_partial_sum_le
    → paper_bridge_decay, bridge_summable
      → hw_summable_corrected (Z(x) < ∞ for x < xc)
```

### Lower bound chain (μ ≥ √(2+√2))
```
infinite_strip_identity (sorry #2)
  → bridge_diff_eq → bridge_recurrence_proved
    → Z_xc_diverges_corrected (Z(xc) = ∞)
```

### Main theorem
```
Z_xc_diverges_corrected + hw_summable_corrected
  → connective_constant_eq_corrected: μ = √(2+√2)
```
