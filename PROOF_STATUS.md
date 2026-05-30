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

### SAWCancellationProof.lean (NEW, ALL SORRY-FREE)
Core properties of the cancellation identity and its algebraic ingredients:

1. `j_ne_zero` — j ≠ 0
2. `conj_j_ne_zero` — conj(j) ≠ 0
3. `j_normSq_eq_one` — |j|² = 1
4. `j_cube_eq_one'` — j³ = 1
5. `j_sum_zero'` — 1 + j + j² = 0
6. `j_sq_eq_conj'` — j² = conj(j)
7. `midEdgeDir_zero_ne_zero` — direction to 0-th neighbor is nonzero
8. `hexNeighbors3_complete` — every hex neighbor is one of 3 listed
9. `hexNeighbors3_injective` — the 3 neighbors are distinct
10. `vertex_relation_from_reduced` — F₀ + jF₁ + j̄F₂ = 0 ⟹ vertex relation
11. `reduced_from_vertex_relation` — vertex relation ⟹ F₀ + jF₁ + j̄F₂ = 0
12. `vertexContrib_triplet_zero` — triplet contribution vanishes
13. `vertexContrib_pair_zero` — pair contribution vanishes
14. `sum_zero_of_partition_cancel` — abstract partition ⟹ sum = 0
15. `direction_cancellation` — interior edge directions cancel

### SAWWalkPartition.lean (NEW, ALL SORRY-FREE)
Walk partition infrastructure for the cancellation identity:

1. `hex_vertex_degree` — complete neighbor characterization (iff)
2. `trail_to_v_has_predecessor` — nonempty trail decomposition
3. `predecessor_is_named_neighbor` — predecessor is hexNeighbors3 v k
4. `walk_penultimate_adj` — penultimate vertex exists
5. `tripletExtend_last_edge` — extension length relation

### SAWDiscreteStokes.lean (NEW, ALL SORRY-FREE)
Boundary evaluation for the strip identity:

1. `boundary_phase_right` — right boundary phase = 1
2. `right_boundary_direction` — right boundary direction = 1
3. `left_boundary_direction` — left boundary direction = -1
4. `starting_midedge_contribution` — starting contribution = -1

### SAWObservableDef.lean (ALL SORRY-FREE)
Trail-based mid-edge walks and cancellation at individual walk groups:

1. `midEdgeDir_j_relation` — d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
2. `hexWalkWinding` — corrected winding function using arg(d₂/d₁)
3. `MidEdgeTrail` — trail-based mid-edge walks
4. `tripletExtendFromN` — the triplet walk extension operation
5. `arg_neg_j` / `arg_neg_conj_j` — turning angles -π/3 and π/3
6. `triplet_winding_ext1` / `triplet_winding_ext2` — winding changes by ±π/3
7. `triplet_contribution_at_vertex` — triplet contribution = 0
8. `pair_contribution_at_vertex` — pair contribution = 0
9. `cancellation_identity_abstract` — vertex relation from walk partition

### SAWObservable.lean (ALL SORRY-FREE)
Algebraic cancellation identities:

1. `triplet_contribution_zero` — triplet sum = 0 for any d, W, ℓ
2. `pair_contribution_zero` — pair sum = 0 for any d, W, ℓ
3. Direction vectors: `false_dir2_eq_j`, `false_dir3_eq_conjj`, etc.
4. Phase factors: `phase_plus_eq_conj_lam`, `phase_minus_eq_lam`

### SAWVertexRelation.lean (ALL SORRY-FREE)
Vertex relation infrastructure:

1. `j_cube_eq_one` — j³ = 1
2. `false_edge_dirs` / `true_edge_dirs` — direction vectors
3. `triplet_cancel_at_vertex` / `pair_cancel_at_vertex`
4. Boundary phases: `left_boundary_contrib_re`, `right_boundary_phase'`
5. `interior_midedge_cancels` — discrete Stokes key step
6. `winding_three_vertices` / `winding_append_vertex` — winding structure

### SAW.lean (ALL SORRY-FREE)
Core algebraic identities:

1. `pair_cancellation` — j·conj(λ)⁴ + conj(j)·λ⁴ = 0
2. `triplet_cancellation` — 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
3. `xc_inv_eq` — xc⁻¹ = 2·cos(π/8)
4. `c_alpha_pos`, `c_eps_pos`, `xc_pos`

## What remains to close both root sorries

### Already proved (algebraic + combinatorial infrastructure)
- All algebraic cancellation identities (pair, triplet)
- All direction vector computations (j-relation, boundary directions)
- All boundary phase computations (cos(3π/8), cos(π/4))
- Cube root of unity properties (j³=1, 1+j+j²=0, j²=conj(j))
- Hexagonal lattice degree-3 property (every vertex has exactly 3 neighbors)
- Trail decomposition (removing last edge of a nonempty trail)
- Triplet extension/retraction operations
- Interior edge cancellation (direction_cancellation)
- Abstract partition cancellation theorem

### Remaining formalization gaps

1. **Walk partition exhaustiveness**: Show that every walk at v's mid-edges
   belongs to exactly one cancelling group (triplet or pair). The
   extension/retraction infrastructure is proved; what remains is connecting
   it to the observable sum.

2. **Formal observable definition**: Define F(z) = Σ_γ e^{-iσW} xc^ℓ as a
   formal tsum over walks/trails from the start to mid-edge z.

3. **Discrete Stokes summation**: Sum the vertex relation over all vertices,
   show interior mid-edges cancel, and only boundary mid-edges survive.

4. **Boundary evaluation**: Connect the boundary sum to the partition
   functions A, B, E (already computed individual boundary phases).

5. **Limiting argument** (for Sorry #2): Taking L → ∞ in the finite strip
   identity, using monotonicity and boundedness.

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

## Files

### New files (this session)
- `SAWCancellationProof.lean` — j properties, direction vectors, vertex relation equivalences, partition cancellation (ALL SORRY-FREE)
- `SAWWalkPartition.lean` — trail decomposition, predecessor identification, extension/retraction (ALL SORRY-FREE)
- `SAWDiscreteStokes.lean` — boundary phases and strip identity architecture (ALL SORRY-FREE)

### SAWHW*.lean files (22 files) — ALL SORRY-FREE
The Hammersley-Welsh bridge decomposition.

### Key infrastructure files
- `SAW.lean` — hex lattice, constants, pair/triplet cancellation
- `SAWStrip.lean` — strip domains, observable framework
- `SAWStripIdentityCorrect.lean` — PaperSAW_B, B_paper, sorry #1
- `SAWDiagProof.lean` — PaperBridge, paper_bridge_partition
- `SAWRecurrenceProof.lean` — sorry #2, bridge recurrence
- `SAWPaperChain.lean` — main theorem assembly
- `SAWObservable.lean` — parafermionic observable, algebraic cancellations
- `SAWObservableDef.lean` — trail-based observable, MidEdgeTrail, cancellation at vertex
- `SAWVertexRelation.lean` — vertex relation, cube root properties, boundary phases
