# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 4 root sorries** (2 from the parafermionic observable
argument, 2 from submultiplicativity).

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

### Sorry #3-4: `saw_count_exp_bound` and `hw_summable_direct` (SAWMainNew.lean)
**Statement:** Submultiplicativity-based bounds on SAW counts.

These use submultiplicativity c_{n+m} ≤ c_n · c_m (which IS proved) to derive
exponential bounds on c_n. They are independent of the parafermionic observable.

## Parafermionic Observable and Cancellation Identity

### What is proved (all sorry-free)

#### Algebraic cancellations (SAW.lean, SAWObservable.lean)
- `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0
- These are the ONLY identities that use the critical value xc = 1/√(2+√2)
  and the spin σ = 5/8.

#### Direction vectors (SAWObservable.lean, SAWCancellationProof.lean)
- `midEdgeDir_j_relation`: d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
- Direction computation: FALSE → TRUE = 1, TRUE → FALSE = -1

#### Vertex relation structure (SAWCancellationProof.lean)
- `vertex_relation_from_reduced`: F₀ + j·F₁ + j̄·F₂ = 0 → full vertex relation
- `vertexContrib_triplet_zero`: triplet contribution = 0
- `vertexContrib_pair_zero`: pair contribution = 0
- `sum_zero_of_partition_cancel`: abstract partition → sum = 0

#### Walk partition operations (SAWWalkPartitionComplete.lean, SAWCancellationFull.lean)
- `extend_zero_v_edges`: 0-v-edge → 1-v-edge extension
- `outgoing_1_v_edge_retract`: 1-v-edge → 0-v-edge retraction
- `extend_vEdgeCount_one`: extension has exactly 1 v-edge
- `extend_gives_one_v_edge`: extension has 1 v-edge (walk-level)
- `extend_is_trail`: extension preserves trail property
- `extend_is_path`: extension of a path is a path (NEW)
- `retract_extend_gives_j`: retraction recovers root index (NEW)
- `path_vEdgeCount_zero_or_one`: paths have 0 or 1 v-edges (NEW)
- `zero_v_edge_path_not_in_support`: 0 v-edges + path → v ∉ support (NEW)
- `extend_v_in_support`: v is in the extension's support (NEW)
- `extend_support`: extension support = original support ++ [v] (NEW)
- `extend_injective`: different roots give different extensions (NEW)
- `extend_edges`: extension edges = original edges ++ [{n_j, v}] (NEW)

#### Vertex relation from walk partition (SAWCancellationFull.lean — NEW)
- `vertex_relation_from_triplets`: triplet-organized walks sum to 0
- `vertex_relation_combined`: triplets + pairs sum to 0
- This shows: IF walks can be partitioned into cancelling groups,
  THEN the vertex relation holds.

#### Trail structure (SAWTrailStructure.lean)
- `hex_trail_revisit_is_endpoint`: revisit → endpoint on 3-regular lattice
- `boundary_vertex_edge_bound`: boundary vertices have ≤ 2 trail edges
- `right_boundary_trail_is_path`: **KEY**: boundary trails are vertex-SAWs

#### Boundary evaluation (SAWVertexRelation.lean, SAWDiscreteStokes.lean)
- `left_boundary_contrib_re`: Re((-1)·e^{-iσπ}) = c_alpha
- `boundary_cos_pos`: all boundary phases have positive real part
- `starting_direction`: starting mid-edge direction = -1
- `interior_midedge_cancels`: d(v→w) + d(w→v) = 0

### Remaining gaps for the cancellation identity (Lemma 1 → B ≤ 1)

1. **Walk partition exhaustiveness**: Show that EVERY trail in the strip
   to one of v's mid-edges belongs to exactly one cancelling group.
   The grouping operations are defined and their basic properties proved.
   What remains: the round-trip bijection between 0-v-edge roots and
   1-v-edge extensions, and the loop reversal involution for pairs.

2. **Discrete Stokes summation**: Define the observable as a formal sum
   over trails, sum the vertex relations over all vertices, and show
   interior mid-edges cancel pairwise.

3. **Boundary evaluation**: Connect the surviving boundary terms to the
   partition functions A_paper, B_paper, E_paper.

4. **Limiting argument** (for Sorry #2): L → ∞ in the finite strip identity.

## Proof Architecture

### Upper bound chain (μ ≤ √(2+√2))
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
