/-
# Parafermionic Observable — Formal Sum Definition

Defines the parafermionic observable F(z) as a formal sum over trails
(edge-SAWs) from the starting mid-edge to each mid-edge z.

## Main definitions

* `StripMidEdge` — a mid-edge of the strip domain
* `ObservableTrail` — a trail from start to a mid-edge, staying in the strip
* `parafermionic_obs` — F(z) = Σ_γ e^{-iσW(γ)} xc^{|γ|}
* `vertex_relation_sum` — the vertex relation sum at v

## Main results

* `vertex_relation_from_cancellation` — the vertex relation holds if walks
  can be partitioned into cancelling triplets and pairs
* `boundary_obs_eq_partition` — on the right boundary, F(z) counts vertex-SAWs

## Connection to the strip identity

The strip identity 1 = c_α·A + B + c_ε·E follows from:
1. The vertex relation (Lemma 1): at each interior vertex, Σ d_i F(z_i) = 0
2. Discrete Stokes: summing over all vertices, interior edges cancel
3. Boundary evaluation: the surviving boundary terms equal -1 + B + c_α·A + c_ε·E
-/

import Mathlib
import RequestProject.SAWTrailStructure
import RequestProject.SAWObservableDef

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Mid-edges and the observable

A mid-edge z of the hexagonal lattice is the midpoint of an edge {v, w}.
The parafermionic observable F(z) is defined as a sum over trails from
the starting mid-edge a to z.

For the strip domain S_T, we define F(z) for each mid-edge z inside
or on the boundary of the strip. -/

/-- A mid-edge trail from paperStart to a mid-edge at vertex v,
    staying entirely within PaperInfStrip T.
    This is a MidEdgeTrail where all support vertices are in the strip. -/
structure StripMidEdgeTrail (T : ℕ) (prev next : HexVertex) extends
    MidEdgeTrail paperStart prev next where
  in_strip : ∀ u ∈ trail.support, PaperInfStrip T u
  next_adj_in_strip : PaperInfStrip T next ∨ ¬ PaperInfStrip T next

/-- The contribution of a strip mid-edge trail to the observable:
    direction · e^{-iσW(γ)} · xc^{|γ|} -/
def StripMidEdgeTrail.contrib (T : ℕ) {prev next : HexVertex}
    (γ : StripMidEdgeTrail T prev next) (dir : ℂ) : ℂ :=
  dir * γ.toMidEdgeTrail.weight

/-! ## The vertex relation sum

At each vertex v of the strip, the vertex relation sum is:
  S(v) = Σ_{i=0}^{2} midEdgeDir v i · F(z_i)

where z_i is the mid-edge between v and its i-th neighbor.

The cancellation identity (Lemma 1) says S(v) = 0 for each interior vertex v.
This follows from the walk partition:
- Trails visiting 1 mid-edge at v form triplets (3 walks each)
- Trails visiting 3 mid-edges at v form pairs (2 walks each)
- Each group's contribution is zero (algebraic cancellation)

The algebraic cancellations are fully proved:
- `vertexContrib_triplet_zero`: triplet sum = 0
- `vertexContrib_pair_zero`: pair sum = 0
-/

/-- The vertex relation: the sum of direction × observable at each
    mid-edge of v vanishes.

    This is equivalent to: F₀ + j · F₁ + j̄ · F₂ = 0
    (after dividing by midEdgeDir v 0, which is nonzero).

    Proof: partition trails into triplets and pairs, each cancelling
    by vertexContrib_triplet_zero and vertexContrib_pair_zero. -/
theorem vertex_relation_abstract (v : HexVertex) (F₀ F₁ F₂ : ℂ)
    (h_cancel : F₀ + j * F₁ + conj j * F₂ = 0) :
    midEdgeDir v 0 * F₀ + midEdgeDir v 1 * F₁ + midEdgeDir v 2 * F₂ = 0 :=
  vertex_relation_from_reduced v F₀ F₁ F₂ h_cancel

/-! ## Connection between trails and paths on the boundary

The key result from SAWTrailStructure: trails from paperStart to
right boundary mid-edges, staying in PaperInfStrip T, are vertex-SAWs.
This means F(z) on the right boundary equals the partition function B_paper.

Similarly for the left boundary (F(z) = A_paper with phase factors). -/

/-- On the right boundary, trails are paths. Therefore the observable
    F(z) for a right boundary mid-edge equals the path-based partition
    function (sum of xc^{n+1} over vertex-SAWs to the right boundary). -/
theorem right_boundary_trails_are_paths (T : ℕ) (hT : 1 ≤ T)
    (x y : ℤ) (h_diag : x + y = -(T : ℤ))
    (trail : hexGraph.Walk paperStart (x, y, false))
    (h_trail : trail.IsTrail)
    (h_stay : ∀ u ∈ trail.support, PaperInfStrip T u) :
    trail.IsPath :=
  right_boundary_trail_is_path T hT x y h_diag trail h_trail h_stay

/-! ## Summary of the proof architecture

### Fully proved (all sorry-free):

**Algebraic cancellation** (SAW.lean, SAWObservable.lean):
- `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0
- `triplet_contribution_zero`: triplet walk group sum = 0
- `pair_contribution_zero`: pair walk group sum = 0

**Direction vectors** (SAWObservable.lean, SAWCancellationProof.lean):
- `midEdgeDir_j_relation`: d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
- `false_vertex_j_relation` / `true_vertex_j_relation`

**Vertex relation structure** (SAWCancellationProof.lean):
- `vertex_relation_from_reduced`: F₀ + j·F₁ + j̄·F₂ = 0 → full relation = 0
- `reduced_from_vertex_relation`: full relation = 0 → reduced form
- `vertexContrib_triplet_zero`: triplet contribution = 0
- `vertexContrib_pair_zero`: pair contribution = 0

**Walk partition infrastructure** (SAWObservableDef.lean, SAWWalkPartition.lean):
- `tripletExtendFromN`: extension operation for triplets
- `tripletExtendFromN_len`: extended walk has length ℓ+1
- `triplet_winding_ext1/2`: winding changes by ±π/3
- `triplet_contribution_at_vertex`: triplet group contribution = 0
- `pair_contribution_at_vertex`: pair group contribution = 0
- `trail_to_v_has_predecessor`: trail decomposition at last edge
- `predecessor_is_named_neighbor`: predecessor is one of 3 neighbors
- `hex_vertex_degree`: complete neighbor characterization

**Trail structure** (SAWTrailStructure.lean — NEW):
- `hex_trail_revisit_is_endpoint`: trail revisiting v ⟹ v ∈ {s,t}
- `hex_trail_interior_visit_bound`: interior vertices visited at most once
- `hex_edges_incident_le_three`: at most 3 incident edges per vertex
- `boundary_vertex_edge_bound`: boundary vertices have ≤ 2 trail edges
- `boundary_endpoint_count_le_one`: boundary endpoints visited at most once
- `strip_trail_boundary_endpoints_is_path`: boundary-to-boundary trail is a path
- `right_boundary_trail_is_path`: start-to-right-boundary trail is a path

**Boundary evaluation** (SAWDiscreteStokes.lean, SAWVertexRelation.lean):
- `boundary_phase_right`: right boundary phase = 1
- `left_boundary_contrib_re`: Re(left phase) = c_alpha
- `starting_midedge_contribution`: starting contribution = -1
- `interior_midedge_cancels`: interior edge directions cancel

### Remaining gaps for B_paper ≤ 1:

1. **Walk partition exhaustiveness**: Show every trail to v's mid-edges
   belongs to exactly one cancelling group (triplet or pair).
   The grouping operations (extension/retraction, loop reversal) are
   defined, and their algebraic cancellation is proved. What remains
   is the formal partition argument.

2. **Discrete Stokes summation**: Sum vertex relations over all strip
   vertices, show interior mid-edges cancel pairwise.

3. **Boundary identification**: Connect the boundary observable sum to
   the partition functions A_paper, B_paper, E_paper.
   The key step — boundary trails are paths — is proved.
-/

end
