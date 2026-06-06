/-
# Strip Observable — Formal Observable for the Cancellation Identity

Defines the parafermionic observable F(z) at each mid-edge z of the
strip domain, using vertex-SAWs (paths) as in the paper.

F(z) = Σ_{γ: a → z, γ ⊂ Ω} e^{-iσW_γ(a,z)} · x^{ℓ(γ)}

For vertex-SAWs, F(a) = 1 (only the trivial walk from a to itself).

## Key results

* `stripPathObs` — the path-based observable F(z)
* `starting_path_unique` — only the trivial walk from a to a
* `starting_path_weight` — weight of the trivial walk
-/

import Mathlib
import RequestProject.SAWTripletInStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-! ## Path-based mid-edge walk in the strip -/

/-- A vertex-SAW from paperStart to mid-edge (prev, next) in PaperFinStrip T L. -/
structure StripPathToMidEdge (T L : ℕ) (prev next : HexVertex) where
  path : hexGraph.Walk paperStart prev
  is_path : path.IsPath
  adj : hexGraph.Adj prev next
  fresh : next ∉ path.support
  in_strip : ∀ u ∈ path.support, PaperFinStrip T L u

/-- Length of a strip path (edges + 1 half-edge). -/
def StripPathToMidEdge.len {T L : ℕ} {prev next : HexVertex}
    (γ : StripPathToMidEdge T L prev next) : ℕ :=
  γ.path.length + 1

/-- Full vertex list. -/
def StripPathToMidEdge.fullSupport {T L : ℕ} {prev next : HexVertex}
    (γ : StripPathToMidEdge T L prev next) : List HexVertex :=
  γ.path.support ++ [next]

/-- Winding. -/
def StripPathToMidEdge.winding {T L : ℕ} {prev next : HexVertex}
    (γ : StripPathToMidEdge T L prev next) : ℝ :=
  hexWalkWinding γ.fullSupport

/-- Complex weight: e^{-iσW} · xc^ℓ. -/
def StripPathToMidEdge.weight {T L : ℕ} {prev next : HexVertex}
    (γ : StripPathToMidEdge T L prev next) : ℂ :=
  walkWeight γ.winding γ.len xc sigma

/-! ## The observable at a mid-edge -/

/-- The parafermionic observable at mid-edge (prev, next) in strip S_{T,L}.
    Sums over all vertex-SAWs from paperStart to the mid-edge. -/
def stripPathObs (T L : ℕ) (prev next : HexVertex) : ℂ :=
  ∑' (γ : StripPathToMidEdge T L prev next), γ.weight

/-! ## F(a) = walkWeight 0 1 xc sigma

The starting mid-edge a is between paperStart = TRUE(0,0) and
hexOrigin = FALSE(0,0). For vertex-SAWs, the only walk from a to a
is the trivial walk (length 0). -/

/-- The nil path as a StripPathToMidEdge. -/
def startingPathWalk (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    StripPathToMidEdge T L paperStart hexOrigin where
  path := .nil
  is_path := SimpleGraph.Walk.IsPath.nil
  adj := by unfold paperStart hexOrigin hexGraph; simp
  fresh := by simp [SimpleGraph.Walk.support, hexOrigin, paperStart]
  in_strip := by
    intro u hu; simp [SimpleGraph.Walk.support] at hu; subst hu
    exact paperStart_in_fin_strip T L hT hL

/-- Any StripPathToMidEdge from paperStart to (paperStart, hexOrigin)
    must have a nil path. -/
lemma starting_path_unique (T L : ℕ)
    (γ : StripPathToMidEdge T L paperStart hexOrigin) :
    γ.path = .nil := by
  cases h : γ.path with
  | nil => rfl
  | cons hadj rest =>
    exfalso
    have h_path := γ.is_path
    rw [h] at h_path
    have := h_path.support_nodup
    rw [SimpleGraph.Walk.support] at this
    exact (List.nodup_cons.mp this).1 (SimpleGraph.Walk.end_mem_support rest)

/-- The weight of the starting path walk. -/
lemma starting_path_weight (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (startingPathWalk T L hT hL).weight = walkWeight 0 1 xc sigma := by
  unfold StripPathToMidEdge.weight StripPathToMidEdge.winding
  unfold StripPathToMidEdge.fullSupport StripPathToMidEdge.len
  simp [startingPathWalk, hexWalkWinding]

/-- walkWeight 0 1 xc sigma = xc. -/
lemma walkWeight_zero_one' : walkWeight 0 1 xc sigma = (xc : ℂ) := by
  unfold walkWeight; simp [pow_one]

/-! ## The vertex relation

The vertex relation (Lemma 1) states that at each vertex v in the strip:

  Σᵢ d_i(v) · F(z_i) = 0

where F(z_i) sums over walks to mid-edge z_i from both sides.

For vertex-SAWs, the walk partition uses only triplets (no pairs).
The vertex relation holds at vertices where the triplet partition
is complete (every root generates two valid extensions). -/

/-- The vertex relation term at mid-edge i of vertex v. -/
def stripVertexTerm (T L : ℕ) (v : HexVertex) (i : Fin 3) : ℂ :=
  midEdgeDir v i * (stripPathObs T L v (hexNeighbors3 v i) +
                     stripPathObs T L (hexNeighbors3 v i) v)

/-- The vertex relation sum at v. -/
def stripVertexSum (T L : ℕ) (v : HexVertex) : ℂ :=
  stripVertexTerm T L v 0 + stripVertexTerm T L v 1 + stripVertexTerm T L v 2

/-- The vertex relation reduces to the j-relation form. -/
lemma stripVertexSum_eq_reduced (T L : ℕ) (v : HexVertex) :
    stripVertexSum T L v =
    midEdgeDir v 0 * ((stripPathObs T L v (hexNeighbors3 v 0) +
                        stripPathObs T L (hexNeighbors3 v 0) v) +
      j * (stripPathObs T L v (hexNeighbors3 v 1) +
           stripPathObs T L (hexNeighbors3 v 1) v) +
      conj j * (stripPathObs T L v (hexNeighbors3 v 2) +
               stripPathObs T L (hexNeighbors3 v 2) v)) := by
  unfold stripVertexSum stripVertexTerm
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2]; ring

/-- The vertex relation holds iff the reduced form is zero. -/
lemma vertex_relation_iff_reduced (T L : ℕ) (v : HexVertex) :
    stripVertexSum T L v = 0 ↔
    (stripPathObs T L v (hexNeighbors3 v 0) +
      stripPathObs T L (hexNeighbors3 v 0) v) +
    j * (stripPathObs T L v (hexNeighbors3 v 1) +
         stripPathObs T L (hexNeighbors3 v 1) v) +
    conj j * (stripPathObs T L v (hexNeighbors3 v 2) +
             stripPathObs T L (hexNeighbors3 v 2) v) = 0 := by
  rw [stripVertexSum_eq_reduced]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (midEdgeDir_zero_ne_zero v)
  · intro h; rw [h, mul_zero]

/-- **Lemma 1** (Vertex Relation). For every vertex v in the strip,
    the vertex relation sum is zero.

    **WARNING**: This uses `stripPathObs` (based on `StripPathToMidEdge`),
    which requires the half-edge endpoint to be a VERTEX not in the path.
    For vertex-SAWs with this freshness condition, the triplet partition
    is INCOMPLETE when one of the extension neighbors has already been
    visited by the path. The vertex relation may NOT hold for this observable.

    The correct statement uses `freshVertexSum` (based on `FreshTrail`
    with EDGE freshness, not vertex freshness), proved as
    `fresh_vertex_relation` in `SAWPairInvolutionProof.lean`.

    This sorry is a **dead branch** — not on the critical path. -/
lemma vertex_relation_strip (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v) :
    stripVertexSum T L v = 0 := by
  rw [vertex_relation_iff_reduced]
  sorry

end
