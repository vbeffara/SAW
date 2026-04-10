/-
# Discrete Stokes skeleton for B_paper ≤ 1

This file reduces B_paper_le_one_direct to the vertex relation
for the parafermionic observable.

## Proof outline (Lemma 2 of the paper)

1. Define F(z) at each mid-edge z of the finite strip S_{T,L}.
2. The vertex relation says: for each v ∈ V(S_{T,L}),
   Σ_{w : neighbor(v)} (correctHexEmbed w - correctHexEmbed v) · F(mid(v,w)) = 0.
3. Sum over all vertices: interior mid-edges cancel, boundary mid-edges survive.
4. Evaluate boundary contributions → 0 = -(1 - c_α A) + B + c_ε E.
5. Rearrange: 1 = c_α A + B + c_ε E.
6. Since A, E ≥ 0 and c_α, c_ε > 0: B ≤ 1.
-/

import Mathlib
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Mid-edge observable

For a mid-edge z = mid(v, w) in the strip, F(z) counts SAWs from paperStart
ending at z, weighted by e^{-iσW} · xc^ℓ.

A walk "ending at mid-edge z = mid(v,w)" visits vertices in V(Ω) and exits
toward z. The last vertex can be v or w (whichever is inside the domain). -/

/-- A "strip SAW ending at vertex v" is a SAW from paperStart to v
    staying in PaperFinStrip T L. -/
structure StripSAW (T L : ℕ) (v : HexVertex) where
  len : ℕ
  saw : SAW paperStart len
  endpoint : saw.w = v
  in_strip : ∀ u ∈ saw.p.1.support, PaperFinStrip T L u

/-- The winding of a StripSAW, measured as total turning angle. -/
def stripSAW_winding (T L : ℕ) (v : HexVertex) (s : StripSAW T L v) : ℤ :=
  walkWindingInt s.saw.p.1

/-- The observable at a directed edge (v, w): sum over SAWs ending at v,
    weighted by exp(-iσ · winding · π/3) · xc^{len+1}. -/
def F_directed (T L : ℕ) (v w : HexVertex) : ℂ :=
  ∑' (s : StripSAW T L v),
    Complex.exp (-Complex.I * sigma * (↑(stripSAW_winding T L v s) * Real.pi / 3)) *
    (xc : ℂ) ^ (s.len + 1)

/-- The observable at a mid-edge (v,w), summing over approaches from both sides. -/
def F_midedge (T L : ℕ) (v w : HexVertex) : ℂ :=
  F_directed T L v w + F_directed T L w v

/-! ## Vertex relation (the core sorry)

The vertex relation states that for each vertex v inside the strip,
the weighted sum of the observable over v's three mid-edges is zero.

This is proved in the paper by partitioning walks into pairs (visiting
all 3 mid-edges, loop reversal) and triplets (visiting 1 or 2 mid-edges,
extension by one step). The algebraic core is pair_cancellation and
triplet_cancellation, which are already proved. The combinatorial
construction of the partition is the key remaining gap. -/

/-- The vertex relation for the parafermionic observable.
    For each interior vertex v of the strip S_{T,L}:
    Σ_{w neighbor of v} (correctHexEmbed w - correctHexEmbed v) · F(mid(v,w)) = 0.

    **Status: sorry.** This is the combinatorial core of Lemma 1.
    The algebraic ingredients (pair_cancellation, triplet_cancellation) are proved.
    What remains is constructing the pair/triplet partition of walks at each vertex
    and verifying the weight cancellation. -/
theorem vertex_relation_observable (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v)
    (hv_int : ∀ w, hexGraph.Adj v w → PaperFinStrip T L w) :
    ∑ w ∈ (hexGraph.neighborFinset v), -- this doesn't exist for infinite graphs
      (correctHexEmbed w - correctHexEmbed v) * F_midedge T L v w = 0 := by
  sorry

-- Note: hexGraph.neighborFinset might not exist since hexGraph is infinite.
-- We'd need to manually enumerate the 3 neighbors.

/-! ## Alternative: direct vertex relation sum

Instead of using Finset.sum over neighbors (which requires a finset of neighbors),
we can directly sum over the 3 neighbors of each vertex type. -/

/-
Vertex relation for a FALSE vertex (x, y, false).
    Neighbors: TRUE(x, y), TRUE(x+1, y), TRUE(x, y+1).
-/
theorem vertex_relation_false (T L : ℕ) (x y : ℤ)
    (hv : PaperFinStrip T L (x, y, false))
    (hw1 : PaperFinStrip T L (x, y, true))
    (hw2 : PaperFinStrip T L (x + 1, y, true))
    (hw3 : PaperFinStrip T L (x, y + 1, true)) :
    (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) *
      F_midedge T L (x, y, false) (x, y, true) +
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false)) *
      F_midedge T L (x, y, false) (x + 1, y, true) +
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false)) *
      F_midedge T L (x, y, false) (x, y + 1, true) = 0 := by
  have := @vertex_relation_observable;
  convert this T L ( x, y, false ) hv _ using 1;
  · rw [ show hexGraph.neighborFinset ( x, y, false ) = { ( x, y, true ), ( x + 1, y, true ), ( x, y + 1, true ) } from ?_ ];
    · grind;
    · simp +decide [ Finset.ext_iff, hexGraph ];
      grind;
  · intro w hw; rcases hw with ⟨ hw1, hw2 ⟩ ;
    · grind;
    · tauto

/-
Vertex relation for a TRUE vertex (x, y, true).
    Neighbors: FALSE(x, y), FALSE(x-1, y), FALSE(x, y-1).
-/
theorem vertex_relation_true (T L : ℕ) (x y : ℤ)
    (hv : PaperFinStrip T L (x, y, true))
    (hw1 : PaperFinStrip T L (x, y, false))
    (hw2 : PaperFinStrip T L (x - 1, y, false))
    (hw3 : PaperFinStrip T L (x, y - 1, false)) :
    (correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true)) *
      F_midedge T L (x, y, true) (x, y, false) +
    (correctHexEmbed (x - 1, y, false) - correctHexEmbed (x, y, true)) *
      F_midedge T L (x, y, true) (x - 1, y, false) +
    (correctHexEmbed (x, y - 1, false) - correctHexEmbed (x, y, true)) *
      F_midedge T L (x, y, true) (x, y - 1, false) = 0 := by
  convert vertex_relation_observable T L ( x, y, true ) hv _ using 1;
  · rw [ show hexGraph.neighborFinset ( x, y, true ) = { ( x, y, false ), ( x - 1, y, false ), ( x, y - 1, false ) } from ?_ ];
    · grind;
    · ext ⟨ x', y', b' ⟩ ; simp +decide [ hexGraph, PaperFinStrip ] ;
      grind;
  · intro w hw; cases hw; aesop;
    grind

/-! ## Boundary sum identity (from discrete Stokes)

Summing the vertex relation over all interior vertices,
interior mid-edges cancel and boundary mid-edges survive. -/

/-- The boundary sum of the observable equals zero.
    This follows from summing vertex relations over all strip vertices
    and using interior cancellation.

    **Status: sorry.** Follows from vertex_relation_true/false +
    interior cancellation (proved algebraically in interior_cancellation). -/
theorem boundary_sum_zero (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    -- The sum of (w-v) · F(mid(v,w)) over all boundary mid-edges = 0
    -- Boundary mid-edge: v ∈ V(S_{T,L}), w adjacent to v, w ∉ V(S_{T,L})
    True := by  -- placeholder statement
  trivial

/-! ## Key consequence: B_paper ≤ 1

From the boundary sum identity, we can deduce:
0 = -(1 - c_α · A_paper) + B_paper + c_ε · E_paper
Hence: 1 = c_α · A_paper + B_paper + c_ε · E_paper
Since A, E ≥ 0 and c_α, c_ε > 0: B_paper ≤ 1.

The key steps are:
1. Starting mid-edge contributes: dir = -1, F = 1 → contribution = -1
2. Other left boundary: dir = -1, F involves cos(5π/8) = -c_α → contribution = c_α · A
3. Right boundary: dir = +1, F involves winding 0 → contribution = B
4. Escape boundary: dir involves j, j̄ → contribution = c_ε · E

These boundary evaluations require:
- The winding from a to left boundary is ±π
- The winding from a to right boundary is 0
- The winding from a to escape boundary is ±2π/3
- The direction factors for each boundary type

The direction factors are verified in SAWDiscreteStokes.lean
(right_boundary_dir, starting_dir, etc.) and
SAWObservableProof2.lean (boundary_weight_re_nonneg). -/

end