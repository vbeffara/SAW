/-
# Turning Number Theorem for Hex Lattice Closed Trails

The key topological fact needed for the pair cancellation identity:
a simple closed trail on the hex lattice has turning number ±1.

## Main result

* `hex_closed_trail_turning_number` — for a simple closed trail on the hex
  lattice, the total winding (sum of exterior angles at all vertices including
  the closure) equals ±2π.

## Status

This lemma is sorry'd. It is the single deepest unproved fact in the
formalization. All other sorry's (pair_winding_relation, B_paper_le_one_strip,
infinite_strip_identity) ultimately depend on this result.

The proof would use the fact that a simple closed polygon in the plane has
total exterior angle ±2π (the discrete Gauss-Bonnet theorem / turning
tangent theorem). On the hex lattice, each exterior angle is ±π/3.
-/

import Mathlib
import RequestProject.SAWPairWinding

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## The turning number theorem for hex lattice closed trails

For a closed trail L = [v₀, v₁, ..., vₙ₋₁, v₀] on the hex lattice
where all vertices v₁, ..., vₙ₋₁ are distinct (simple):
  hexWalkWinding L = ±2π - closure_turn

where closure_turn = arg(d₁/dₙ) is the angle between the first
direction d₁ = embed(v₁)-embed(v₀) and the last direction 
dₙ = embed(v₀)-embed(vₙ₋₁).

Equivalently:
  hexWalkWinding L + closure_turn = ±2π

This is the discrete analogue of the Gauss-Bonnet theorem:
the total curvature of a simple closed curve is ±2π. -/

/-- The turning number theorem for simple closed hex trails.
    For a list [v₀, v₁, ..., vₙ₋₁, v₀] that forms a simple closed trail
    on the hex lattice:
    hexWalkWinding L + closure_turn = ±2π

    **Sorry**: This is the discrete Gauss-Bonnet theorem applied to
    simple closed polygons on the hexagonal lattice. The proof requires
    showing that a simple (non-self-intersecting) closed polygon in
    the plane has turning number ±1, which is a fundamental result
    in computational geometry / discrete differential geometry.

    On the hex lattice, each turn is ±π/3, so the sum of n+1 turns
    (n interior + 1 closure) of ±π/3 must equal ±2π = ±6·(π/3).
    This means the number of right turns minus left turns is ±6. -/
lemma hex_closed_trail_turning_number (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    let d_first := correctHexEmbed (L.get ⟨1, by omega⟩) -
                   correctHexEmbed (L.get ⟨0, by omega⟩)
    let d_last := correctHexEmbed (L.get ⟨0, by omega⟩) -
                  correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)
    let closure := Complex.arg (d_first / d_last)
    hexWalkWinding L + closure = 2 * Real.pi ∨
    hexWalkWinding L + closure = -(2 * Real.pi) := by
  sorry

end
