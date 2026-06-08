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

## Proof decomposition

The proof decomposes into two parts:
1. `closed_trail_winding_multiple_of_2pi` — For ANY closed hex trail (not
   necessarily simple), the total winding (hexWalkWinding + closure) is a
   multiple of 2π. This is proved algebraically: the product of all direction
   ratios telescopes to 1, giving exp(i·total) = 1.

2. For a SIMPLE closed hex trail, the total winding is exactly ±2π
   (turning number = ±1). This is the topological part that requires
   simplicity, and is the discrete Gauss-Bonnet / Umlaufsatz theorem.
-/

import Mathlib
import RequestProject.SAWPairWinding

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Part 1: Hex edge direction properties

Each hex edge direction has unit magnitude.
The product of direction ratios along a trail telescopes. -/

/-
Each hex edge direction has unit magnitude (norm 1).
-/
lemma hex_edge_norm_one (v w : HexVertex) (h : hexGraph.Adj v w) :
    Complex.normSq (correctHexEmbed w - correctHexEmbed v) = 1 := by
  rcases v with ⟨ x, y, b ⟩ ; rcases w with ⟨ x', y', b' ⟩ ;
  cases b <;> cases b' <;> simp_all +decide [ hexGraph ];
  · unfold correctHexEmbed; norm_num [ Complex.normSq ] ; ring;
    rcases h with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num <;> ring;
  · rcases h with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num [ correctHexEmbed ];
    · norm_num [ Complex.normSq ];
    · norm_num [ Complex.normSq ] ; ring ; norm_num;
    · norm_num [ Complex.normSq ] ; ring ; norm_num

/-! ## The turning number theorem for simple closed hex trails -/

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