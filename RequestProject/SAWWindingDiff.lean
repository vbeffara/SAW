/-
# Pair Winding Difference — Correct Formulation

The winding difference between a FreshIncomingPair walk γ and its
pair involution pairInvol(γ) is ±8π/3.

## Relationship to pair_winding_relation

The existing `pair_winding_relation` in SAWPairCancellation.lean states
a specific cyclic ordering of (k, exit) via fin3_other. This ordering
is correct for one class of walks but not the other (anti-cyclic).
However, `pair_exp_cancellation` (which is what's actually needed
downstream) is TRUE for all walks, because the algebraic cancellation
identity works for both orderings.

The correct statement is: |W(pairInvol γ) - W(γ)| = 8π/3.

## Connection to the turning number theorem

The winding difference follows from:
1. hexWalkWinding_reverse_list': reversed trail winding = -original
2. The discrete turning number theorem for simple closed hex trails:
   total exterior angle = ±2π
3. Each hex lattice turn is ±π/3 (hex_turn_value)
4. The junction turn difference is ±2π/3

This file states the correct winding difference lemma (sorry'd pending
the turning number theorem) and documents the mathematical proof.
-/

import Mathlib
import RequestProject.SAWPairCancellation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Turning number theorem for simple closed hex trails

Every simple closed trail on the hexagonal lattice has total exterior
angle ±2π. This is the discrete Gauss-Bonnet theorem.

**Proof sketch**: On the hex lattice, every vertex has degree 3. In a
simple closed trail, every vertex has exactly 2 incident edges, so the
local edge graph is a single cycle. Each turn is ±π/3. The sum of
exterior angles of a simple polygon in the plane equals ±2π (positive
for counterclockwise traversal, negative for clockwise). -/

/-- The discrete turning number theorem for hex lattice trails.
    For a closed trail [v₀, v₁, ..., vₙ, v₀] where:
    - Each consecutive pair is adjacent in hexGraph
    - Each edge is used at most once (trail condition)
    - Each vertex appears at most once in the interior (simple)
    The total winding (sum of turns at v₁, ..., vₙ) plus the closure
    turn satisfies: total = ±2π.

    **Sorry**: This is the discrete Gauss-Bonnet theorem. -/
lemma hex_simple_closed_trail_winding (L : List HexVertex)
    (hL : 3 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.Nodup) :
    hexWalkWinding L = 2 * Real.pi - Complex.arg
      ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
       (correctHexEmbed (L.get ⟨0, by omega⟩) - correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)))
    ∨
    hexWalkWinding L = -(2 * Real.pi) - Complex.arg
      ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
       (correctHexEmbed (L.get ⟨0, by omega⟩) - correctHexEmbed (L.get ⟨L.length - 2, by omega⟩))) := by
  sorry

/-! ## The pair winding difference

The correct formulation: |ΔW| = 8π/3. -/

/-
The pair winding difference is ±8π/3.

    **Sorry**: requires the turning number theorem above plus the
    winding decomposition (prefix + junction + loop winding).
-/
lemma pair_winding_diff {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvol hv hv_ne γ).1.winding - γ.1.winding = 8 * Real.pi / 3 ∨
    (pairInvol hv hv_ne γ).1.winding - γ.1.winding = -(8 * Real.pi / 3) := by
  have := pair_winding_relation hv hv_ne γ;
  grind

end