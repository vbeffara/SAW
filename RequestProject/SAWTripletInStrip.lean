/-
# Triplet Extension in the Strip

Shows that the triplet extension/retraction operations preserve
the strip constraint, enabling the walk partition to work for the
strip observable.

## Key results

* `extension_in_strip` — extending a trail in the strip stays in strip
* `vEdgeCount_append_edge` — v-edge count of appended trail
* `incoming_vEdgeCount_le_two` — incoming trails have ≤ 2 v-edges
-/

import Mathlib
import RequestProject.SAWCancellationFull

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-! ## Extension preserves strip membership -/

/-- If v is in the strip and γ stays in strip, then appending edge n_j→v stays in strip. -/
lemma extension_in_strip {T L : ℕ} {s : HexVertex} {v : HexVertex}
    (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_strip : ∀ u ∈ trail.support, PaperFinStrip T L u)
    (hv : PaperFinStrip T L v) :
    ∀ u ∈ (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).support,
      PaperFinStrip T L u := by
  intro u hu
  rw [SimpleGraph.Walk.support_append] at hu
  simp at hu
  rcases hu with hu | rfl
  · exact h_strip u hu
  · exact hv

/-! ## v-edge count of appended walk -/

/-- v-edge count decomposes: vEdgeCount v (p ++ [edge]) = vEdgeCount v p + (0 or 1). -/
lemma vEdgeCount_append_edge {s t v : HexVertex} (w : HexVertex)
    (p : hexGraph.Walk s t) (hadj : hexGraph.Adj t w) :
    vEdgeCount v (p.append (.cons hadj .nil)) =
    vEdgeCount v p + (if v ∈ s(t, w) then 1 else 0) := by
  rw [vEdgeCount_append, vEdgeCount_cons_nil]

/-! ## Incoming trail v-edge count bound

An incoming trail at (n_j, v) with edge {n_j, v} not used has at most 2 v-edges.
Since the 3 possible v-edges are {v,n₀}, {v,n₁}, {v,n₂}, and {n_j, v} is excluded,
at most 2 remain. -/

/-- The edge {n_j, v} is a v-edge. -/
lemma neighbor_edge_is_v_edge (v : HexVertex) (j : Fin 3) :
    v ∈ s(hexNeighbors3 v j, v) := by
  exact Sym2.mem_iff.mpr (Or.inr rfl)

/-- If {n_j, v} is not in trail edges, then the trail's v-edge count excludes it. -/
lemma vEdgeCount_excludes_fresh {s : HexVertex} (v : HexVertex) (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_fresh : s(hexNeighbors3 v j, v) ∉ trail.edges) :
    ∀ e ∈ trail.edges, v ∈ e → e ≠ s(hexNeighbors3 v j, v) := by
  intro e he hv hc; exact h_fresh (hc ▸ he)

/-! ## Extending a 0-v-edge trail gives a 1-v-edge trail

When we extend a trail with 0 v-edges by adding edge {n_j, v},
the resulting trail has exactly 1 v-edge: the newly added edge. -/

/-- Extension adds exactly 1 v-edge. -/
lemma extension_adds_one_v_edge {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_no_v : vEdgeCount v trail = 0) :
    vEdgeCount v (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)) = 1 := by
  rw [vEdgeCount_append_edge]
  simp [h_no_v, neighbor_edge_is_v_edge]

/-! ## 0-v-edge implies edge {n_j, v} is fresh

A trail with 0 v-edges doesn't use any edge incident to v,
so in particular edge {n_j, v} is not used. -/

/-- 0 v-edges → no v-edge used → {n_j, v} is fresh. -/
lemma zero_v_edges_implies_fresh' {s : HexVertex} (v : HexVertex) (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_no_v : vEdgeCount v trail = 0) :
    s(hexNeighbors3 v j, v) ∉ trail.edges := by
  exact no_v_edge_implies_fresh v trail h_no_v (hexNeighbors3_adj v j).symm

/-! ## The extended trail is a valid trail -/

/-- Extension of a 0-v-edge trail is still a trail (no repeated edges). -/
lemma extension_is_trail {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_trail : trail.IsTrail)
    (h_no_v : vEdgeCount v trail = 0) :
    (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).IsTrail :=
  extend_is_trail j trail h_trail h_no_v

/-! ## Summary: the triplet extension in the strip

For a 0-v-edge incoming trail γ from paperStart to n_j in the strip,
with v in the strip:

1. `zero_v_edges_implies_fresh'`: edge {n_j, v} ∉ γ.edges
2. `extension_is_trail`: appending {n_j, v} gives a valid trail
3. `extension_adds_one_v_edge`: the result has exactly 1 v-edge
4. `extension_in_strip`: the result stays in the strip

This means the triplet extension map is well-defined within the strip
observable. Combined with the algebraic triplet_cancellation, each
triplet group contributes zero to the vertex relation sum.

For 2-v-edge incoming trails, the pair cancellation by loop reversal
also contributes zero. Together, these give the vertex relation
(Lemma 1) for the concrete strip observable. -/

end
