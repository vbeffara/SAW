/-
# Hex Lattice Path Helpers

Helper lemmas for proving that trails on the hex lattice are paths (SAWs).
These are needed for the IsTrail → IsPath correctness fix in FreshTrail.

On the hex lattice (degree 3), a trail is almost always a path:
- Interior vertices use 2 edges each, so at most 1 visit (2 ≤ 3)
- Start/end vertices use 1 edge, but could be revisited (1 + 2 = 3 ≤ 3)
- The only vertices that can be visited twice are start and end

For FreshTrail: the endpoint has the fresh edge constraint, which limits
it to 2 used edges, preventing revisits.

## Key results

* `vEdgeCount_ge_two_of_interior` — interior visits use ≥ 2 edges
* `hex_trail_interior_visits_once` — interior vertices visited at most once
* `hex_vEdgeCount_le_three` — degree 3 bound
* `support_count_le_vEdgeCount` — count ≤ vEdgeCount (for non-endpoint)
* `hex_trail_is_path_of_endpoint_bounds` — trail → path when endpoints
  have limited edge counts
-/

import Mathlib
import RequestProject.SAWWalkPartitionComplete

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-! ## vEdgeCount and walk support -/

/-- A vertex that appears in the interior of a walk's support has at least
    2 incident edges in the walk. -/
lemma vEdgeCount_ge_two_of_interior {s t v : HexVertex}
    (w : hexGraph.Walk s t) (h_trail : w.IsTrail)
    (hmem : v ∈ w.support) (hne_s : v ≠ s) (hne_t : v ≠ t) :
    2 ≤ vEdgeCount v w := by
  obtain ⟨ e₁, e₂, he₁, he₂, he₁₂ ⟩ := trail_interior_vertex_uses_two_edges w h_trail v hmem hne_s hne_t;
  refine' le_trans _ ( List.toFinset_card_le _ );
  refine' Finset.one_lt_card.mpr ⟨ e₁, _, e₂, _, _ ⟩ <;> aesop

/-- On the hex lattice (degree 3), a vertex can appear at most once as
    an interior vertex of a trail. -/
lemma hex_trail_interior_visits_once {s t v : HexVertex}
    (w : hexGraph.Walk s t) (h_trail : w.IsTrail)
    (hne_s : v ≠ s) (hne_t : v ≠ t) :
    w.support.count v ≤ 1 := by
  convert hex_trail_interior_visit_bound w h_trail v hne_s hne_t using 1

/-- On the hex lattice, a trail uses at most 3 edges at any vertex. -/
lemma hex_vEdgeCount_le_three (v : HexVertex) {s t : HexVertex}
    (w : hexGraph.Walk s t) (h_trail : w.IsTrail) :
    vEdgeCount v w ≤ 3 := by
  convert hex_edges_incident_le_three w h_trail v using 1

/-! ## Count-to-vEdgeCount bound

The number of times a vertex v appears in a walk's support is bounded
by the number of edges incident to v in the walk (vEdgeCount).
For v ≠ t (not the endpoint), each appearance uses at least one outgoing edge. -/

/-
For the start vertex, count ≤ vEdgeCount.
    Each appearance of s in the support (including the initial one) corresponds
    to at least one outgoing edge from s.
-/
lemma support_count_start_le_vEdgeCount {s t : HexVertex}
    (w : hexGraph.Walk s t) (h_trail : w.IsTrail) (h_ne : s ≠ t) :
    w.support.count s ≤ vEdgeCount s w := by
  have h_ind_step : ∀ {v : HexVertex} {w : hexGraph.Walk v t}, w.IsTrail → s ∈ w.support → w.support.count s ≤ (w.edges.filter (fun e => s ∈ e)).length := by
    intros v w h_trail hmem; induction' w with v w h_trail hmem ih <;> simp_all +decide [ List.count_cons ] ;
    grind;
  exact h_ind_step h_trail ( by simp )

/-! ## Trail to path conversion -/

/-
A trail on the hex lattice where both endpoints have limited edge counts
    is automatically a path (SAW).
-/
lemma hex_trail_is_path_of_endpoint_bounds {s t : HexVertex}
    (w : hexGraph.Walk s t) (h_trail : w.IsTrail)
    (h_start : vEdgeCount s w ≤ 1)
    (h_end : vEdgeCount t w ≤ 1)
    (h_ne : s ≠ t) :
    w.IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  rw [List.nodup_iff_count_le_one]
  intro v
  by_cases hv : v ∈ w.support
  · by_cases hvs : v = s
    · subst hvs; exact (support_count_start_le_vEdgeCount w h_trail h_ne).trans h_start
    · by_cases hvt : v = t
      · subst hvt
        -- For t: if count t ≥ 2, then t appears as interior, using ≥ 2 edges
        -- plus endpoint (≥ 1 edge), total ≥ 3. But vEdgeCount ≤ 1. Contradiction.
        have h_support_count : List.count v w.support ≤ vEdgeCount v w := by
          convert support_count_start_le_vEdgeCount w.reverse h_trail.reverse _ using 1;
          · simp +decide [ List.count ];
          · unfold vEdgeCount; simp +decide [ SimpleGraph.Walk.edges_reverse ] ;
          · tauto;
        grobner
      · exact hex_trail_interior_visits_once w h_trail hvs hvt
  · exact Nat.le_of_eq (List.count_eq_zero_of_not_mem hv) |>.trans (by norm_num)

end