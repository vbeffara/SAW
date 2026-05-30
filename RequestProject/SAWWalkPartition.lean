/-
# Walk Partition at a Vertex

Formalizes the walk partition from the proof of Lemma 1 (cancellation identity).
-/

import Mathlib
import RequestProject.SAWCancellationProof

open Real Complex ComplexConjugate Filter Topology Classical

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Walk classification -/

def trail_visits_vertex {s prev : HexVertex}
    (trail : hexGraph.Walk s prev) (v : HexVertex) : Prop :=
  v ∈ trail.support

instance {s prev : HexVertex} (trail : hexGraph.Walk s prev) (v : HexVertex) :
    Decidable (trail_visits_vertex trail v) :=
  inferInstanceAs (Decidable (v ∈ trail.support))

/-! ## Hex lattice: exactly 3 neighbors -/

lemma hexGraph_symm' (v w : HexVertex) : hexGraph.Adj v w → hexGraph.Adj w v :=
  fun h => hexGraph.symm h

theorem hex_vertex_degree (v : HexVertex) :
    ∀ w : HexVertex, hexGraph.Adj v w ↔
      (w = hexNeighbors3 v 0 ∨ w = hexNeighbors3 v 1 ∨ w = hexNeighbors3 v 2) := by
  intro w
  exact ⟨hexNeighbors3_complete v w, fun h => by
    rcases h with rfl | rfl | rfl
    exacts [hexNeighbors3_adj v 0, hexNeighbors3_adj v 1, hexNeighbors3_adj v 2]⟩

/-! ## Trail predecessor decomposition -/

/-- A nonempty trail ending at v can be decomposed by removing the last edge. -/
lemma trail_to_v_has_predecessor {s v : HexVertex}
    (trail : hexGraph.Walk s v) (h_trail : trail.IsTrail)
    (h_nonempty : 0 < trail.length) :
    ∃ (w : HexVertex) (prefix_trail : hexGraph.Walk s w),
      prefix_trail.IsTrail ∧
      hexGraph.Adj w v ∧
      trail.length = prefix_trail.length + 1 ∧
      s(w, v) ∉ prefix_trail.edges := by
  obtain ⟨r, hr⟩ : ∃ r : hexGraph.Walk v s, r = trail.reverse ∧ r.IsTrail := by aesop
  obtain ⟨w, adj_vw, tail, hr_cons⟩ :
      ∃ w, ∃ adj_vw : hexGraph.Adj v w, ∃ tail : hexGraph.Walk w s,
        r = SimpleGraph.Walk.cons adj_vw tail := by
    cases r
    · replace hr := congr_arg SimpleGraph.Walk.length hr.1; aesop
    · tauto
  refine ⟨w, tail.reverse, ?_, hexGraph_symm' _ _ adj_vw, ?_, ?_⟩
  <;> simp_all +decide [SimpleGraph.Walk.isTrail_cons]
  · replace hr := congr_arg SimpleGraph.Walk.length hr.1
    simp_all +decide [SimpleGraph.Walk.length_reverse]
  · grind

/-
The predecessor is one of v's named neighbors.
-/
lemma predecessor_is_named_neighbor {s v : HexVertex}
    (trail : hexGraph.Walk s v) (h_trail : trail.IsTrail)
    (h_nonempty : 0 < trail.length) :
    ∃ (k : Fin 3) (prefix_trail : hexGraph.Walk s (hexNeighbors3 v k)),
      prefix_trail.IsTrail ∧ trail.length = prefix_trail.length + 1 ∧
      s(hexNeighbors3 v k, v) ∉ prefix_trail.edges := by
  obtain ⟨w, prefix_trail, hw_trail, hw_adj, hw_len, hw_fresh⟩ := trail_to_v_has_predecessor trail h_trail h_nonempty;
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, w = hexNeighbors3 v k := by
    have := hexNeighbors3_complete v w ( hexGraph_symm' _ _ hw_adj ) ; aesop;
  grind +ring

/-- Penultimate vertex exists. -/
lemma walk_penultimate_adj {s v : HexVertex}
    (trail : hexGraph.Walk s v) (h_trail : trail.IsTrail)
    (h : 0 < trail.length) :
    ∃ w : HexVertex, hexGraph.Adj w v ∧ w ∈ trail.support := by
  induction' trail with w hw ih
  · contradiction
  · grind +suggestions

/-! ## Triplet extension/retraction -/

lemma tripletExtend_last_edge {s n₀ v nⱼ : HexVertex}
    (γ : MidEdgeTrail s n₀ v) (h₁ : hexGraph.Adj n₀ v) (h₂ : hexGraph.Adj v nⱼ)
    (hf : s(n₀, v) ∉ γ.trail.edges) :
    (tripletExtendFromN γ h₁ h₂ hf).trail.length = γ.trail.length + 1 := by
  simp [tripletExtendFromN, SimpleGraph.Walk.length_append]

end